-- Adapted from sf-in-lean/SFLCompat.lean and
-- sf-in-lean/SFLCompat/Experiment.lean, merged into a single
-- file (namespace SFLCompat.Experiment -> CSwLCompat). CSwL does not have
-- sf-in-lean's `recall` mechanism (`SFLCompat/Recall/*.lean`), so nothing
-- from there was ported -- only the `sf_experiment`/`sf_expect_failure`/
-- `sf_expect_failure?` macros that back the ` ```lean -keep ` and
-- ` ```lean +error ` fences (see `CSwLMeta/Save/Extract.lean`, `walkBlock`,
-- and `CSwLMeta/Save/Lean.lean`, `LeanSaved.Data.extractionMode`).
--
-- Two deliberate differences from the original:
-- 1. No `import Batteries.CodeAction`, which the root `SFLCompat.lean` had:
--    it exists to propagate Lean code actions to the generated project, but
--    `CSwL` does not depend on `batteries` (only on `cslib`/Mathlib) --
--    pulling in `batteries` just for that would needlessly bloat the
--    extracted project.
-- 2. No `namespace Tests` from the end of the original
--    `SFLCompat/Experiment.lean`: those are `#guard_msgs` that check the
--    exact text of Lean diagnostics ("Unknown identifier `x`", literal
--    positions via `(positions := true)`, etc.). `CSwL` is on the same
--    `v4.33.0` as `sf-in-lean` today, but pinning that text here risks
--    breaking both the book's build and every extracted project's build
--    (the file is copied verbatim) on any message drift between Lean
--    versions -- with no payoff for the course, which uses neither `recall`
--    nor tests these macros directly.
--
-- This file is the "seed" copied verbatim to `_out/<variant>/lean/` by
-- `CSwLMeta/Save/Project.lean` (function `bundleCompatSeed`) whenever some
-- extracted chapter has `import CSwLCompat` in its header.

module

public meta import Lean.Elab.BuiltinCommand

namespace CSwLCompat

open Lean Elab Command

meta section

-- Copied from `SubVerso.Compat` so generated projects don't depend on
-- Verso. We need the info state and messages to be available right after
-- elaboration, so we turn off `Elab.async`, which would let diagnostics
-- pass through asynchronously via snapshot tasks.
private def commandWithoutAsync (act : CommandElabM Unit) : CommandElabM Unit := do
  match (← get).scopes with
  | [] => act
  | h :: t =>
    let mut orig : Option Bool := none
    try
      orig := h.opts.get? `Elab.async
      modify fun s => { s with scopes := { h with opts := h.opts.setBool `Elab.async false } :: t }
      act
    finally
      if let h :: t := (← get).scopes then
        let opts := orig.map (h.opts.setBool `Elab.async) |>.getD (h.opts.erase `Elab.async)
        modify fun s => { s with scopes := { h with opts := opts } :: t }

private def withRestoringState (keepMsgs : Bool) (m : CommandElabM Unit) : CommandElabM Unit := do
  let savedState ← get
  try
    m
  finally
    let state ← get
    set { savedState with
      -- Preserve the info tree.
      infoState := state.infoState
      messages := if keepMsgs then state.messages else savedState.messages }

namespace IndentedCommands

/-! ## Indented command block parser
  Parses an indented block of commands, separated by lines. Since we want
  to capture parse errors in `sf_expect_failure`, we cannot use Lean's
  command parser directly in our command's syntax, because a parse error
  there would take down `sf_expect_failure` itself. The fix is to parse the
  entire indented body as raw syntax first, and only then run Lean's
  command parser and elaborator. -/

open Parser

private def rawLineEndFn : ParserFn :=
  eoiFn <|> satisfyFn (· == '\n') "line break"

/-- Consumes everything up to the next line break and then the break
itself. -/
private def rawLineFn : ParserFn :=
  takeUntilFn (· == '\n') >> rawLineEndFn

/- For each line after the body's first line, consumes the leading
  whitespace. If the line is blank, consumes only the line break;
  otherwise, consumes the line while requiring the indentation. -/
private def rawIndentedLineFn : ParserFn := atomicFn <|
  takeWhileFn (· == ' ') >>
  (satisfyFn (· == '\n') "line break" <|>
    (checkColGeFn "indented command sequence" >> rawLineFn))

private def rawCommandBlockFn : ParserFn :=
  rawFn (rawLineFn >> manyFn rawIndentedLineFn) (trailingWs := true)

private def rawCommandBlock : Parser := { fn := rawCommandBlockFn }

@[combinator_parenthesizer rawCommandBlock]
private def rawCommandBlock.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter rawCommandBlock]
private def rawCommandBlock.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

private partial def runRawCmdsAux
    (ictx : InputContext) (pstate : ModuleParserState) : CommandElabM Unit := do
  let state ← get
  let scope := state.scopes.head!
  let pctx :=  {
      env := state.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls : ParserModuleContext
    }
  let (cmd, pstate, messages) := parseCommand ictx pctx pstate state.messages
  modify fun state => { state with messages }
  unless cmd.isOfKind ``Command.eoi do
    elabCommand cmd
    runLinters cmd
    unless isTerminalCommand cmd do
      runRawCmdsAux ictx pstate

/- Recovers the source and elaborates the commands. -/
private def runRawCmds (body : Syntax) : CommandElabM Unit := do
  let some source := body.getSubstring? (withLeading := false) (withTrailing := false)
    | throwErrorAt body "command sequence has no source range"
  let fileName ← getFileName
  let fileMap ← getFileMap
  -- `rawIndentedLineFn` may consume whitespace after the line break; here
  -- we pull the end back to the last non-whitespace character so
  -- diagnostics get the correct position.
  let stopPos := source.trimRight.stopPos
  if h : stopPos ≤ fileMap.source.rawEndPos then
    let ictx := InputContext.mk fileMap.source fileName
      (fileMap := fileMap) (endPos := stopPos) (endPos_valid := h)
    runRawCmdsAux ictx { pos := source.startPos, recovering := false, hasLeading := false }
  else
    throwErrorAt body "invalid command-sequence source range"

end IndentedCommands

end

public meta section

open Parser IndentedCommands

/--
Elaborates the inner commands and reports their diagnostics, but discards
the effects afterward.

Example:
```lean
sf_experiment
  def hidden : Nat := 1
  #check hidden
-- `hidden` is not available here.
```
-/
def experimentTk := leading_parser
  "sf_experiment"

@[command_parser] def experimentCmd := leading_parser
  experimentTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

/--
Only succeeds if the inner commands fail.
The expected failure's diagnostics are suppressed.

Example:
```lean
sf_expect_failure
  example : 1 = 2 := rfl
```
-/
def expectFailureTk := leading_parser
  "sf_expect_failure"

/-
  Like `sf_expect_failure`, but reports the diagnostics.
-/
def expectFailureInfoTk := leading_parser
  "sf_expect_failure?"

@[command_parser] def expectFailureCmd := leading_parser
  expectFailureTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_parser] def expectFailureInfoCmd := leading_parser
  expectFailureInfoTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_elab experimentCmd]
def elabExperimentCmd : CommandElab := fun stx => do
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState true do
    runRawCmds body

@[command_elab expectFailureCmd, command_elab expectFailureInfoCmd]
def elabExpectFailureCmd : CommandElab := fun stx => do
  let keepMsgs := stx.isOfKind ``expectFailureInfoCmd
  unless keepMsgs || stx.isOfKind ``expectFailureCmd do
    throwUnsupportedSyntax
  let tk := stx[0]
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState keepMsgs do
    withRef tk <| failIfSucceeds <| runRawCmds body

end

end CSwLCompat
