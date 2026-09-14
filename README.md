# CSwL — `student` variant

Generated from the book (Verso, `Manual` genre) by `lake exe cswl-book student` — **do not edit here**: the source is `CSwL`, and the next build overwrites this directory.

## Setting up

Install Lean with [elan](https://lean-lang.org/install). Then, in this
directory, fetch the prebuilt Mathlib and build:

    lake exe cache get
    lake build

`lake exe cache get` matters: without it, `lake build` compiles all of
Mathlib from scratch.

Use VS Code with the Lean 4 extension, and open **this directory** as
the folder — not a file inside it, or the extension will not find the
project.

## Working the exercises

Each exercise is a `sorry` to replace. Lean checks your answer as you
type: while a `sorry` remains, the file reports a warning, and when the
proof or definition is complete the warning disappears. The InfoView
panel shows the goal at the cursor.

The exercises are in the same order as the book, and each one sits in
the chapter section that discusses it. Read the corresponding section
of the book alongside the code.

Keep your own copy of anything you want to survive: this directory is
regenerated from the book, and a rebuild overwrites whatever is here.

## Reporting a problem

If something does not build, a statement is ambiguous, or the prose is
wrong, open an issue at
<https://github.com/cslib-community/CSwL/issues>. Say which chapter and
which exercise, and paste the message Lean gave you.
