-- # Falando de árvores sintáticas

namespace Parsing

inductive ParseTree (α β : Type) where
  | ep
  | leaf (a : α)
  | branch (b : β) (ts : List (ParseTree α β))
  deriving Repr, BEq

def ParseTree.toText {α β : Type}
    [ToString α] [ToString β] : ParseTree α β → String
  | .ep => "[]"
  | .leaf a => toString a
  | .branch b ts =>
    "[." ++ toString b ++ " " ++
      " ".intercalate (ts.map toText) ++ "]"

instance {α β : Type} [ToString α] [ToString β] :
    ToString (ParseTree α β) :=
  ⟨ParseTree.toText⟩

def snowWhite : ParseTree String String :=
  .branch "S"
    [.branch "NP" [.leaf "Snow White"],
     .branch "VP" [.branch "TV" [.leaf "loved"],
                   .branch "NP" [.leaf "the dwarfs"]]]

#eval IO.println snowWhite

abbrev Pos := List Nat

def pos {α β : Type} (p : ParseTree α β) : List Pos :=
  let rec posFrom {α β : Type} :
    Nat → List (ParseTree α β) → List Pos
   | _, [] => []
   | i, t :: ts =>
     (pos t).map (i :: ·) ++ posFrom (i + 1) ts
  match p with
  | .ep => [[]]
  | .leaf _ => [[]]
  | .branch _ ts => [] :: posFrom 0 ts

#eval pos snowWhite

def subtree {α β : Type} :
  ParseTree α β → Pos → ParseTree α β
  | t, [] => t
  | .branch _ ts, i :: is =>
    match ts[i]? with
    | some t => subtree t is
    | none => .ep
  | _, _ :: _ => .ep

def subtrees {α β : Type} (t : ParseTree α β)
  : List (ParseTree α β) :=
  (pos t).map (subtree t)

#eval IO.println (subtree snowWhite [1])

def posPairs {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (pos t).flatMap fun p => (pos t).map fun q => (p, q)

def properDominance {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => p ≠ q && p <+: q

def dominance {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => p <+: q

#eval properDominance snowWhite

-- ### Exercise (2 stars): imm-dominance ⭐⭐

-- A posição `p` **domina imediatamente** `q` quando `p` domina propriamente
-- `q` e não há posição `r`, diferente das duas, tal que `p` domina `r` e `r`
-- domina `q`. Defina `immDominance` e confira o resultado na árvore
-- `snowWhite`.

def immDominance {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  sorry

theorem immDominance_snowWhite :
    immDominance snowWhite =
      [([], [0]), ([], [1]), ([0], [0, 0]), ([1], [1, 0]),
       ([1], [1, 1]), ([1, 0], [1, 0, 0]),
       ([1, 1], [1, 1, 0])] := by
  sorry

def sisters : Pos → Pos → Bool
  | [i], [j] => i != j
  | i :: is, j :: js => i == j && sisters is js
  | _, _ => false

def sisterhood {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => sisters p q

#eval sisterhood snowWhite

def relComp {γ : Type} [BEq γ] (r s : List (γ × γ)) :
    List (γ × γ) :=
  (r.flatMap fun (x, y) =>
    (s.filter fun (w, _) => y == w).map fun (_, z) =>
      (x, z)).eraseDups

def cCommand {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  relComp (sisterhood t) (dominance t)

#eval dominance snowWhite
#eval cCommand snowWhite

def branchingPos {α β : Type} (t : ParseTree α β) :
    List Pos :=
  let ps := pos t
  ps.filter fun p =>
    ps.contains (p ++ [0]) && ps.contains (p ++ [1])

#eval branchingPos snowWhite

-- THE FOLLOWING DETAILS CAN BE SKIPPED (Dois lemas sobre posições irmãs)
theorem sisters_length (p r : Pos)
    (h : sisters p r = true) : p.length = r.length := by
  induction p generalizing r with
  | nil => simp [sisters] at h
  | cons i is ih =>
    cases r with
    | nil => simp [sisters] at h
    | cons j js =>
      cases is with
      | nil =>
        cases js with
        | nil => rfl
        | cons k ks => simp [sisters] at h
      | cons i' is' =>
        cases js with
        | nil => simp [sisters] at h
        | cons k ks =>
          simp only [sisters, Bool.and_eq_true] at h
          simp [ih _ h.2]

theorem sisters_not_prefix (p r : Pos)
    (h : sisters p r = true) : ¬ p <+: r := by
  induction p generalizing r with
  | nil => simp [sisters] at h
  | cons i is ih =>
    cases r with
    | nil => simp [sisters] at h
    | cons j js =>
      cases is with
      | nil =>
        cases js with
        | nil => simp_all [sisters]
        | cons k ks => simp_all [sisters]
      | cons i' is' =>
        cases js with
        | nil => simp [sisters] at h
        | cons k ks =>
          simp only [sisters, Bool.and_eq_true,
            beq_iff_eq] at h
          obtain ⟨rfl, h⟩ := h
          rw [List.cons_prefix_cons]
          intro ⟨_, hp⟩
          exact ih _ h hp
-- END DETAILS

-- ### Exercise (3 stars): c-command-dominance ⭐⭐⭐

-- Suponha que `p` c-comanda `q`: uma irmã `r` de `p` domina `q`. Prove que
-- `p` não domina `q` e que `q` não domina `p`.

-- Dica: um prefixo de `q` que não é mais longo do que outro prefixo de `q` é
-- prefixo dele (`List.prefix_of_prefix_length_le`), e um prefixo do mesmo
-- comprimento é a própria lista (`List.IsPrefix.eq_of_length`).

theorem cCommand_not_dominates (p r q : Pos)
    (hs : sisters p r = true) (hd : r <+: q) :
    ¬ p <+: q := by
  sorry

theorem cCommand_not_dominated (p r q : Pos)
    (hs : sisters p r = true) (hd : r <+: q) :
    ¬ q <+: p := by
  sorry

-- ### Exercise (2 stars): mutual-c-command ⭐⭐

-- O c-comando não é simétrico, mas o **c-comando mútuo** é: `p` e `q` se
-- c-comandam mutuamente quando `p` c-comanda `q` e `q` c-comanda `p`. Defina
-- `mutualCCommand` e confira, na árvore `snowWhite`, que ele coincide com a
-- relação de irmãs.

def mutualCCommand {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  sorry

theorem mutualCCommand_snowWhite :
    mutualCCommand snowWhite = sisterhood snowWhite := by
  sorry

def precede : Pos → Pos → Bool
  | i :: is, j :: js => i < j || (i == j && precede is js)
  | _, _ => false

def precedence {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  (posPairs t).filter fun (p, q) => precede p q

#eval precedence snowWhite

-- ### Exercise (2 stars): imm-precedence ⭐⭐

-- Defina a **precedência imediata**, a partir da precedência, do mesmo modo
-- que a dominância imediata foi definida a partir da dominância. Confira o
-- resultado na árvore `snowWhite`.

def immPrecedence {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  sorry

theorem immPrecedence_snowWhite :
    immPrecedence snowWhite =
      [([0], [1]), ([0], [1, 0]), ([0], [1, 0, 0]),
       ([0, 0], [1]), ([0, 0], [1, 0]),
       ([0, 0], [1, 0, 0]), ([1, 0], [1, 1]),
       ([1, 0], [1, 1, 0]), ([1, 0, 0], [1, 1]),
       ([1, 0, 0], [1, 1, 0])] := by
  sorry

-- ### Exercise (2 stars): command ⭐⭐

-- Defina `command` supondo que o S mais próximo é sempre a raiz da árvore.
-- Confira o resultado na árvore `snowWhite`.

def command {α β : Type} (t : ParseTree α β) :
    List (Pos × Pos) :=
  sorry

theorem command_snowWhite :
    (command snowWhite).length = 28 := by
  sorry

end Parsing

