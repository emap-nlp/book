import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Palindrome

-- # Reconhecendo e analisando linguagens livres de contexto

namespace Parsing

def split2 {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
    ([], x :: xs) ::
      (split2 xs).map fun (ys, zs) => (x :: ys, zs)

#eval split2 "Jan".toList |>.map
  λ (a, b) ↦ (String.ofList a, String.ofList b)

def splitN {α : Type} : Nat → List α → List (List (List α))
  | 0, [] => [[]]
  | 0, _ :: _ => []
  | 1, xs => [[xs]]
  | n + 2, xs =>
    (split2 xs).flatMap fun (ys, zs) =>
      (splitN (n + 1) zs).map fun rs => ys :: rs

#eval splitN 3 "Jan".toList |>.map
   (·.map String.ofList)

-- THE FOLLOWING DETAILS CAN BE SKIPPED (As divisões juntam-se de volta na entrada)
theorem append_of_mem_split2 {α : Type} :
    ∀ {xs : List α} {p : List α × List α},
      p ∈ split2 xs → p.1 ++ p.2 = xs
  | [], p, h => by
    simp [split2] at h
    simp [h]
  | x :: xs, p, h => by
    simp only [split2, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨ys, zs⟩, h, rfl⟩
    · rfl
    · simp [← append_of_mem_split2 h]

theorem flatten_of_mem_splitN {α : Type} :
    ∀ {n : Nat} {xs : List α} {l : List (List α)},
      l ∈ splitN n xs → l.flatten = xs
  | 0, [], l, h | 1, _, l, h => by
    simp [splitN] at h
    simp [h]
  | 0, _ :: _, _, h => by simp [splitN] at h
  | n + 2, xs, l, h => by
    simp only [splitN, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨ys, zs⟩, h1, rs, h2, rfl⟩ := h
    simp [flatten_of_mem_splitN h2, append_of_mem_split2 h1]
-- END DETAILS

def recognize (xs : List Char) : Bool :=
  xs == [] || xs == ['a'] || xs == ['b'] || xs == ['c'] ||
  (splitN 3 xs).attach.any fun
    | ⟨[['a'], ys, ['a']], h⟩ => recognize ys
    | ⟨[['b'], ys, ['b']], h⟩ => recognize ys
    | ⟨[['c'], ys, ['c']], h⟩ => recognize ys
    | _ => false
termination_by xs.length
decreasing_by
  all_goals
    have := congrArg List.length (flatten_of_mem_splitN h)
    simp at this
    omega

#eval recognize "aabcbbcbaa".toList
#eval recognize "aabcbbcba".toList

def gener {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, alphabet =>
    alphabet.flatMap fun x =>
      (gener n alphabet).map (x :: ·)

def generUpTo {α : Type} (n : Nat) (alphabet : List α) :
    List (List α) :=
  (List.range (n + 1)).flatMap fun k => gener k alphabet

#eval ((generUpTo 3 "abc".toList).filter recognize).map
  String.ofList

-- THE FOLLOWING DETAILS CAN BE SKIPPED (O reconhecedor e a definição de palíndromo)
theorem mem_split2_append {α : Type} :
    ∀ ys zs : List α, (ys, zs) ∈ split2 (ys ++ zs)
  | [], [] => by simp [split2]
  | [], z :: zs => by simp [split2]
  | y :: ys, zs => by
    simp only [List.cons_append, split2, List.mem_cons,
      List.mem_map]
    exact Or.inr ⟨(ys, zs), mem_split2_append ys zs, rfl⟩

theorem mem_splitN_flatten {α : Type} :
    ∀ l : List (List α), l ∈ splitN l.length l.flatten
  | [] => by simp [splitN]
  | [ys] => by simp [splitN]
  | ys :: zs :: rs => by
    simp only [List.length_cons, List.flatten_cons]
    simp only [splitN, List.mem_flatMap, List.mem_map]
    refine ⟨(ys, (zs :: rs).flatten),
      by simpa using mem_split2_append ys _,
      zs :: rs, ?_, rfl⟩
    simpa using mem_splitN_flatten (zs :: rs)

theorem recognize_sound (n : Nat) :
    ∀ w : List Char, w.length ≤ n →
      recognize w → w.Palindrome := by
  induction n with
  | zero =>
    intro w hw hr
    simp at hw
    rw [hw]
    exact .nil
  | succ n ih =>
    intro w hw h
    rw [recognize] at h
    simp only [Bool.or_eq_true, beq_iff_eq,
      List.any_eq_true] at h
    rcases h with (((rfl | rfl) | rfl) | rfl)
      | ⟨⟨l, hl⟩, _, hm⟩
    · exact .nil
    · exact .singleton _
    · exact .singleton _
    · exact .singleton _
    · split at hm <;> (try contradiction) <;>
      · rename_i ys hys _
        have he := flatten_of_mem_splitN hys
        simp at he
        subst he
        apply List.Palindrome.cons_concat
        exact ih ys (by simp at hw; omega) hm

theorem recognize_complete (n : Nat) :
    ∀ w : List Char, w.length ≤ n → w ⊆ "abc".toList →
      w.Palindrome → recognize w = true := by
  induction n with
  | zero =>
    intro w hw _ _
    simp at hw
    subst hw
    rw [recognize]
    simp
  | succ n ih =>
    intro w hw ha hp
    cases hp with
    | nil =>
      rw [recognize]
      simp
    | singleton x =>
      have hx : x ∈ "abc".toList := ha (by simp)
      simp at hx
      rcases hx with rfl | rfl | rfl <;>
        (rw [recognize]; simp)
    | cons_concat x hl =>
      rename_i l
      have hx : x ∈ "abc".toList := ha (by simp)
      have hl' : l ⊆ "abc".toList :=
        fun c hc => ha (by simp [hc])
      have ih' := ih l (by simp at hw; omega) hl' hl
      rw [recognize]
      simp only [Bool.or_eq_true, beq_iff_eq,
        List.any_eq_true]
      right
      have hmem :
          [[x], l, [x]] ∈ splitN 3 (x :: (l ++ [x])) := by
        simpa using mem_splitN_flatten [[x], l, [x]]
      refine ⟨⟨_, hmem⟩, List.mem_attach _ _, ?_⟩
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ih'

theorem recognize_iff_palindrome (w : List Char)
    (hw : w ⊆ "abc".toList) :
    recognize w ↔ w.Palindrome :=
  ⟨recognize_sound _ w (Nat.le_refl _),
   recognize_complete _ w (Nat.le_refl _) hw⟩

theorem subset_of_mem_gener {α : Type} (alphabet : List α) :
    ∀ n w, w ∈ gener n alphabet → w ⊆ alphabet
  | 0, w, h => by
    simp [gener] at h
    simp [h]
  | n + 1, w, h => by
    simp only [gener, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, v, hv, rfl⟩ := h
    intro c hc
    simp at hc
    rcases hc with rfl | hc
    · exact hx
    · exact subset_of_mem_gener alphabet n v hv hc

theorem recognize_generUpTo (n : Nat) :
    ∀ w ∈ generUpTo n "abc".toList,
      recognize w = true ↔ w.Palindrome := by
  intro w hw
  simp only [generUpTo, List.mem_flatMap] at hw
  obtain ⟨k, _, hk⟩ := hw
  exact recognize_iff_palindrome w
    (subset_of_mem_gener _ k w hk)
-- END DETAILS

def parse (xs : List Char) : List (ParseTree Char Char) :=
  (if xs == [] then [.ep] else []) ++
  (if xs == ['a'] then [.leaf 'a'] else []) ++
  (if xs == ['b'] then [.leaf 'b'] else []) ++
  (if xs == ['c'] then [.leaf 'c'] else []) ++
  (splitN 3 xs).attach.flatMap fun
    | ⟨[['a'], ys, ['a']], _h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'a', t, .leaf 'a']
    | ⟨[['b'], ys, ['b']], _h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'b', t, .leaf 'b']
    | ⟨[['c'], ys, ['c']], _h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'c', t, .leaf 'c']
    | _ => []
termination_by xs.length
decreasing_by
  all_goals
    have := congrArg List.length (flatten_of_mem_splitN _h)
    simp at this
    omega

#eval IO.println (parse "aabaa".toList)
#eval IO.println (parse "aabbaa".toList)
#eval IO.println (parse "aabcbbcba".toList)

-- ### Exercise (2 stars): split-nonempty ⭐⭐

-- Numa gramática sem regras ε, nenhum pedaço da divisão pode ser vazio.
-- Defina `split2'` e `splitN'`, que dão só as divisões sem pedaços vazios.
-- Confira o resultado em `"Jan"`.

def split2' {α : Type} : List α → List (List α × List α)
  | [] | [_] => []
  | x :: y :: ys =>
    sorry

def splitN' {α : Type} : Nat → List α → List (List (List α))
  | 0, [] => [[]]
  | 0, _ :: _ => []
  | 1, [] => []
  | 1, xs => [[xs]]
  | n + 2, xs =>
    sorry

theorem split2'_jan :
    split2' "Jan".toList =
      [(['J'], ['a', 'n']), (['J', 'a'], ['n'])] := by
  sorry

theorem splitN'_jan :
    splitN' 3 "Jan".toList = [[['J'], ['a'], ['n']]] := by
  sorry

end Parsing

