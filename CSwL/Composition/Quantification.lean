import CSwL.ModelChecking
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Card
import Mathlib.Computability.Language

-- # Quantificação

namespace Composition

open ModelChecking

open FOL in
def atLeastTwo (a b : String) : LF :=
  .exists_ x (.exists_ y (.conjs
    [.neg (.eq tx ty), .atom a [tx], .atom a [ty],
     .atom b [tx], .atom b [ty]]))


def check (f : LF) : Bool :=
  f.eval entities intFairy ass0 (FOL.liftAssign fintFairy)

#eval toString <| atLeastTwo "person" "laugh"
#eval check (atLeastTwo "person" "laugh")

-- ### Exercise (1 star): at-most-two ⭐

-- Seguindo o modelo de `atLeastTwo`, defina a fórmula de "no máximo dois A
-- são B". Dica: se três elementos são A e B, dois deles são iguais.

open FOL in
def atMostTwo (a b : String) : LF :=
  sorry

theorem atMostTwo_girl :
    check (atMostTwo "girl" "laugh") = true :=
  sorry

theorem atMostTwo_person :
    check (atMostTwo "person" "laugh") = false :=
  sorry

-- ### Exercise (3 stars): at-least-n ⭐⭐⭐

-- Defina `atLeast n a b`, a fórmula de "pelo menos n A são B", e
-- `atMost n a b`, a de "no máximo n A são B". Dica: "no máximo n" é a negação
-- de "pelo menos n + 1". Para `atLeast`, uma função auxiliar recursiva pode
-- carregar a lista dos termos já quantificados, para exigir que cada nova
-- variável seja diferente de todos eles.

open FOL in
def atLeastFrom (a b : String) (n : Nat) (ts : List Term) :
    LF :=
  sorry

def atLeast (n : Nat) (a b : String) : LF :=
  sorry

def atMost (n : Nat) (a b : String) : LF :=
  sorry

theorem atLeast_person :
    check (atLeast 3 "person" "laugh") = true ∧
      check (atLeast 4 "person" "laugh") = false :=
  sorry

theorem atMost_girl :
    check (atMost 2 "girl" "laugh") = true ∧
      check (atMost 1 "girl" "laugh") = false :=
  sorry

-- ## A visão relacional dos quantificadores

def every (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → q x)

#eval (every princess) laugh

#eval [("laugh", laugh), ("cheer", cheer),
       ("shudder", shudder)]
  |>.filter (fun (_, q) => every princess q) |>.map (·.1)

def a (p q : OnePlacePred) : Bool :=
  entities.any (fun x => p x ∧ q x)

def defeated (X : OnePlacePred → Bool) : OnePlacePred :=
  fun y => X (fun z => defeat y z)

#eval entities.filter (defeated (a giant))

#eval (every dwarf) (defeated (a giant))
#eval every dwarf (defeated (a giant))

-- ## Condições sobre as relações quantificadoras

namespace GQ

abbrev Det (α : Type) := Set α → Set α → Set α → Prop

def all  {α} : Det α := fun _ A B => A ⊆ B
def some {α} : Det α := fun _ A B => ∃ x, x ∈ A ∧ x ∈ B
def no   {α} : Det α := fun _ A B => ∀ x, x ∈ A → x ∉ B
def only {α} : Det α := fun _ A B => B ⊆ A

theorem every_iff_all (p q : OnePlacePred) :
    every p q = true ↔
      all Set.univ {x | p x = true} {x | q x = true} := by
  unfold every all
  constructor
  · intro h x hx
    have hx' := List.all_eq_true.mp h x (mem_entities x)
    simp_all
  · intro h
    apply List.all_eq_true.mpr
    intro x _
    by_cases hp : p x = true
    · have hq : q x = true := h hp
      simp [hq]
    · simp [hp]

-- ### Exercise (2 stars): subalternation ⭐⭐

-- Em Quantificação vimos que, sem a pressuposição existencial, "todo A é B"
-- não implica "algum A é B". Prove as duas coisas: a subalternação vale
-- quando `A` tem um elemento, e falha em geral.

theorem all_imp_some {α : Type} (E A B : Set α)
    (hA : ∃ x, x ∈ A) (h : all E A B) : some E A B := by
  sorry

theorem all_not_imp_some :
    ¬ ∀ (A B : Set Entity),
        all Set.univ A B → some Set.univ A B := by
  sorry

def Ext {α : Type} (D : Det α) : Prop :=
  ∀ E E' A B, A ⊆ E → B ⊆ E → E ⊆ E' → (D E A B ↔ D E' A B)

def Cons {α : Type} (D : Det α) : Prop :=
  ∀ E A B, A ⊆ E → B ⊆ E → (D E A B ↔ D E A (A ∩ B))

theorem all_ext {α : Type} : Ext (all : Det α) := by
  intro E E' A B _ _ _
  rfl

theorem all_cons {α : Type} : Cons (all : Det α) := by
  intro E A B _ _
  constructor
  · intro h x hx
    exact ⟨hx, h hx⟩
  · intro h x hx
    exact (h hx).2

theorem some_ext {α : Type} : Ext (some : Det α) := by
  intro E E' A B _ _ _
  rfl

theorem some_cons {α : Type} : Cons (some : Det α) := by
  intro E A B _ _
  constructor
  · intro h
    obtain ⟨x, hA, hB⟩ := h
    exact ⟨x, hA, hA, hB⟩
  · intro h
    obtain ⟨x, hA, _, hB⟩ := h
    exact ⟨x, hA, hB⟩

-- ### Exercise (2 stars): no-cons ⭐⭐

-- Prove que **no** é conservativo.

theorem no_cons {α : Type} : Cons (no : Det α) := by
  sorry

def many {α : Type} : Det α :=
  fun E A B => E.ncard < 2 * (A ∩ B).ncard

-- ### Exercise (2 stars): many-not-ext ⭐⭐

-- Prove que `many` não satisfaz EXT. Basta um universo `E` em que a relação
-- vale e um universo maior `E'` em que ela deixa de valer.

theorem many_not_ext : ¬ Ext (many : Det Nat) := by
  sorry

-- ### Exercise (2 stars): only-not-cons ⭐⭐

-- Prove que **only** não é conservativo. Basta escolher uma restrição e um
-- escopo para os quais as duas leituras da definição de `Cons` dão resultados
-- diferentes.

theorem only_not_cons : ¬ Cons (only : Det Entity) := by
  sorry

def Isom {α : Type} (D : Det α) : Prop :=
  ∀ (f : α → α) E E' A B, A ⊆ E → B ⊆ E →
    Set.BijOn f E E' → D E A B → D E' (f '' A) (f '' B)

theorem all_isom {α : Type} : Isom (all : Det α) := by
  intro f E E' A B _ _ _ h
  exact Set.image_mono h

theorem some_isom {α : Type} : Isom (some : Det α) := by
  intro f E E' A B _ _ _ h
  obtain ⟨x, hA, hB⟩ := h
  exact ⟨f x, ⟨x, hA, rfl⟩, ⟨x, hB, rfl⟩⟩

-- ### Exercise (2 stars): the-quant ⭐⭐

-- Na leitura de Model checking, **The dwarf laughed** diz que há exatamente
-- um anão e que ele riu. Como relação entre conjuntos, `the E A B` diz que
-- `A` tem um único elemento e que ele está em `B`. Mostre que `the` satisfaz
-- EXT, CONS e ISOM. Assim, o artigo **the** é, no sentido técnico desta
-- seção, um quantificador.

def the {α : Type} : Det α :=
  fun _ A B => ∃ x, A = {x} ∧ x ∈ B

theorem the_ext {α : Type} : Ext (the : Det α) := by
  sorry

theorem the_cons {α : Type} : Cons (the : Det α) := by
  sorry

theorem the_isom {α : Type} : Isom (the : Det α) := by
  sorry

-- ### Exercise (3 stars): poss-not-isom ⭐⭐⭐

-- O possessivo **Alice's**, como em **Alice's daggers are sharp**, ocupa a
-- posição de um determinante: `poss owns a A B` diz que todo `A` que `a`
-- possui é `B`. A relação de posse `owns` é um parâmetro. Mostre que `poss`
-- satisfaz EXT e CONS, mas não ISOM. Assim, as três condições são
-- independentes: EXT e CONS não bastam para fazer de um determinante um
-- quantificador.

-- Dica: para ISOM, basta um exemplo pequeno em `Bool`, em que `false` possui
-- só `true`, e a bijeção `not`.

def poss {α : Type} (owns : α → α → Prop) (a : α) : Det α :=
  fun _ A B => ∀ x, x ∈ A → owns a x → x ∈ B

theorem poss_ext {α : Type} (owns : α → α → Prop) (a : α) :
    Ext (poss owns a) := by
  sorry

theorem poss_cons {α : Type} (owns : α → α → Prop) (a : α) :
    Cons (poss owns a) := by
  sorry

theorem poss_not_isom :
    ¬ Isom (poss (fun _ x => x = true) false) := by
  sorry

end GQ

-- ## Árvores numéricas

def row (k : Nat) : List (Nat × Nat) :=
  (List.range (k + 1)).map fun x => (k - x, x)

def tree (k : Nat) : List (List (Nat × Nat)) :=
  (List.range (k + 1)).map row

#eval tree 3

def labelTree (k : Nat) (cell : Nat → Nat → String) :
    List (List String) :=
  (tree k).map fun r => r.map fun (m, n) => cell m n

def drawTree (w : Nat) (rows : List (List String)) :
    String :=
  let last := rows.length - 1
  let lines := rows.mapIdx fun k cells =>
    let indent := (last - k) * (w + 1) / 2
    String.ofList (List.replicate indent ' ') ++
      String.intercalate " " cells
  String.intercalate "\n" lines

def numberTree (k : Nat) : String :=
  drawTree 3 (labelTree k fun m n => s!"{m},{n}")

#eval IO.println <| numberTree 3

-- ### Exercise (1 star): tree-of-numbers ⭐

-- Defina `treeOfNumbers k`, a lista dos pares de `tree k`, percorrida de cima
-- para baixo e da esquerda para a direita.

def treeOfNumbers (k : Nat) : List (Nat × Nat) :=
  sorry

theorem treeOfNumbers_three :
    treeOfNumbers 3 =
      [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2),
       (3, 0), (2, 1), (1, 2), (0, 3)] :=
  sorry

def patternTree (k : Nat) (q : Nat → Nat → Bool) :
    String :=
  drawTree 1 (labelTree k fun m n =>
    if q m n then "+" else "-")

#eval IO.println <| patternTree 5 fun _ n => n ≥ 3
#eval IO.println <| patternTree 5 fun m n => 2 * n < m + n
#eval IO.println <| patternTree 5 fun _ n => n % 2 == 0

abbrev ListQuant := List Nat → (Nat → Bool) → Bool

-- ### Exercise (2 stars): gen-tree ⭐⭐

-- Defina `genTree q k`, a lista dos pares `(m, n)` de `tree k` para os quais
-- `q` é verdadeiro num universo de `m + n` objetos dos quais exatamente `n`
-- têm a propriedade. Por exemplo, `(0, 3)` está na lista de `List.all`,
-- porque se todos os A são B, os 3 objetos de um A de 3 objetos têm a
-- propriedade B.

def genTree (q : ListQuant) (k : Nat) : List (Nat × Nat) :=
  sorry

theorem genTree_all :
    genTree List.all 3 = [(0, 0), (0, 1), (0, 2), (0, 3)] :=
  sorry

theorem genTree_any :
    genTree List.any 3 =
      [(0, 1), (1, 1), (0, 2), (2, 1), (1, 2), (0, 3)] :=
  sorry

theorem genTree_no :
    genTree (fun dom p => !dom.any p) 3 =
      [(0, 0), (1, 0), (2, 0), (3, 0)] :=
  sorry

-- ## Representações lógicas para quantificadores

abbrev NumQuant := Nat → Nat → Bool

def allNum : NumQuant := fun m _ => m = 0
def noNum  : NumQuant := fun _ n => n = 0
def atLeastNum (k : Nat) : NumQuant := fun _ n => n ≥ k
def atMostNum  (k : Nat) : NumQuant := fun _ n => n ≤ k

def toNum (q : ListQuant) : NumQuant :=
  fun m n => q (List.range' 1 (m + n)) (fun x => x ≤ n)

theorem toNum_all :
    patternTree 5 (toNum List.all) =
      patternTree 5 allNum := by
  rfl

theorem toNum_no :
    patternTree 5 (toNum fun dom p => !dom.any p) =
      patternTree 5 noNum := by
  rfl

def notNum (q : NumQuant) : NumQuant :=
  fun m n => !q m n

def andNum (q₁ q₂ : NumQuant) : NumQuant :=
  fun m n => q₁ m n && q₂ m n

def orNum (q₁ q₂ : NumQuant) : NumQuant :=
  fun m n => q₁ m n || q₂ m n

def atLeast3ButNotAll : NumQuant :=
  andNum (atLeastNum 3) (notNum allNum)

#eval IO.println <| patternTree 5 atLeast3ButNotAll

-- ### Exercise (3 stars): tree-patterns ⭐⭐⭐

-- Defina `someNum`, `notAllNum` e `exactlyNum k`, as expressões de **some**,
-- **not all** e **exactly k**. Use `patternTree` para ver os padrões de
-- **all**, **some**, **no** e **not all**, e os de **at least three**, **at
-- most three** e **exactly three**. Depois, prove as relações entre eles:
-- **some** é a negação de **no**, **not all** é a negação de **all**,
-- **exactly k** é a conjunção de **at least k** e **at most k**, e **at most
-- k** é a negação de **at least k + 1**.

-- Dica: depois de `funext m n`, `rw [Bool.eq_iff_iff]` transforma a igualdade
-- entre dois `Bool` numa equivalência entre proposições. Em seguida, `simp`
-- com as definições simplifica a meta, e `omega` resolve o que sobrar de
-- aritmética.

def someNum : NumQuant :=
  sorry

def notAllNum : NumQuant :=
  sorry

def exactlyNum (k : Nat) : NumQuant :=
  sorry

theorem someNum_eq : someNum = notNum noNum := by
  sorry

theorem notAllNum_eq : notAllNum = notNum allNum := by
  sorry

theorem exactlyNum_eq (k : Nat) :
    exactlyNum k = andNum (atLeastNum k) (atMostNum k) := by
  sorry

theorem atMostNum_eq (k : Nat) :
    atMostNum k = notNum (atLeastNum (k + 1)) := by
  sorry

-- ## Propriedades relacionais

namespace GQ

def Refl {α : Type} (D : Det α) : Prop :=
  ∀ E A, A ⊆ E → D E A A

theorem all_refl {α : Type} : Refl (all : Det α) := by
  intro E A ha x hx
  exact hx

-- ### Exercise (1 star): some-not-refl ⭐

-- Prove que **some** não é reflexivo.

theorem some_not_refl : ¬ Refl (some : Det Entity) := by
  sorry

def ReflNum (q : NumQuant) : Prop :=
  ∀ n, q 0 n

theorem allNum_refl : ReflNum allNum := by
  intro n
  rfl

#eval IO.println <| patternTree 5 allNum
#eval IO.println <| patternTree 5 (notNum noNum)

-- _Quiz:_

-- Se a borda direita do padrão de `Q` é toda `-`, que propriedade `Q` tem?
-- Qual quantificador do nosso elenco tem esse padrão? E **no**, tem?

#eval (a girl laugh, a laugh girl)
#eval (every princess laugh, every laugh princess)

def Symm {α : Type} (D : Det α) : Prop :=
  ∀ E A B, A ⊆ E → B ⊆ E → (D E A B ↔ D E B A)

theorem some_symm {α : Type} : Symm (some : Det α) := by
  intro E A B _ _
  constructor
  · intro h
    obtain ⟨x, hA, hB⟩ := h
    exact ⟨x, hB, hA⟩
  · intro h
    obtain ⟨x, hB, hA⟩ := h
    exact ⟨x, hA, hB⟩

-- ### Exercise (2 stars): symm-pattern ⭐⭐

-- Defina `SymmNum q`, a forma do padrão de um quantificador simétrico.
-- Depois, prove que **no** e **at least three** têm essa forma, e que **all**
-- não tem.

-- Dica: em `Q A B`, `m` conta os A que não são B; em `Q B A`, conta os B que
-- não são A. O que muda entre os dois é só `m`.

def SymmNum (q : NumQuant) : Prop :=
  sorry

theorem noNum_symm : SymmNum noNum := by
  sorry

theorem atLeastNum_symm : SymmNum (atLeastNum 3) := by
  sorry

theorem allNum_not_symm : ¬ SymmNum allNum := by
  sorry

def MonUp {α : Type} (D : Det α) : Prop :=
  ∀ E A B B', A ⊆ E → B ⊆ B' → B' ⊆ E →
    D E A B → D E A B'

def MonDown {α : Type} (D : Det α) : Prop :=
  ∀ E A B B', A ⊆ E → B' ⊆ B → B ⊆ E →
    D E A B → D E A B'

theorem all_monUp {α : Type} : MonUp (all : Det α) := by
  intro E A B B' _ hB _ h x hx
  exact hB (h hx)

-- ### Exercise (1 star): no-mon-down ⭐

-- Prove que **no** é MON↓.

theorem no_monDown {α : Type} : MonDown (no : Det α) := by
  sorry

end GQ

-- _Quiz:_

-- Compare os padrões de **all** e de **at least three**, que são MON↑. Que
-- forma tem o padrão de um quantificador MON↑? E o de um MON↓?

def MonUpNum (q : NumQuant) : Prop :=
  ∀ m n, q (m + 1) n → q m (n + 1)

def MonDownNum (q : NumQuant) : Prop :=
  ∀ m n, q m (n + 1) → q (m + 1) n

def evenNum : NumQuant := fun _ n => n % 2 == 0

theorem atLeastNum_monUp (k : Nat) :
    MonUpNum (atLeastNum k) := by
  intro m n h
  simp [atLeastNum] at *
  omega

theorem noNum_monDown : MonDownNum noNum := by
  intro m n h
  simp [noNum] at h

-- ### Exercise (2 stars): even-not-mon ⭐⭐

-- Prove que **an even number of** não é MON↑ nem MON↓. Basta uma posição do
-- padrão em que a forma falha.

theorem evenNum_not_monUp : ¬ MonUpNum evenNum := by
  sorry

theorem evenNum_not_monDown : ¬ MonDownNum evenNum := by
  sorry

-- ### Exercise (2 stars): mon-not ⭐⭐

-- Prove que a negação troca MON↑ por MON↓, e MON↓ por MON↑.

theorem notNum_monUp (q : NumQuant) (h : MonUpNum q) :
    MonDownNum (notNum q) := by
  sorry

theorem notNum_monDown (q : NumQuant) (h : MonDownNum q) :
    MonUpNum (notNum q) := by
  sorry

-- ### Exercise (2 stars): mon-and ⭐⭐

-- Prove que a conjunção de dois quantificadores MON↑ é MON↑, e que a de dois
-- MON↓ é MON↓.

theorem andNum_monUp (q₁ q₂ : NumQuant)
    (h₁ : MonUpNum q₁) (h₂ : MonUpNum q₂) :
    MonUpNum (andNum q₁ q₂) := by
  sorry

theorem andNum_monDown (q₁ q₂ : NumQuant)
    (h₁ : MonDownNum q₁) (h₂ : MonDownNum q₂) :
    MonDownNum (andNum q₁ q₂) := by
  sorry

-- ### Exercise (2 stars): mon-or ⭐⭐

-- Prove que a disjunção de dois quantificadores MON↑ é MON↑, e que a de dois
-- MON↓ é MON↓.

theorem orNum_monUp (q₁ q₂ : NumQuant)
    (h₁ : MonUpNum q₁) (h₂ : MonUpNum q₂) :
    MonUpNum (orNum q₁ q₂) := by
  sorry

theorem orNum_monDown (q₁ q₂ : NumQuant)
    (h₁ : MonDownNum q₁) (h₂ : MonDownNum q₂) :
    MonDownNum (orNum q₁ q₂) := by
  sorry

-- ### Exercise (3 stars): mon-up-down ⭐⭐⭐

-- Mostre que, combinando um quantificador MON↑ com um MON↓, nada se pode
-- garantir: nem a conjunção nem a disjunção são sempre MON↑ ou MON↓.

-- Dica: para a conjunção, use **at least one** e **at most three**; para a
-- disjunção, **at least three** e **at most one**. Antes de provar, desenhe
-- os padrões da conjunção e da disjunção com `patternTree`.

theorem andNum_up_down :
    ¬ ∀ q₁ q₂, MonUpNum q₁ → MonDownNum q₂ →
      MonUpNum (andNum q₁ q₂) ∨
        MonDownNum (andNum q₁ q₂) := by
  sorry

theorem orNum_up_down :
    ¬ ∀ q₁ q₂, MonUpNum q₁ → MonDownNum q₂ →
      MonUpNum (orNum q₁ q₂) ∨
        MonDownNum (orNum q₁ q₂) := by
  sorry

-- ### Exercise (2 stars): left-mon-pattern ⭐⭐

-- Defina `UpMonNum q` e `DownMonNum q`, as formas do padrão de um
-- quantificador ↑MON e de um ↓MON. Depois, prove que **some** e **not all**
-- são ↑MON, e que **all** e **no** são ↓MON.

-- Dica: acrescentar um elemento a `A` aumenta em um `n`, se o elemento está
-- em `B`, ou `m`, se não está.

def UpMonNum (q : NumQuant) : Prop :=
  sorry

def DownMonNum (q : NumQuant) : Prop :=
  sorry

theorem some_upMon : UpMonNum (notNum noNum) := by
  sorry

theorem notAll_upMon : UpMonNum (notNum allNum) := by
  sorry

theorem all_downMon : DownMonNum allNum := by
  sorry

theorem no_downMon : DownMonNum noNum := by
  sorry

-- ## Quantificadores, autômatos e definibilidade

abbrev Word := List Bool

def wordOf (A : List Entity) (B : OnePlacePred) : Word :=
  A.map B

def accepts (q : NumQuant) (w : Word) : Bool :=
  q (w.count false) (w.count true)

def langOf (q : NumQuant) : Language Bool :=
  {w | accepts q w}

theorem mem_langOf (q : NumQuant) (w : Word) :
    w ∈ langOf q ↔ accepts q w :=
  Iff.rfl

#eval wordOf (entities.filter girl) laugh
#eval (accepts allNum (wordOf (entities.filter girl) laugh),
  accepts (notNum noNum)
    (wordOf (entities.filter girl) laugh))

theorem langOf_perm (q : NumQuant) {v w : Word}
    (h : v.Perm w) (hv : v ∈ langOf q) :
    w ∈ langOf q := by
  rw [mem_langOf, accepts] at *
  rw [← h.count_eq, ← h.count_eq]
  exact hv

theorem langOf_notNum (q : NumQuant) :
    langOf (notNum q) = (langOf q)ᶜ := by
  ext w
  show accepts (notNum q) w ↔ ¬ accepts q w
  simp [accepts, notNum]

-- ### Exercise (2 stars): lang-and-or ⭐⭐

-- Prove que a conjunção `andNum` dá a interseção das linguagens, `⊓`, e que a
-- disjunção `orNum` dá a união, `+`.

theorem langOf_andNum (q₁ q₂ : NumQuant) :
    langOf (andNum q₁ q₂) = langOf q₁ ⊓ langOf q₂ := by
  sorry

theorem langOf_orNum (q₁ q₂ : NumQuant) :
    langOf (orNum q₁ q₂) = langOf q₁ + langOf q₂ := by
  sorry

-- ### Exercise (3 stars): all-kstar ⭐⭐⭐

-- Prove que a linguagem de **all** é `{[true]}∗`.

open Computability in
theorem langOf_allNum :
    langOf allNum = ({[true]} : Language Bool)∗ := by
  sorry

end Composition

