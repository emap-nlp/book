import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic

-- # Conjuntos e Relações

-- Conjuntos e relações são a notação que todo texto de matemática pressupõe.
-- Este capítulo é onde eles se tornam objetos do Lean — e onde as afirmações
-- que se costuma fazer sobre eles passam a ser teoremas a demonstrar.

namespace Sets

open Set

-- ## Conjuntos e notação de conjuntos

-- Um conjunto de elementos de `α` por sua função característica: a função
-- que, dado um elemento, responde se ele pertence ao conjunto. Há duas
-- maneiras de responder:

-- - `α → Bool` calcula a resposta. O resultado é `true` ou `false`, e pode-se
--   rodar.

-- - `α → Prop` enuncia a resposta. O resultado é uma afirmação, que se pode
--   provar.

-- A segunda versão é, literalmente, como conjuntos são definidos no Lean.

#print Set

-- def Set.{u} : Type u → Type u :=
-- fun α => α → Prop

def S1 : Set ℕ := {10}
def S2 : Set ℕ := {10, 20}

#check S1

-- Sets.S1 : Set ℕ

#check 10 ∈ S1

-- 10 ∈ S1 : Prop

#check S1 ⊆ S2

-- S1 ⊆ S2 : Prop

example : (10 ∈ S1) = (S1 10) := rfl

-- Um `Set α` é uma função `α → Prop`, e nada mais. A notação de conjunto que
-- se escreve na prática é açúcar para construir essa função, e pertencer é
-- aplicá-la — as duas coisas são a mesma, e o `rfl` prova:

example : {n : Nat | n > 2} = Set.ofPred (λ n ↦ n > 2) :=
  rfl

example (p : Nat → Prop) (x : Nat) :
    (x ∈ {n | p n}) = p x := rfl

-- conjunto vazio e conjunto universal

def my_emptyset : Set ℕ := fun _ ↦ False
example: my_emptyset = ∅  := by rfl

def my_univ : Set ℕ := fun _ ↦ True
example: my_univ = Set.univ := by rfl

-- Escrever `x ∈ A` em vez de `A x` é comodidade de leitura. Vale saber disso
-- porque, quando uma prova sobre conjuntos empacar, desdobrar a notação até a
-- aplicação costuma destravar — e o desdobramento é `rfl`, não um passo que
-- precise de justificativa. Então `above2`, aplicado, é o predicado aplicado
-- — e `above2 3` é literalmente `3 > 2`, sem nenhuma camada de conjunto no
-- meio:

def above2 : Set Nat := {n | n > 2}

example : (3 ∈ above2) = above2 3 := rfl
example : above2 3 = (3 > 2) := rfl

-- `decide` sozinho **não** fecha `3 ∈ above2`: a mensagem é
-- `failed to
-- synthesize Decidable (3 ∈ above2)`. O motivo é que `above2` é um
-- `def`, e `decide` não desdobra definições — para ele o objetivo é opaco.
-- `unfold` faz esse desdobramento manualmente, e depois `decide` calcula:

example : 3 ∈ above2 := by
  unfold above2
  decide

-- ### Aquecimento: conjuntos com nome

def above5 : Set Nat := {n | n > 5}

-- ### Exercise (1 star): five-in-above2 ⭐

-- **A1.** Prove que 5 pertence a `above2`.

example : 5 ∈ above2 := sorry

-- ### Exercise (1 star): one-not-in-above2 ⭐

-- **A2.** Prove que 1 não pertence a `above2`. `x ∉ A` abrevia `¬ (x ∈ A)`,
-- que por sua vez é `x ∈ A → False`.

example : 1 ∉ above2 := sorry

-- ### Exercise (1 star): above5-subset-above2 ⭐

-- **A3.** Prove a inclusão. `unfold above2 above5` desdobra as duas
-- definições; `simp only [Set.mem_ofPred_eq] at h` desdobra a pertinência em
-- `h` até a desigualdade, que `omega` então resolve.

example : above5 ⊆ above2 := sorry

-- União e interseção são disjunção e conjunção elemento a elemento. As duas
-- inclusões abaixo valem para conjuntos quaisquer, e as provas não precisam
-- saber nada sobre eles.

-- ### Exercise (1 star): union-contains ⭐

-- **A4.** Todo conjunto está contido na sua união com outro. Depois do
-- `intro`, `Or.inl` prova uma disjunção pelo lado esquerdo.

example (A B : Set Nat) : A ⊆ A ∪ B := sorry

-- ### Exercise (1 star): intersection-contained ⭐

-- **A5.** E a interseção está contida em cada um dos dois.

example (A B : Set Nat) : A ∩ B ⊆ A := sorry

-- A Mathlib tem esses dois últimos prontos, com os nomes
-- `Set.subset_union_left` e `Set.inter_subset_left`. Aqui o exercício é
-- escrever a prova, não encontrá-los — mas vale procurar depois, para ver
-- como as coisas se chamam.

-- ### Mais teoria dos conjuntos

section
variable {α : Type} (A B C D : Set α)

example : A ⊆ A := by
  rw [subset_def]
  intro x h
  assumption

example (A B : Set ℕ) :
    (A ⊆ B) = (∀ x, x ∈ A → x ∈ B) := rfl

#check mem_inter_iff

-- Set.mem_inter_iff.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b

example : A ∩ B ⊆ B := by
  intro x h
  rw [mem_inter_iff] at h
  obtain ⟨xA,xB⟩ := h
  exact xB

#check subset_def

-- Set.subset_def.{u} {α : Type u} {s t : Set α} : (s ⊆ t) = ∀ x ∈ s, x ∈ t

-- **A6.** Transitividade da inclusão.

example : A ⊆ B → B ⊆ C → A ⊆ C := sorry

#check Set.inter_def

-- Set.inter_def.{u} {α : Type u} {s₁ s₂ : Set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂}

-- **A7.** Se `A` está contido em `B` e em `C`, está contido na interseção.

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := sorry

-- ### Exercise (1 star): empty-subset ⭐

-- Explique por que `∅ ⊆ A` vale para todo conjunto `A`. Prove-o. O argumento
-- é vacuoso, e a prova deve exibir isso.

-- **Não vale usar `Set.empty_subset`** (nem `simp`, que o encontra): esse
-- lema é exatamente o enunciado, e citá-lo apagaria o exercício.

example : ∅ ⊆ A := sorry

-- ### Exercise (1 star): empty-vs-singleton ⭐

-- Explique a diferença entre `∅` e `{∅}`.

-- `∅` é o conjunto que não tem elemento nenhum; `{∅}` é um conjunto que tem
-- exatamente um elemento, e esse elemento é o conjunto vazio. São, portanto,
-- objetos distintos: um está vazio, o outro não. A confusão vem de olhar para
-- o "conteúdo do conteúdo" — o único elemento de `{∅}` é ele mesmo vazio, mas
-- isso não faz o recipiente ficar vazio.

-- Cardinalidades: `|∅| = 0` e `|{∅}| = 1`. (A prova abaixo explora justamente
-- isso: `∅ ∈ {∅}` vale por `rfl`, e transportar essa pertinência pela
-- igualdade suposta daria `∅ ∈ ∅`, isto é, `False`.)

-- **Não vale usar `Set.singleton_ne_empty`, `Set.empty_ne_singleton` nem
-- `simp`.**

example :
    (∅ : Set (Set α)) ≠ ({∅} : Set (Set α)) := sorry

-- ### Exercise (2 stars): double-complement ⭐⭐

-- Verifique que o complemento do complemento de `A` é `A`.

-- Use `Set.ext`. Uma das duas direções precisa de raciocínio clássico: vale
-- `Classical.byContradiction`, `Classical.em` ou `Classical.byCases`.

-- **Não vale usar `compl_compl`** (nem `simp`, nem `tauto`, nem `grind`): a
-- Mathlib prova esse lema para qualquer álgebra de Boole, e conjuntos são
-- uma. Aqui o exercício é o argumento sobre elementos.

-- **Qual inclusão precisou do argumento clássico?** A direção que precisa é
-- `Aᶜᶜ ⊆ A`, isto é, `¬¬(x ∈ A) → x ∈ A` (eliminação da dupla negação). A
-- outra, `A ⊆ Aᶜᶜ`, ou seja `x ∈ A → ¬¬(x ∈ A)`, é construtiva: dados
-- `hx : x ∈ A` e `hnx : x ∈ Aᶜ`, basta aplicar `hnx hx` para obter `False`. A
-- razão é que, na leitura construtiva, `¬ P` é `P → False`; de uma função que
-- transforma "refutações de `P`" em absurdo não se extrai, por meios
-- construtivos, uma *prova* de `P`. Passar de `¬¬P` para `P` é exatamente o
-- conteúdo do terceiro excluído.

example : Aᶜᶜ = A := sorry

end

-- #### Calcular ou enunciar

-- `α → Prop` enuncia a pertinência. Existe também `α → Bool`, que a calcula,
-- e é o que se usa quando o conjunto é finito e a resposta tem que ser
-- computada — é o caso da verificação de modelos, no fim do livro, onde
-- decidir se uma sentença vale num modelo é percorrer um domínio finito.

-- Ser par, na versão que se calcula.

def isEven (n : Nat) : Bool := n % 2 == 0

#eval isEven 4

-- true

#eval isEven 5

-- false

-- A versão que se enuncia já existe na biblioteca: `Even n` afirma que `n` é
-- o dobro de algum número, sem dizer como encontrá-lo. Aqui está a distinção
-- em ato. `isEven` é um algoritmo — divide e compara o resto. `Even` é uma
-- condição de verdade — existe um `r` tal que `n = r + r`. São conteúdos
-- diferentes, e por isso vale a pena que sejam objetos diferentes.

#print Even

-- def Even.{u_2} : {α : Type u_2} → [Add α] → α → Prop :=
-- fun {α} [Add α] a => ∃ r, a = r + r

-- Provar `Even 4` é exibir o `r` que a afirmação promete, junto com a
-- verificação de que ele serve.

example : Even 4 := by
  unfold Even
  apply Exists.intro 2   -- alternative `use`
  rfl

-- Nada obriga, a priori, uma afirmação e um algoritmo a dizerem a mesma
-- coisa. Que estes dois digam é um fato sobre os naturais, Mathlib já traz a
-- prova, sob o nome `Nat.even_iff`:

example (n : Nat) : Even n ↔ n % 2 = 0 := Nat.even_iff

-- Provado isso, `Even n` passa a ser uma afirmação que se pode calcular para
-- um `n` dado — e o Lean faz isso sem que se peça nada:

#eval Even 4

-- true

-- Vale reparar no que acabou de acontecer. `Even 4` é uma afirmação, não um
-- programa; ainda assim o `#eval` respondeu `true`. Há um mecanismo por trás
-- disso, que registra quais afirmações admitem esse cálculo e como fazê-lo —
-- e ele é uma classe de tipos, como o `BEq` e o `DecidableEq` de Programação
-- Funcional no Lean. A classe se chama `Decidable`.

-- ## Relações

-- Um conjunto representa a função que responde se um elemento pertence. Uma
-- relação binária faz o mesmo com *pares*: é a função que, dados dois
-- elementos, responde se estão na relação. Em Lean isso não é analogia
-- nenhuma — é a definição:

#print Rel

-- @[reducible] def Rel.{u_6, u_7} : Type u_6 → Type u_7 → Type (max u_6 u_7) :=
-- fun α β => α → β → Prop

-- `Rel α β` é `α → β → Prop`. É a primeira vez neste capítulo que o domínio
-- deixa de ser um tipo qualquer e passa a ter conteúdo linguístico: um
-- domínio de duas entidades, e a relação de gostar entre elas.

-- O domínio de entidades. Duas bastam para os exemplos deste capítulo.

inductive Entity where
  | dorothy | toto
deriving DecidableEq

def likesR : Entity → Entity → Prop
  | .dorothy, .toto => True
  | .toto, .dorothy => True
  | _, _            => False

#check (likesR : Rel Entity Entity)

-- likesR : Entity → Entity → Prop

-- ### Inversa

-- A inversa de uma relação troca a ordem dos argumentos, e é `flip` quem faz
-- isso. Em língua, é o que a voz passiva faz: *Dorothy likes Toto* e *Toto is
-- liked by Dorothy* descrevem o mesmo par, em ordens opostas.

#check (flip likesR)

-- flip likesR : Entity → Entity → Prop

example :
    flip likesR .toto .dorothy =
      likesR .dorothy .toto := rfl

-- ### Composição

-- Compor duas relações é encadeá-las por um elemento intermediário: `R`
-- composta com `S` relaciona `x` a `z` quando existe um `y` com `x R y` e
-- `y S z`. É `Relation.Comp`, e provar uma composição é exibir esse
-- intermediário.

-- Composição é o que define parentesco em cadeia: "avô" é "pai" composto com
-- "pai". Aqui, quem gosta de quem gosta de quem:

example : Relation.Comp likesR likesR .dorothy .dorothy :=
  ⟨.toto, trivial, trivial⟩

-- ### Propriedades

-- Reflexividade, simetria e transitividade se enunciam com quantificador e
-- conectivo, e são afirmações sobre a relação inteira — não sobre um par.

def Reflexive' (R : α → α → Prop) : Prop := ∀ x, R x x
def Symmetric' (R : α → α → Prop) : Prop :=
  ∀ x y, R x y → R y x
def Transitive' (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z

-- `likesR` é simétrica, e a prova percorre os casos: `decide` não serve,
-- porque `Prop` aqui não é decidível de graça, mas o casamento de padrão
-- resolve.

example : Symmetric' likesR := by
  intro x y h
  cases x <;> cases y <;> simp_all [likesR]

-- As três juntas dão uma *relação de equivalência*, e a biblioteca tem o nome
-- pronto: `Equivalence`. A igualdade é o exemplo canônico.

#check @Equivalence

-- @Equivalence : {α : Sort u_1} → (α → α → Prop) → Prop

example :
    Equivalence (· = · : Entity → Entity → Prop) :=
  eq_equivalence

-- ### Calcular ou enunciar, outra vez

-- Vale a mesma escolha da seção de conjuntos. A divisibilidade vem na
-- biblioteca na versão que enuncia — `m ∣ n` afirma que existe um fator que
-- leva de `m` a `n`, e provar é exibi-lo — e ainda assim se calcula, porque a
-- instância `Decidable` existe:

example : (3 : Nat) ∣ 12 := ⟨4, rfl⟩

#eval (3 ∣ 12 : Prop)

-- true

#eval (5 ∣ 12 : Prop)

-- false

example : ∀ n : Nat, n ∣ n := fun _ => Nat.dvd_refl _

-- Relação é a estrutura que a verificação de modelos vai usar para dar modelo
-- a um fragmento — um domínio de entidades e, para cada verbo, a relação que
-- ele denota — e à qual o tratamento de verbos de mais de dois lugares, e do
-- escopo entre eles, volta mais tarde.

-- ### Exercise (2 stars): cartesian-square ⭐⭐

-- Tome `A` como o conjunto `{Kasparov, Karpov, Anand}`. Encontre `A × A`.

-- Como `A` é finito, o produto cartesiano é finito e a Mathlib o calcula:
-- `Finset` é o tipo dos conjuntos finitos, `Fintype α` é a evidência de que
-- `α` tem finitos elementos (e dá `Finset.univ`, o conjunto de todos eles), e
-- `s ×ˢ t` é o produto cartesiano de dois `Finset`. Construa `A ×
-- A` e prove
-- que tem nove elementos.

-- A evidência de que `Player` é finito: a lista dos seus elementos, mais a
-- prova de que não falta ninguém. (O normal seria `deriving Fintype`, mas o
-- gerador automático está quebrado nesta versão da Mathlib — então a
-- instância vai à mão, o que também mostra o que um `Fintype` é.)

inductive Player where
  | kasparov | karpov | anand
deriving Repr, DecidableEq

instance : Fintype Player :=
  ⟨{.kasparov, .karpov, .anand},
   fun x => by cases x <;> decide⟩

def playerPairs : Finset (Player × Player) :=
  sorry

theorem playerPairs_test : playerPairs.card = 9 :=
  sorry

-- ### Exercise (2 stars): successor-composition ⭐⭐

-- Qual é a composição de `{(n, n + 2) | n ∈ ℕ}` com ela mesma?

-- Enuncie a resposta e prove.

def plusTwo : Rel Nat Nat := fun a b => b = a + 2

theorem plusTwo_test (a c : Nat) :
    Relation.Comp plusTwo plusTwo a c ↔ c = a + 4 :=
    sorry

-- ### Exercise (2 stars): converse-subset ⭐⭐

-- Mostre que de `R˘ ⊆ R` segue que `R = R˘`.

-- A Mathlib tem `Std.Symm.flip_eq : flip r = r` para relações simétricas.
-- Usá-lo é permitido — mas então o trabalho é seu de construir a instância
-- `Std.Symm R` a partir de `h`, que é o mesmo argumento. A prova direta é
-- mais curta.

theorem flip_eq_test {α : Type} (R : Rel α α)
    (h : flip R ≤ R) : R = flip R := sorry

-- ### Exercise (2 stars): which-are-transitive ⭐⭐

-- Quais das relações seguintes são transitivas?

-- 1. `{(1,2), (2,3), (3,4)}`
-- 2. `{(1,2), (2,3), (3,4), (1,3), (2,4)}`
-- 3. `{(1,2), (2,3), (3,4), (1,3), (2,4), (1,4)}`
-- 4. `{(1,2), (2,1)}`
-- 5. `{(1,1), (2,2)}`

-- Estas relações são finitas, e por isso podem ser dadas como o `Finset` dos
-- seus pares — e aí a transitividade *se decide*: escreva-a como uma
-- proposição sobre os pares do `Finset` e o `decide` calcula a resposta.

-- Complete `isTransitive` e depois decida os cinco casos. É `abbrev`, e não
-- `def`, para que a instância `Decidable` seja encontrada através da
-- definição — trocar por `def` faz o `decide` falhar com
-- `failed to
-- synthesize Decidable (isTransitive r3)`, porque a busca de
-- instâncias não desdobra um `def`.

abbrev isTransitive (r : Finset (Nat × Nat)) : Prop :=
  sorry

def r1 : Finset (Nat × Nat) := {(1,2), (2,3), (3,4)}
def r2 : Finset (Nat × Nat) :=
  {(1,2), (2,3), (3,4), (1,3), (2,4)}
def r3 : Finset (Nat × Nat) :=
  {(1,2), (2,3), (3,4), (1,3), (2,4), (1,4)}
def r4 : Finset (Nat × Nat) := {(1,2), (2,1)}
def r5 : Finset (Nat × Nat) := {(1,1), (2,2)}

theorem r1_test : ¬ isTransitive r1 := sorry
theorem r2_test : ¬ isTransitive r2 := sorry
theorem r3_test :   isTransitive r3 := sorry
theorem r4_test : ¬ isTransitive r4 := sorry
theorem r5_test :   isTransitive r5 := sorry

-- ### Exercise (2 stars): transitive-iff-comp ⭐⭐

-- Verifique que uma relação `R` é transitiva se e somente se `R ∘ R ⊆ R`.

-- **Não vale usar `SetRel.isTrans_iff_comp_subset_self`**, que é este
-- enunciado na versão "relação como conjunto de pares" (vale abrir
-- `Mathlib/Data/Rel.lean` e ver: o exercício aparece lá provado, com esse
-- nome). Prove as duas direções.

theorem isTrans_iff_test {α : Type} (R : Rel α α) :
    IsTrans α R ↔ Relation.Comp R R ≤ R := sorry

-- ### Exercise (2 stars): transitive-not-idempotent ⭐⭐

-- Você pode dar um exemplo de relação transitiva `R` para a qual `R ∘ R =
-- R`
-- não vale?

-- Exiba a testemunha completando `counterexample` e prove as duas coisas: que
-- ela é transitiva, e que a composição com ela mesma não lhe é igual.

def counterexample : Rel Nat Nat :=
  sorry

theorem counterexample_trans : IsTrans Nat counterexample :=
  sorry

theorem counterexample_different :
    Relation.Comp counterexample counterexample ≠
      counterexample :=
  sorry

-- ## Funções

-- Funções já apareceram — o capítulo sobre Lean as apresentou como tipo
-- primitivo, `α → β`. O que se acrescenta aqui é a ligação com as relações:
-- uma função é uma relação com uma restrição. Para cada `a`, no máximo um `b`
-- está relacionado a ele. `Rel α β`, do jeito que ficou definido acima, não
-- impõe isso — `likesR` bem poderia relacionar `dorothy` a duas entidades
-- diferentes. Uma função é o caso particular em que a resposta é única, e é
-- justamente essa unicidade que permite escrever `f x` em vez de "algum `b`
-- tal que `(x, b) ∈ f`".

-- ### Função característica

-- Toda relação, vista como conjunto de pares, tem uma função característica:
-- a função que decide se um par está nela. Reaproveitando `likesR` de acima —
-- que já é a própria função característica da relação de gostar, escrita como
-- `Entity → Entity → Prop`: dados `x` e `y`, `likesR x y` é a afirmação "x
-- gosta de y", nem mais nem menos. Isto prepara a leitura da seção seguinte:
-- conjunto e relação **são** funções para `Prop` (ou `Bool`), não apenas
-- "correspondem" a elas.

-- ### Exercise (1 star): successor-as-relation ⭐

-- A função sucessor `s : ℕ → ℕ` é dada por `n ↦ n + 1`. Qual é a composição
-- de `s` com ela mesma?

-- `∘` é `Function.comp`, e duas funções são iguais quando concordam em todo
-- ponto — é o que `funext` diz.

def s : Nat → Nat := fun n => n + 1

theorem s_comp_test : s ∘ s = fun n => n + 2 := sorry

-- ### Exercise (1 star): leq-as-function ⭐

-- `≤` é uma relação binária sobre os naturais. Qual é a função característica
-- correspondente?

-- Escreva a função e prove que ela é adequada — que responde `true`
-- exatamente quando a relação vale.

-- Aqui `Prop` e `Bool` se encontram: `m ≤ n` é uma proposição, `leChar m
-- n` é
-- um cálculo. A ponte é `decide`, e os lemas que a atravessam são
-- `decide_eq_true_iff`, `of_decide_eq_true` e `decide_eq_true`.

def leChar : Nat → Nat → Bool :=
  sorry

theorem leChar_test (m n : Nat) :
    leChar m n = true ↔ m ≤ n := sorry

-- ### Exercise (2 stars): graph-is-functional ⭐⭐

-- Seja `f : A → B` uma função. Mostre que a relação `R` dada por `(x, y) ∈
-- R`
-- se e somente se `f x = f y` é uma relação de equivalência sobre `A`.

-- `Equivalence R` é a estrutura com os três campos `refl`, `symm` e `trans`;
-- `Setoid α` é a mesma coisa empacotada com a relação, e é o que a Mathlib
-- usa para quocientes.

-- **Não vale usar `Setoid.ker`**: é exatamente esta relação, já construída na
-- Mathlib com a prova de que é de equivalência. Prove os três campos.

def kernel {α β : Type} (f : α → β) : Rel α α :=
  fun x y => f x = f y

theorem ex_3_12 {α β : Type} (f : α → β) :
    Equivalence (kernel f) :=
  sorry

-- O mesmo fato, empacotado: um `Setoid` é uma relação mais a prova de que ela
-- é de equivalência. Reaproveite `ex_3_12`.

def kernelSetoid {α β : Type} (f : α → β) : Setoid α :=
  sorry

end Sets

