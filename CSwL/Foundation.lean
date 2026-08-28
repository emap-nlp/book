import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic

-- # Conjuntos e Relações, Lambda Calculus e Tipos

-- Ref. CSwFP/2. Lambda Calculus, Type Theory, and Functional Programming. No
-- CSwFP é prosa sem código; aqui formalizamos o possível em Lean.

namespace Foundation

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

-- Foundation.S1 : Set ℕ

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

-- ### Exercise (1 star): a1-pertence-above2 ⭐

-- **A1.** Prove que 5 pertence a `above2`.

example : 5 ∈ above2 := sorry

-- ### Exercise (1 star): a2-nao-pertence-above2 ⭐

-- **A2.** Prove que 1 não pertence a `above2`. `x ∉ A` abrevia `¬ (x ∈ A)`,
-- que por sua vez é `x ∈ A → False`.

example : 1 ∉ above2 := sorry

-- ### Exercise (1 star): a3-above5-subset-above2 ⭐

-- **A3.** Prove a inclusão. `unfold above2 above5` desdobra as duas
-- definições; `simp only [Set.mem_ofPred_eq] at h` desdobra a pertinência em
-- `h` até a desigualdade, que `omega` então resolve.

example : above5 ⊆ above2 := sorry

-- União e interseção são disjunção e conjunção elemento a elemento. As duas
-- inclusões abaixo valem para conjuntos quaisquer, e as provas não precisam
-- saber nada sobre eles.

-- ### Exercise (1 star): a4-uniao ⭐

-- **A4.** Todo conjunto está contido na sua união com outro. Depois do
-- `intro`, `Or.inl` prova uma disjunção pelo lado esquerdo.

example (A B : Set Nat) : A ⊆ A ∪ B := sorry

-- ### Exercise (1 star): a5-intersecao ⭐

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

-- ### Exercise (1 star): 3.1 ⭐

-- Ref. CSwFP/2, exercício 3.1 (p. 17).

-- Explique por que `∅ ⊆ A` vale para todo conjunto `A`. Prove-o. O argumento
-- é vacuoso, e a prova deve exibir isso.

-- **Não vale usar `Set.empty_subset`** (nem `simp`, que o encontra): esse
-- lema é exatamente o enunciado, e citá-lo apagaria o exercício.

example : ∅ ⊆ A := sorry

-- ### Exercise (1 star): 3.2 ⭐

-- Ref. CSwFP/2, exercício 3.2 (p. 17). ✎

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

-- ### Exercise (2 stars): 3.3 ⭐⭐

-- Ref. CSwFP/2, exercício 3.3 (p. 17). ✎

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
-- computada — é o caso do capítulo 6, onde verificar uma sentença num modelo
-- é percorrer um domínio finito.

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
-- e ele é uma classe de tipos, como o `BEq` e o `DecidableEq` do capítulo 2.
-- A classe se chama `Decidable`.

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

-- Relação é a estrutura que o capítulo 6 vai usar para dar modelo a um
-- fragmento — um domínio de entidades e, para cada verbo, a relação que ele
-- denota —, e o capítulo 10 volta a ela para tratar verbos de mais de dois
-- lugares e o escopo entre eles.

-- ### Exercise (2 stars): 3.4 ⭐⭐

-- Ref. CSwFP/2, exercício 3.4 (p. 18).

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

-- ### Exercise (2 stars): 3.5 ⭐⭐

-- Ref. CSwFP/2, exercício 3.5 (p. 18).

-- Qual é a composição de `{(n, n + 2) | n ∈ ℕ}` com ela mesma?

-- Enuncie a resposta e prove.

def plusTwo : Rel Nat Nat := fun a b => b = a + 2

theorem plusTwo_test (a c : Nat) :
    Relation.Comp plusTwo plusTwo a c ↔ c = a + 4 :=
    sorry

-- ### Exercise (2 stars): 3.6 ⭐⭐

-- Ref. CSwFP/2, exercício 3.6 (p. 18).

-- Mostre que de `R˘ ⊆ R` segue que `R = R˘`.

-- A Mathlib tem `Std.Symm.flip_eq : flip r = r` para relações simétricas.
-- Usá-lo é permitido — mas então o trabalho é seu de construir a instância
-- `Std.Symm R` a partir de `h`, que é o mesmo argumento. A prova direta é
-- mais curta.

theorem flip_eq_test {α : Type} (R : Rel α α)
    (h : flip R ≤ R) : R = flip R := sorry

-- ### Exercise (2 stars): 3.7 ⭐⭐

-- Ref. CSwFP/2, exercício 3.7 (p. 19).

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

-- ### Exercise (2 stars): 3.8 ⭐⭐

-- Ref. CSwFP/2, exercício 3.8 (p. 19).

-- Verifique que uma relação `R` é transitiva se e somente se `R ∘ R ⊆ R`.

-- **Não vale usar `SetRel.isTrans_iff_comp_subset_self`**, que é este
-- enunciado na versão "relação como conjunto de pares" (vale abrir
-- `Mathlib/Data/Rel.lean` e ver: o exercício aparece lá provado, com esse
-- nome). Prove as duas direções.

theorem isTrans_iff_test {α : Type} (R : Rel α α) :
    IsTrans α R ↔ Relation.Comp R R ≤ R := sorry

-- ### Exercise (2 stars): 3.9 ⭐⭐

-- Ref. CSwFP/2, exercício 3.9 (p. 19).

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

-- Uma função é uma relação com uma restrição: para cada `a`, no máximo um `b`
-- está relacionado a ele. `Rel α β`, do jeito que ficou definido acima, não
-- impõe isso — `likesR` bem poderia relacionar `dorothy` a duas entidades
-- diferentes. Uma função é o caso particular em que a resposta é única, e é
-- justamente essa unicidade que permite escrever `f x` em vez de "algum `b`
-- tal que `(x, b) ∈ f`".

-- Uma função admite duas leituras, e as duas importam:

-- - **extensional** — a função como tabela: o conjunto de pares entrada/saída.
--   Uma conversão de Celsius para Fahrenheit é a tabela
--   `{(0, 32), (100, 212), …}`, ponto.

-- - **intensional** — a função como instrução de cálculo. A mesma conversão é
--   `x ↦ x * 9 / 5 + 32`, uma receita que produz a tabela sem precisar
--   listá-la.

-- Em Lean, `def` escreve sempre a versão intensional — a instrução —, mas
-- duas instruções diferentes podem ser a mesma função, no sentido
-- extensional, se produzem a mesma tabela. É isso que `funext` verifica: duas
-- funções são iguais quando concordam em todo ponto do domínio.

def celsiusToFahrenheit (c : Int) : Int := c * 9 / 5 + 32

#eval celsiusToFahrenheit 0

-- 32

#eval celsiusToFahrenheit 100

-- 212

-- ### Composição

-- Componhamos duas conversões: de Kelvin para Celsius, depois de Celsius para
-- Fahrenheit. `∘` é `Function.comp`, e `(f ∘ g) x = f (g x)` — primeiro `g`,
-- depois `f`, na ordem em que a leitura da notação sugere o contrário.

def kelvinToCelsius (k : Int) : Int := k - 273

def kelvinToFahrenheit : Int → Int :=
  celsiusToFahrenheit ∘ kelvinToCelsius

#eval kelvinToFahrenheit 373

-- 212

-- ### Função característica

-- Toda relação, vista como conjunto de pares, tem uma função característica:
-- a função que decide se um par está nela. Reaproveitando `likesR` de acima —
-- que já é a própria função característica da relação de gostar, escrita como
-- `Entity → Entity → Prop`: dados `x` e `y`, `likesR x y` é a afirmação "x
-- gosta de y", nem mais nem menos. Isto prepara a leitura da seção seguinte:
-- conjunto e relação **são** funções para `Prop` (ou `Bool`), não apenas
-- "correspondem" a elas.

-- ### Exercise (1 star): 3.10 ⭐

-- Ref. CSwFP/2, exercício 3.10 (p. 21).

-- A função sucessor `s : ℕ → ℕ` é dada por `n ↦ n + 1`. Qual é a composição
-- de `s` com ela mesma?

-- `∘` é `Function.comp`, e duas funções são iguais quando concordam em todo
-- ponto — é o que `funext` diz.

def s : Nat → Nat := fun n => n + 1

theorem s_comp_test : s ∘ s = fun n => n + 2 := sorry

-- ### Exercise (1 star): 3.11 ⭐

-- Ref. CSwFP/2, exercício 3.11 (p. 21).

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

-- ### Exercise (2 stars): 3.12 ⭐⭐

-- Ref. CSwFP/2, exercício 3.12 (p. 21).

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

-- ## Cálculo lambda

-- A notação `fun x => e` não é invenção de linguagem de programação. Ela
-- resolve uma ambiguidade real, e vale ver qual.

-- A expressão `x² + y` não determina uma função. Ela pode ser lida como
-- função de `x`, com `y` fixo; como função de `y`, com `x` fixo; ou como
-- função dos dois. O que falta é dizer qual variável é o parâmetro — e o
-- operador lambda é exatamente o marcador que diz isso. Em `λx ↦ x² + y`, o
-- `x` está **ligado** e o `y` está **livre**.

-- O nome da variável ligada não importa: `λz ↦ z² + y` é a mesma função. E
-- isso não é convenção — em Lean as duas são o mesmo termo, e o `rfl` prova:

example :
    (fun (x : Nat) => x * x) =
      (fun (z : Nat) => z * z) := rfl

-- ### A gramática dos termos

-- O cálculo lambda tem três formas de construir expressão, e nada mais.
-- Escritas na notação usual para gramáticas — a Forma de Backus-Naur, ou BNF:

-- E ::= v | (E E) | (λv ↦ E)

-- Leia: uma expressão é uma variável, ou a justaposição de duas expressões
-- (aplicação), ou um lambda seguido de variável e expressão (abstração). A
-- última cláusula é implícita e importante: **nada além disso é expressão**.

-- Aqui está o ponto. Uma gramática BNF é uma definição indutiva, e uma
-- definição indutiva é um tipo `inductive` — o mesmo mecanismo que no
-- capítulo 2 declarou as classes de declinação do sueco e os traços
-- fonológicos. As duas coisas são a mesma, escritas em notações diferentes:

-- A gramática acima, como tipo. Cada cláusula da BNF virou um construtor.

inductive Lam where
  | var (name : String)
  | app (fn arg : Lam)
  | lam (binder : String) (body : Lam)

-- Essa correspondência é o motor do curso. Do capítulo 4 em diante, cada
-- fragmento da língua vai ser dado por uma gramática, e a gramática vai ser
-- um tipo `inductive` — o que torna "esta expressão é bem formada" a mesma
-- coisa que "este termo tem esse tipo".

-- Aqui, `Lam` fica como ilustração e não será usado: o cálculo lambda que
-- interessa é o próprio Lean, não uma cópia dele dentro de Lean.

-- ### Redução

-- O que se faz com uma aplicação é substituir. A regra é uma só:

-- (λx ↦ E) A  →  E\[x := A\]

-- onde `E\[x := A\]` é `E` com toda ocorrência livre de `x` trocada por `A`.
-- Isso é a β-redução, e é o único mecanismo de cálculo do cálculo lambda
-- inteiro.

-- Em Lean essa redução é o que o `#eval` executa e o que o `rfl` verifica:

example : (fun (x : Nat) => x + 42) 5 = 5 + 42 := rfl

-- ### Captura de variável

-- Substituir ingenuamente dá errado, e o exemplo clássico merece atenção
-- porque o erro é silencioso. Considere aplicar `λyλx ↦ x + y` ao argumento
-- `x`.

-- Trocando `y` por `x` sem cuidado, obtém-se `λx ↦ x + x` — a função que soma
-- um número a si mesmo. Mas o resultado correto é a função que soma `x` a um
-- número dado: o `x` que veio de fora foi **capturado** pelo `λx` que já
-- estava lá. Que o resultado é outro se vê renomeando antes: `λyλz
-- ↦ z + y`
-- aplicado a `x` dá `λz ↦ z + x`, que é o certo.

-- A saída é renomear a variável ligada quando houver risco de captura. Lean
-- faz isso sozinho — internamente as variáveis ligadas não têm nome, e o
-- problema não existe:

example (x : Nat) :
    (fun y => fun z => z + y) x = (fun z => z + x) := rfl

-- ### Funções são dados

-- Abstração e aplicação, como definidas, não distinguem dados de funções. Se
-- tudo é expressão, então uma função pode receber função, devolver função, e
-- ser aplicada a si mesma. Não há duas categorias de coisas.

-- É isso que permite escrever uma função que aplica outra a um argumento
-- fixo:

def applyToDragon (f : String → String) : String :=
  f "dragon"

def pluralize (w : String) : String := w ++ "s"

#eval applyToDragon pluralize

-- "dragons"

-- ### Por que isso serve à semântica

-- Um verbo transitivo é uma função de dois lugares. *Likes* se escreve
-- `λxλy ↦ y likes x`, onde `likes` é a função característica da relação de
-- gostar — a mesma `likesR` da seção de relações, só que agora vista como
-- instrução curried em vez de par de argumentos.

-- Aqui a aplicação parcial do capítulo 2 deixa de ser conveniência de
-- programação e passa a ter conteúdo linguístico. `add 3` era uma função à
-- espera do segundo número; do mesmo modo, o verbo aplicado ao seu objeto é
-- uma expressão à espera do sujeito — que é precisamente o que se chama de
-- sintagma verbal. A currificação não modela o VP por acaso: ela é o VP.

-- Repare no que a notação **não** diz. Ela não diz o que *likes* significa no
-- mundo. Diz apenas com que outras expressões o verbo se combina e que papel
-- desempenha na expressão maior — e é justamente por dizer só isso que o
-- cálculo lambda serve à semântica composicional. A derivação do significado
-- pode então acompanhar, passo a passo, a estrutura sintática da sentença.

-- ### Exercise (1 star): 3.13 ⭐

-- Ref. CSwFP/2, exercício 3.13 (p. 26).

-- Outro exemplo de função de ordem superior é `λf λx ↦ f (f x)`, que aplica
-- uma função duas vezes a uma entrada dada. Ponha-a para trabalhar reduzindo:
-- `(λf λx ↦ f (f x)) (λy ↦ 1 + y)`.

def twice {α : Type} (f : α → α) : α → α :=
  sorry

theorem twice_test1 :
    twice (fun y => 1 + y) = fun x => 2 + x := sorry

theorem twice_test2 : twice (fun y => 1 + y) 0 = 2 :=
  sorry

-- Ref. CSwFP/2, exercício 3.14 (p. 26–27). ✎

-- Um aspecto do cálculo lambda é que reduções podem não terminar. Observe o
-- comportamento de redução de `(λx ↦ x x) (λx ↦ x x)`, e depois de
-- `(λx
-- ↦ x x x) (λx ↦ x x x)`.

-- Este exercício não se enuncia em Lean, e a razão é o assunto da questão:

-- **1. Um passo de redução.** Substituindo `x` por `(λx ↦ x x)` no corpo
-- `x x`, obtém-se `(λx ↦ x x) (λx ↦ x x)` — o mesmo termo de partida. A
-- redução é portanto um laço: qualquer número de passos devolve o termo
-- original, e a normalização nunca termina. Este termo é o combinador
-- tradicionalmente chamado `Ω`. Já `(λx ↦ x x x) (λx ↦ x x x)` reduz a
-- `(λx ↦ x x x) (λx ↦ x x x) (λx ↦ x x x)`: além de não terminar, cada passo
-- produz um termo *maior* que o anterior, então nem mesmo o tamanho fica
-- estável.

-- **2. A mensagem do Lean.** Descomentando
-- `def omega := (fun x => x x)
-- (fun x => x x)` abaixo, o Lean acusa dois
-- erros: a auto-aplicação `x x` exige que `x` seja função de algum tipo
-- `?m → ?n`, mas o argumento é o próprio `x`, que teria então de ter
-- simultaneamente o tipo `?m`. O elaborador precisa resolver `?m = ?m → ?n`,
-- e não existe tipo que satisfaça isso (falha o *occurs check*: `?m`
-- ocorreria dentro de si mesmo). Como não há atribuição de tipos possível, o
-- termo não pode nem ser *escrito* em Lean.

-- **3. Relação entre não terminar e não ter tipo.** O cálculo lambda *tipado*
-- (simplesmente tipado, e também o de Lean) é fortemente normalizante: todo
-- termo bem tipado tem forma normal, e a redução sempre termina. A
-- contrapositiva é o que se observa aqui: um termo cuja redução não termina
-- não pode ser bem tipado. Os dois fenômenos têm a mesma raiz — a
-- auto-aplicação `x x` — e o sistema de tipos funciona como um filtro que
-- rejeita exatamente esses termos. É por isso que Lean pode ser ao mesmo
-- tempo uma linguagem de programação e uma lógica consistente: a terminação é
-- garantida pelos tipos, não pela boa vontade do programador. (O preço é que
-- Lean também rejeita programas que terminam, mas cuja terminação ele não
-- sabe verificar; daí a necessidade de provar terminação em definições
-- recursivas.)

-- -- def omega := (fun x => x x) (fun x => x x)

-- ## Tipos na gramática e na computação

-- No cálculo lambda como está, toda expressão se aplica a toda expressão.
-- Nada impede escrever o número `4` aplicado a uma função, e o resultado não
-- é falso — é sem sentido. Tipos existem para excluir isso.

-- A gramática dos tipos também é uma BNF, com duas cláusulas:

-- τ ::= b | (τ → τ)

-- Há tipos básicos, e há tipos de função construídos a partir deles. Na
-- semântica, os dois básicos costumam ser `e`, das entidades, e `t`, dos
-- valores de verdade. Em Lean, `t` é `Prop`.

-- E a atribuição de tipos a expressões se dá por três regras:

-- - **variáveis** — para cada tipo há variáveis daquele tipo;
-- - **abstração** — se `x : δ` e `E : τ`, então `(λx ↦ E) : δ → τ`;
-- - **aplicação** — se `E₁ : δ → τ` e `E₂ : δ`, então `(E₁ E₂) : τ`.

-- Não há mais nada. O `#check` do Lean é essas três regras rodando:

-- `happy` é uma propriedade de entidades: aplicada a uma, dá uma afirmação.
-- `opaque` declara o nome com o tipo e sem corpo — aqui o assunto são os
-- tipos, e qualquer definição serviria.

opaque happy : Entity → Prop

section
variable (x : Entity)

-- regra da aplicação: `happy : Entity → Prop` e `x : Entity`, logo
-- `happy
-- x : Prop`

#check happy x

-- happy x : Prop

-- regra da abstração: `x : Entity` e `happy x : Prop`, logo o lambda é
-- `Entity → Prop`

#check fun (y : Entity) => happy y

-- fun y => happy y : Entity → Prop

end

-- Tipos, em programação e no cálculo lambda, se comportam como **categorias
-- sintáticas** em gramática — e essa observação amarra as duas metades do
-- argumento acima.

-- Categorias como NP correspondem a tipos básicos: expressões completas, que
-- carregam significado por si. Categorias como VP correspondem a tipos de
-- função: expressões incompletas, cujo significado consiste na contribuição
-- que dão à expressão em que aparecem.

-- Sob essa leitura, uma regra de reescrita como `S → NP VP` diz uma coisa
-- sobre tipos: se `a : NP` e `b : VP`, então a concatenação de `a` e `b` é um
-- `S`. E se o VP é o que combina com um NP para dar um S, então o próprio VP
-- tem tipo `NP → S` — a categoria deixa de ser um rótulo e passa a ser uma
-- função.

-- Essa é a ideia da **gramática categorial**, que vem de Ajdukiewicz. Um
-- verbo transitivo, que combina com dois NPs, tem tipo `NP → (NP → S)` — e é
-- justamente o tipo de `likesR`, `Entity → Entity → Prop`, lido com
-- `NP := Entity` e `S := Prop`. A relação binária da seção anterior já era,
-- sem que se precisasse dizer, um verbo transitivo em potencial: **o verbo
-- transitivo denota uma relação binária, e o tipo de `likesR` já dizia
-- isso.**

-- A regra de combinação é uma só: uma expressão de categoria `A` combina com
-- uma de categoria `A → B` e produz uma de categoria `B` — isto é, aplicação.
-- Em Lean isso se escreve diretamente, e o verificador de tipos passa a
-- validar a derivação:

abbrev NP := Entity
abbrev S := Prop
abbrev VP := NP → S
abbrev TV := NP → VP

def dorothy : NP := .dorothy
def toto : NP := .toto

-- O verbo, como função de dois lugares: recebe o objeto, depois o sujeito.

opaque likes : TV

-- O VP: o verbo já recebeu o objeto e espera o sujeito.

def likesToto : VP := likes toto

-- E a sentença, com o sujeito no lugar.

def dorothyLikesToto : S := likesToto dorothy

#check dorothyLikesToto

-- Foundation.dorothyLikesToto : S

-- A derivação da sentença é uma sequência de duas aplicações, e cada passo é
-- conferido pelos tipos. Uma combinação mal formada não chega a ser um termo.

-- ### Lean como cálculo lambda

-- O que se descreveu acima é o cálculo lambda com tipos simples, e Lean o
-- contém. Abstração, aplicação, β-redução, tipos de função: tudo o que foi
-- dito vale literalmente, e os `#check` acima são as regras de tipagem sendo
-- aplicadas.

-- Lean vai além disso em pontos que o curso vai usar:

-- - **tipos indutivos** — os do capítulo 2, que aqui se revelam ser gramáticas:
--   uma BNF é um tipo, com casamento de padrão e recursão garantidamente
--   terminante;

-- - **tipos dependentes** — um tipo pode depender de um valor, o que permite
--   exigir na assinatura condições que aqui teriam de ser verificadas à parte;

-- - **proposições como tipos** — `Prop` não é um tipo básico opaco: uma prova
--   de `P` é um termo de tipo `P`, e é por isso que o mesmo verificador serve
--   para checar programas e demonstrações;

-- - **universos** — `Type`, `Type 1`, e assim por diante, o que evita os
--   paradoxos que apareceriam se houvesse um tipo de todos os tipos.

-- Para o que vem pela frente, a leitura útil é essa: o aparato da semântica
-- de Montague é um fragmento do que Lean oferece, e o excedente é o que vai
-- permitir demonstrar coisas sobre os significados, e não apenas calculá-los.

-- Ref. CSwFP/2, exercício 3.15 (p. 28). ✎

-- Atribua tipos às expressões lambda do exemplo (2.6) da página 27:

-- S  = Dorothy likes Toto
-- NP = Dorothy
-- VP = λy ↦ y likes Toto
-- V  = λx λy ↦ y likes x
-- NP = Toto

-- Com os dois tipos básicos já em uso acima, `NP := Entity` e `S := Prop` (o
-- `e`/`t` da semântica de Montague):

-- - S — `Dorothy likes Toto` — tipo `S` (= `t`)
-- - NP — `Dorothy` — tipo `NP` (= `e`)
-- - VP — `λy ↦ y likes Toto` — tipo `NP → S`
-- - V — `λx λy ↦ y likes x` — tipo `NP → (NP → S)`
-- - NP — `Toto` — tipo `NP` (= `e`)

-- A operação que leva do tipo de `V` ao tipo de `VP` é a **aplicação de
-- função**: aplicar `likes : NP → (NP → S)` ao objeto `toto : NP` satura o
-- primeiro argumento e devolve `NP → S`, que é o tipo de `VP` — é exatamente
-- `likesToto` acima. O mesmo passo, aplicado outra vez com o sujeito
-- `dorothy : NP`, leva até `S` — é `dorothyLikesToto`. Em suma, a árvore
-- sintática é lida como uma cadeia de aplicações, e cada combinação de nós
-- consome um argumento; a frase completa é o ponto em que não falta mais
-- nada, e é por isso que seu tipo é `S` e não uma função.

-- Observação sobre convenção: como o léxico escreve `V = λx λy ↦ y likes
-- x`,
-- o *objeto* é o primeiro argumento e o *sujeito* o segundo — é o que
-- `likesToto := likes toto` e `dorothyLikesToto := likesToto dorothy` acima
-- já fazem, na ordem certa.

-- Ref. CSwFP/2, exercício 3.16 (p. 28). ✎

-- E o termo `(λx ↦ x x) (λx ↦ x x)` do exercício anterior? Você consegue
-- achar um tipo para ele?

-- **Não.** Nenhuma atribuição de tipos funciona, e a maneira de mostrar isso
-- é tentar construí-la e ver onde ela quebra.

-- Suponha que `λx ↦ x x` tenha tipo. Chame de `σ` o tipo de `x`. No corpo
-- `x x`, o `x` da esquerda está em posição de função aplicada a um argumento,
-- logo `σ` tem de ser um tipo de função: `σ = σ₁ → τ` para algum `σ₁` e `τ`.
-- O `x` da direita é o argumento dessa aplicação, então seu tipo tem de ser o
-- domínio: `σ = σ₁`. Combinando as duas exigências, `σ = σ → τ`. Não há tipo
-- simples que satisfaça essa equação: qualquer solução teria de ser um tipo
-- estritamente maior que si mesmo (a árvore de `σ → τ` contém a de `σ` como
-- subárvore própria), e não existe tipo finito assim. É precisamente o
-- *occurs check* que o unificador do Lean reporta ao dizer que `x` tem tipo
-- `?m → ?n` mas se espera `?m`.

-- Portanto `λx ↦ x x` já é intipável, e a fortiori a aplicação dele a si
-- mesmo também. Vale notar que a impossibilidade não é um defeito do Lean:
-- ela é consequência de o sistema ser fortemente normalizante. Sistemas que
-- admitem tipos recursivos (`σ ≅ σ → τ`, via `μ`-tipos) conseguem tipar esse
-- termo, mas ao preço de perder a garantia de terminação — e, se usados como
-- lógica, a consistência.

-- ### Exercise (1 star): 3.17 ⭐

-- Ref. CSwFP/2, exercício 3.17 (p. 30).

-- Adjetivos combinam com nomes para formar nomes complexos: *friendly*
-- combina com *wizard* para formar *friendly wizard*. Adjetivos são,
-- portanto, de tipo `N → N`.

-- Ache um tipo para o advérbio *very*, tal que se possa construir *very
-- friendly wizard* e *very very friendly wizard*. (Assuma que as expressões
-- se estruturam como `(very friendly) wizard` e
-- `(very (very
-- friendly)) wizard`.)

-- `very : Adj → Adj`: um advérbio de grau não modifica um nome, modifica um
-- *adjetivo*, e devolve outro adjetivo. É exatamente isso que permite as duas
-- construções pedidas — como o resultado de `very` é de novo um `Adj`, ele
-- serve como argumento de si mesmo.

abbrev N := String
abbrev Adj := N → N

def wizard : N := "wizard"
def friendly : Adj := fun n => "friendly " ++ n

def very : Adj → Adj :=
  sorry

theorem very_test1 :
    very friendly wizard = "very friendly wizard" :=
  sorry
theorem very_test2 :
    very (very friendly) wizard =
      "very very friendly wizard" :=
  sorry

-- O ponto teórico é que o tipo de `very` é *endomórfico* na categoria dos
-- adjetivos (entra `Adj`, sai `Adj`), e por isso a iteração é ilimitada com
-- um único tipo, sem precisar de um tipo novo para cada nível de encaixe. As
-- duas verificações por `rfl` acima compilam — o que faz do próprio
-- verificador de tipos a confirmação da resposta.

-- ## Tipos como disciplina

-- O tipo de uma função diz o que ela aceita e o que devolve, e Lean recusa a
-- aplicação que não respeite isso — ao escrever, antes de rodar.

-- Essa recusa é o instrumento central do texto. As árvores sintáticas do
-- capítulo 4 serão tipos, e os significados do capítulo 7 também; daí em
-- diante, "esta combinação de palavras não é bem formada" e "este programa
-- não tipa" passam a ser a mesma frase.

-- Para ver a recusa acontecer, tente dar ao verbo um objeto que não é uma
-- entidade: `#check likes "Toto"` não compila, e o erro aponta o argumento —
-- uma `String` onde se esperava um `NP`. É a versão tipada de dizer que a
-- combinação não é bem formada.

end Foundation

