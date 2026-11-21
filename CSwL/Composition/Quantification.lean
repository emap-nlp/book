import CSwL.ModelChecking
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Card
import Mathlib.Computability.Language

-- # Quantificação

namespace Composition

open ModelChecking

-- A quantificação é central para explicar as inferências em língua natural. A
-- teoria aristotélica apresentada em Um Motor de Inferência trata sentenças
-- com um único quantificador. Ela não permite combinar quantificadores na
-- mesma sentença nem abrange expressões como **most**, **half of** e **at
-- least five**. Além disso, algumas de suas inferências pressupõem que a
-- restrição tenha elementos.

-- Na lógica de Frege, os quantificadores $\forall$ e $\exists$ ligam
-- variáveis em fórmulas arbitrárias, permitindo combinar várias
-- quantificações. Eles podem ser definidos um pelo outro com a negação:
-- $\exists x\,P(x)$ equivale a $\neg\forall x\,\neg P(x)$. As quatro formas
-- do quadrado das oposições recebem representações nessa lógica. Por exemplo,
-- «todo A é B» é $\forall x\,(A(x)\to B(x))$, e «algum A é B» é $\exists
-- x\,(A(x)\land B(x))$.

-- Essas fórmulas não pressupõem que a extensão de `A` seja não vazia. Se
-- nenhum elemento satisfaz `A`, a universal é verdadeira e a existencial é
-- falsa. Nesse caso, «todo A é B» e «nenhum A é B» são ambas verdadeiras,
-- enquanto as duas particulares são falsas. As relações de contrariedade,
-- subcontrariedade e subalternação do quadrado exigem, portanto, a
-- pressuposição existencial. As diagonais continuam sendo contraditórias.
-- Esse é também o motivo pelo qual uma inferência como **Darapti** pode
-- falhar na lógica de primeira ordem.

-- Com a igualdade, podemos expressar quantidades fixas na lógica de primeira
-- ordem. Para dizer que pelo menos dois elementos são A e B, quantificamos
-- duas variáveis e exigimos que seus valores sejam distintos: $\exists
-- x\exists y\,(x\neq y\land A(x)\land A(y)\land B(x)\land B(y))$.

-- A função `atLeastTwo` recebe os nomes dos dois predicados e constrói uma
-- fórmula de tipo `LF`. O termo `.neg (.eq tx ty)` exprime a desigualdade
-- entre as variáveis. A função `check` avalia a fórmula no modelo do
-- fragmento. Nesse modelo, há três pessoas que riem, das quais duas são
-- meninas.

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
    check (atMostTwo "girl" "laugh") :=
  sorry

theorem atMostTwo_person :
    ! check (atMostTwo "person" "laugh") :=
  sorry

-- As funções `atLeastTwo` e `atMostTwo` constroem fórmulas. É importante
-- acompanhar os dois níveis envolvidos: Lean é a metalinguagem em que
-- escrevemos o programa, e FOL é a linguagem objeto cujas fórmulas o programa
-- produz.

-- Para cada número natural fixo, podemos construir uma fórmula que conte até
-- ele. Também podemos combinar essas fórmulas por conjunção, disjunção e
-- negação. Isso não fornece à linguagem objeto uma operação única de contagem
-- com limite arbitrário. Cada fórmula resultante é finita e tem sua própria
-- quantidade de variáveis e quantificadores.

-- ### Exercise (3 stars): at-least-n ⭐⭐⭐

-- Defina `atLeast n a b`, a fórmula de "pelo menos n A são B", e
-- `atMost n a b`, a de "no máximo n A são B". Nenhuma fórmula sozinha serve
-- para todo `n`, mas uma única função Lean pode gerar, para cada `n`, a
-- fórmula correspondente.

-- Dicas: as `n` variáveis distintas podem sair do índice de `Variable`, pois
-- `⟨"x", [i]⟩` é a variável `xi`. "No máximo n" é a negação de "pelo menos n
-- + 1". Para `atLeast`, uma função auxiliar recursiva pode carregar a lista
-- dos termos já quantificados, para exigir que cada nova variável seja
-- diferente de todos eles.

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

-- Combinar quantificadores torna visíveis diferenças de escopo. **Every
-- prince sang a ballad** pode afirmar que cada príncipe cantou alguma balada,
-- possivelmente uma diferente para cada um. Com o escopo invertido, existe
-- uma balada que todos os príncipes cantaram. As fórmulas de primeira ordem
-- distinguem as leituras $\forall x\,(Prince(x)\to\exists y\,(Ballad(y)\land
-- Sang(x,y)))$ e $\exists y\,(Ballad(y)\land\forall x\,(Prince(x)\to
-- Sang(x,y)))$. A sentença passiva **A ballad was sung by every prince**
-- também permite examinar esse contraste.

-- Como em Formas Linguísticas e Traduções para Lógica, a estrutura da fórmula
-- pode diferir da estrutura sintática da sentença. Os sintagmas nominais
-- deixam de aparecer como unidades na representação. Queremos preservar suas
-- contribuições semânticas como componentes da composição e obter um
-- procedimento sistemático para combiná-las. Também queremos incluir
-- quantificadores como **most** no mesmo tratamento. A perspectiva relacional
-- e os significados tipados permitirão desenvolver esses três objetivos.

-- ## A Visão Relacional dos Quantificadores

-- Na perspectiva relacional, um determinante relaciona dois subconjuntos de
-- um domínio: a restrição e o escopo. Essa abordagem foi desenvolvida por
-- Mostowski (Mostowski, 1957) e, para a língua natural, por Barwise e Cooper
-- (Barwise and Cooper, 1981).

-- Em **Every princess laughed**, a restrição é o conjunto das princesas, e o
-- escopo é o conjunto dos que riram. A sentença é verdadeira quando o
-- primeiro conjunto está contido no segundo. A função `every` verifica essa
-- condição percorrendo as entidades do modelo.

-- A composição pode ser acompanhada pelos tipos. O determinante recebe duas
-- propriedades e tem tipo `OnePlacePred → OnePlacePred → Bool`. Depois de
-- receber `princess`, a expressão `every princess` ainda espera uma
-- propriedade. Ao receber `laugh`, produz um valor de verdade. Assim, o
-- significado do sintagma nominal continua sendo uma unidade que participa da
-- composição. Em `lfDET`, restrição e escopo serviam para construir uma
-- fórmula; aqui, eles são interpretados diretamente no modelo.

def every (p q : OnePlacePred) : Bool :=
  entities.all (fun x => p x → q x)

#eval (every princess) laugh

-- Uma propriedade como `princess` pode ser vista como a função característica
-- de um conjunto de entidades, conforme Conjuntos e Relações. Aplicamos a
-- mesma ideia às propriedades: `every princess` é a função característica do
-- conjunto das propriedades que todas as princesas têm.

-- Se `q` é uma dessas propriedades, o conjunto das princesas está contido no
-- conjunto das entidades que satisfazem `q`. A avaliação abaixo restringe
-- essa consulta a três propriedades do modelo. Apenas `laugh` é aceita, por
-- isso o resultado contém somente o nome dessa propriedade.

#eval [("laugh", laugh), ("cheer", cheer),
       ("shudder", shudder)]
  |>.filter (fun (_, q) => every princess q) |>.map (·.1)

-- A sentença **Every dwarf defeated a giant** contém dois sintagmas
-- quantificados. Para compor o significado do objeto, começamos pelo
-- determinante **a**. A função `a p q` é verdadeira quando existe uma
-- entidade que satisfaz tanto `p` quanto `q`. Em termos de conjuntos, a
-- interseção entre restrição e escopo deve ser não vazia.

-- Depois de receber a propriedade `giant`, a expressão `a giant` espera a
-- propriedade que será fornecida pela relação verbal.

def a (p q : OnePlacePred) : Bool :=
  entities.any (fun x => p x ∧ q x)

-- Precisamos distinguir a palavra da gramática, sua interpretação no modelo e
-- a função usada na composição. O construtor `TV.defeated` representa a
-- palavra. A função `defeat` é a relação binária entre entidades. Já
-- `defeated` combinará essa relação com o significado de um sintagma nominal.

-- O objeto `a giant` espera uma propriedade, mas a relação de derrotar recebe
-- duas entidades. Fixando um sujeito `y`, obtemos a propriedade
-- `fun z => defeat y z`. Aplicar o objeto a essa propriedade verifica se `y`
-- derrotou algum gigante. Abstraindo sobre `y`, obtemos a propriedade
-- denotada por **defeated a giant**.

-- A avaliação lista as entidades que têm essa propriedade. O resultado,
-- `[B, R]`, contém precisamente os dois anões do modelo.

def defeated (X : OnePlacePred → Bool) : OnePlacePred :=
  fun y => X (fun z => defeat y z)

#eval entities.filter (defeated (a giant))

-- Para completar a sentença, aplicamos `every dwarf` à propriedade
-- `defeated (a giant)`. O cálculo verifica se cada anão derrotou algum
-- gigante. As duas avaliações diferem apenas na presença dos parênteses e
-- realizam a mesma aplicação de funções.

-- Nessa composição, o objeto está no escopo do sujeito. O gigante pode variar
-- conforme o anão. A leitura em que um único gigante está no escopo mais
-- amplo exigiria outra composição.

#eval (every dwarf) (defeated (a giant))
#eval every dwarf (defeated (a giant))

-- ## Condições sobre as Relações Quantificadoras

-- Nem toda relação entre conjuntos se comporta como um quantificador de
-- quantidade. Usaremos três condições para delimitar essa noção: a extensão,
-- EXT, a conservatividade, CONS, e a invariância por isomorfismo, ISOM. Cada
-- uma exclui um tipo de dependência, que veremos em **many**, em **only** e
-- no possessivo **Alice's**. Chamaremos de quantificadores as relações que
-- satisfazem as três condições.

-- Para enunciar e provar as condições, usamos proposições sobre conjuntos. O
-- tipo `GQ.Det α` abrevia `Set α → Set α → Set α → Prop`. Em `D E A B`, `E` é
-- o universo, `A` é a restrição e `B` é o escopo. Como o tipo não impõe
-- inclusões entre esses conjuntos, as condições recebem explicitamente as
-- hipóteses `A ⊆ E` e `B ⊆ E`. A categoria sintática `DET` e o tipo `GQ.Det`
-- têm funções distintas: a primeira representa palavras, e o segundo permite
-- representar relações semânticas, inclusive as que não satisfazem as
-- condições de quantificador.

namespace GQ

abbrev Det (α : Type) := Set α → Set α → Set α → Prop

def all  {α} : Det α := fun _ A B => A ⊆ B
def some {α} : Det α := fun _ A B => ∃ x, x ∈ A ∧ x ∈ B
def no   {α} : Det α := fun _ A B => ∀ x, x ∈ A → x ∉ B
def only {α} : Det α := fun _ A B => B ⊆ A

-- A relação `GQ.all` expressa a inclusão da restrição no escopo. Ela
-- corresponde à função `every` quando representamos cada propriedade pelo
-- conjunto das entidades em que ela é verdadeira.

-- O teorema estabelece essa correspondência nas duas direções. A prova usa
-- `mem_entities`, que garante que toda entidade do tipo `Entity` aparece na
-- lista usada pela avaliação de `every`.

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

-- A condição EXT compara universos `E` e `E'` com `E ⊆ E'`. Se a restrição e
-- o escopo já estão contidos em `E`, aumentar o universo não deve mudar o
-- valor da relação. Podemos, portanto, considerar apenas um universo que
-- contenha `A ∪ B`.

-- A condição CONS compara `D E A B` com `D E A (A ∩ B)`. Ela permite
-- descartar todos os elementos do escopo que estão fora da restrição. Depois
-- dessa redução, as regiões relevantes são os A que satisfazem B e os A que
-- não satisfazem B.

def Ext {α : Type} (D : Det α) : Prop :=
  ∀ E E' A B, A ⊆ E → B ⊆ E → E ⊆ E' → (D E A B ↔ D E' A B)

def Cons {α : Type} (D : Det α) : Prop :=
  ∀ E A B, A ⊆ E → B ⊆ E → (D E A B ↔ D E A (A ∩ B))

-- As relações `GQ.all` e `GQ.some` satisfazem EXT e CONS. Para EXT, as provas
-- usam `rfl`, pois ambas as definições ignoram o argumento do universo. Os
-- dois lados da equivalência são, assim, a mesma proposição.

-- Para CONS, a inclusão `A ⊆ B` equivale a `A ⊆ A ∩ B`. No caso existencial,
-- um elemento pertence simultaneamente a `A` e `B` exatamente quando pertence
-- a `A` e a `A ∩ B`. As provas abaixo explicitam essas duas correspondências.

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

-- Uma leitura de **many** pode depender do tamanho do universo. Vamos
-- representar uma versão simples em que «muitos A são B» significa que os
-- elementos de `A ∩ B` são mais da metade dos elementos de `E`. Ao aumentar
-- `E` sem alterar `A` e `B`, a relação pode deixar de valer, violando EXT.

-- Usamos `Set.ncard` para expressar as cardinalidades finitas.

def many {α : Type} : Det α :=
  fun E A B => E.ncard < 2 * (A ∩ B).ncard

-- ### Exercise (2 stars): many-not-ext ⭐⭐

-- Prove que `many` não satisfaz EXT. Basta um universo `E` em que a relação
-- vale e um universo maior `E'` em que ela deixa de valer.

theorem many_not_ext : ¬ Ext (many : Det Nat) := by
  sorry

-- Em **Only dwarfs sing during work**, todos os que cantam durante o trabalho
-- devem ser anões. A relação `GQ.only` exige, portanto, `B ⊆ A`.

-- ### Exercise (2 stars): only-not-cons ⭐⭐

-- Prove que **only** não é conservativo. Basta escolher uma restrição e um
-- escopo para os quais as duas leituras da definição de `Cons` dão resultados
-- diferentes.

theorem only_not_cons : ¬ Cons (only : Det Entity) := by
  sorry

-- A condição ISOM formaliza a independência em relação à identidade dos
-- elementos. Se `f` leva o universo `E` bijetivamente em `E'`, a relação que
-- vale entre `A` e `B` deve valer entre suas imagens. A notação `f '' A`
-- denota o conjunto dos valores `f x` com `x ∈ A`, e `Set.BijOn` expressa a
-- bijeção entre os universos.

-- Com EXT, CONS e ISOM, uma relação sobre conjuntos finitos depende somente
-- das quantidades nas regiões `A - B` e `A ∩ B`. Isso inclui artigos. **A**
-- tem a condição existencial de **some**. Na leitura de Russell, **the**
-- exige que `A` tenha um único elemento e que ele pertença a `B`, isto é,
-- $|A-B|=0$ e $|A\cap B|=1$.

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

-- Na leitura de Verificação de Modelos com Lógica de Primeira Ordem, **The
-- dwarf laughed** diz que há exatamente um anão e que ele riu. Como relação
-- entre conjuntos, `the E A B` diz que `A` tem um único elemento e que ele
-- está em `B`. Mostre que `the` satisfaz EXT, CONS e ISOM. Assim, o artigo
-- **the** é, no sentido técnico desta seção, um quantificador.

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
-- satisfaz EXT e CONS, mas não ISOM. Assim, EXT e CONS não bastam para fazer
-- de um determinante um quantificador.

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

-- ## Árvores Numéricas

-- Para representar os casos finitos, escrevemos $m=|A-B|$ e $n=|A\cap B|$. O
-- par `(m, n)` descreve quantos elementos da restrição deixam de satisfazer o
-- escopo e quantos o satisfazem. As condições estudadas permitem ignorar o
-- restante do universo e a identidade dos elementos.

-- Organizamos esses pares em uma árvore de linhas. Na linha `k`, a restrição
-- tem `k` elementos e, portanto, `m + n = k`. Da esquerda para a direita,
-- diminuímos `m` e aumentamos `n`. A posição `(1, 2)` da linha três, por
-- exemplo, representa uma restrição com três elementos, dos quais dois
-- satisfazem o escopo. A função `row` enumera as posições de uma linha.

def row (k : Nat) : List (Nat × Nat) :=
  (List.range (k + 1)).map fun x => (k - x, x)

-- A função `tree k` reúne as linhas de zero até `k`. Cada linha acrescenta os
-- casos para mais um tamanho de restrição. A árvore matemática tem infinitas
-- linhas, mas sua representação por uma lista do Lean é finita. O parâmetro
-- `k` fixa o trecho que queremos examinar ou desenhar.

def tree (k : Nat) : List (List (Nat × Nat)) :=
  (List.range (k + 1)).map row

#eval tree 3

-- Para desenhar a árvore, transformamos cada par em um texto. A função
-- `labelTree k cell` aplica `cell` aos dois números de cada posição, e
-- `drawTree w` distribui os textos em linhas, usando a largura `w` para
-- calcular o recuo.

-- A função `numberTree` escreve o próprio par em cada posição. Até a linha
-- nove, os dois números têm um algarismo cada e, separados por vírgula, cabem
-- na largura de três caracteres usada no desenho.

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

-- Um quantificador numérico seleciona as posições em que é verdadeiro. A
-- função `patternTree` usa a mesma organização da árvore numérica, mas
-- escreve `+` para uma posição aceita e `-` para uma posição recusada.
-- Chamamos esse desenho de padrão do quantificador.

-- Os exemplos mostram três condições sobre as contagens. **At least three**
-- exige `n ≥ 3`, **less than half** exige `2 * n < m + n`, e **an even number
-- of** exige que `n` seja par. A comparação dos desenhos permite observar
-- como cada condição seleciona regiões diferentes da árvore.

def patternTree (k : Nat) (q : Nat → Nat → Bool) :
    String :=
  drawTree 1 (labelTree k fun m n =>
    if q m n then "+" else "-")

#eval IO.println <| patternTree 5 fun _ n => n ≥ 3
#eval IO.println <| patternTree 5 fun m n => 2 * n < m + n
#eval IO.println <| patternTree 5 fun _ n => n % 2 == 0

-- Também podemos dar um quantificador como uma função que recebe uma lista de
-- objetos e uma propriedade. O tipo `ListQuant` usa naturais como objetos
-- para que possamos montar universos de teste. As funções `List.all` e
-- `List.any` verificam se todos ou algum dos elementos da lista satisfazem a
-- propriedade.

-- Essa apresentação toma a própria restrição como universo da consulta,
-- usando as reduções permitidas por CONS e EXT.

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

-- ## Representações Lógicas para Quantificadores

-- Os padrões podem ser descritos diretamente por expressões aritméticas nas
-- duas contagens. O tipo `NumQuant` dá nome às funções `Nat → Nat → Bool`, já
-- usadas como argumento de `patternTree`. Um valor desse tipo decide quais
-- pares pertencem ao padrão.

-- Por exemplo, **all** exige `m = 0`, **no** exige `n = 0`, **at least k**
-- exige `n ≥ k`, e **at most k** exige `n ≤ k`. As definições abaixo permitem
-- combinar e estudar essas condições sem construir conjuntos ou listas de
-- entidades a cada consulta.

abbrev NumQuant := Nat → Nat → Bool

def allNum : NumQuant := fun m _ => m = 0
def noNum  : NumQuant := fun _ n => n = 0
def atLeastNum (k : Nat) : NumQuant := fun _ n => n ≥ k
def atMostNum  (k : Nat) : NumQuant := fun _ n => n ≤ k

-- A função `toNum` constrói uma representação numérica a partir de um
-- `ListQuant`. Para cada par `(m, n)`, fornece à função uma lista dos
-- naturais de um até `m + n` e a propriedade «ser menor ou igual a `n`».
-- Nessa lista, exatamente `n` elementos têm a propriedade.

-- Se a função representa um quantificador invariante por isomorfismo, essa
-- consulta depende apenas das contagens. As igualdades abaixo comparam os
-- padrões de `List.all` e de sua condição numérica, bem como os de **no**,
-- até a linha cinco.

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

-- Podemos formar quantificadores compostos aplicando operações lógicas a seus
-- valores em cada posição. A negação troca `+` por `-` e `-` por `+`. A
-- conjunção aceita uma posição quando os dois quantificadores a aceitam, e a
-- disjunção a aceita quando pelo menos um deles a aceita.

-- A expressão **at least three but not all** combina `n ≥ 3` com a negação de
-- `m = 0`. Seu padrão conserva as posições de **at least three** que ficam
-- fora da borda direita da árvore. As funções `notNum`, `andNum` e `orNum`
-- implementam essas operações.

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

-- ## Propriedades Relacionais

-- Como quantificadores são relações entre conjuntos, podemos perguntar se são
-- reflexivos, simétricos ou monótonos. Cada propriedade pode ser enunciada
-- para as relações de tipo `GQ.Det` e estudada nos padrões numéricos
-- correspondentes.

-- A reflexividade exige que `Q A A` valha para toda restrição `A`. Isso vale
-- para **all**, pois todo conjunto está contido em si mesmo. Para **some**, a
-- interseção de `A` consigo mesmo precisa ter um elemento.

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

-- Na consulta `Q A A`, nenhum elemento da restrição fica fora do escopo.
-- Logo, `m = 0`, e a posição correspondente é `(0, |A|)`. Variando o tamanho
-- da restrição, percorremos a borda direita da árvore. Um quantificador
-- reflexivo tem `+` em toda essa borda, incluindo o topo `(0, 0)`.

-- O topo é o caso da restrição vazia. O padrão de **all** o aceita, enquanto
-- o de **some** o recusa. A definição `ReflNum` expressa a condição da borda
-- por uma proposição sobre funções numéricas.

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

-- Uma relação quantificadora é simétrica quando trocar restrição e escopo
-- conserva seu valor. **Some** é simétrico porque a existência de um elemento
-- em `A ∩ B` também garante um elemento em `B ∩ A`. Assim, **Alguma menina
-- riu** tem o mesmo valor de verdade que **Alguém que riu era menina**.

-- A troca altera o significado de **all**. **Toda princesa riu** permite que
-- outras pessoas também tenham rido; **Todos os que riram eram princesas**
-- exige que não haja essas outras pessoas. As avaliações mostram a diferença
-- no modelo.

-- A simetria também ajuda a estudar as construções existenciais do inglês.
-- Nos exemplos considerados aqui, **There are some dwarfs**, **There are no
-- dragons** e **There are three wizards** aceitam quantificadores simétricos.
-- As leituras existenciais neutras de **There are all dwarfs** e **There are
-- most dragons** não apresentam a mesma aceitabilidade. Usaremos esse
-- contraste como uma aplicação da análise relacional dos quantificadores.

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

-- A monotonicidade no escopo descreve o que acontece quando variamos `B`,
-- mantendo a restrição. Um quantificador é MON↑ se uma consulta verdadeira
-- permanece verdadeira quando o escopo aumenta. Se todos os A pertencem a B,
-- também pertencem a qualquer conjunto que contenha B. O mesmo crescimento
-- preserva **some** e **at least three**.

-- Um quantificador é MON↓ se a verdade é preservada quando o escopo diminui.
-- Se nenhum A pertence a B, nenhum pertence a um subconjunto de B. Essa
-- propriedade vale para **no** e para **not all**. As definições abaixo
-- enunciam os dois sentidos sobre conjuntos.

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

-- As definições `MonUpNum` e `MonDownNum` escrevem essas formas como
-- proposições sobre `NumQuant`.

-- O padrão de **an even number of** alterna entre `+` e `-` nas linhas.
-- Acrescentar ou retirar um elemento do escopo pode mudar a paridade.

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

-- A monotonicidade também permite estudar contrastes linguísticos. Em **all
-- men and some women**, a coordenação reúne dois sintagmas MON↑. Em **many
-- English but no Dutch**, a conjunção **but** marca um contraste entre
-- orientações de inferência.

-- Expressões como **any** e **lift a finger** são itens de polaridade
-- negativa. Um escopo MON↓ pode licenciá-las, como em **No dwarf liked any of
-- the elves**. A troca por **Every dwarf** retira esse ambiente decrescente e
-- torna a leitura pretendida inaceitável. Esses contrastes motivam o estudo
-- da monotonicidade, sem esgotar as condições linguísticas de licenciamento.

-- Há também contrastes associados à polaridade positiva. **Some people could
-- hardly believe it** é aceitável na leitura considerada, enquanto **Nobody
-- could hardly believe it** é marcada como inaceitável nessa mesma leitura. A
-- comparação muda a orientação do sintagma que toma a expressão em seu
-- escopo.

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

-- Também podemos variar a restrição e manter o escopo. Um quantificador é
-- ↑MON se a verdade é preservada ao aumentar `A`, e ↓MON se é preservada ao
-- diminuir `A`. **Some** e **not all** são crescentes na restrição; **all** e
-- **no** são decrescentes nela.

-- Por exemplo, se algum A é B, aumentar A conserva esse elemento. Se todo A é
-- B, restringir A conserva a inclusão. Na árvore, acrescentar um elemento a A
-- aumenta `n` quando ele está em B e aumenta `m` quando está fora de B.

-- A orientação na restrição também aparece em fenômenos de polaridade. **All
-- dwarfs who liked any of the elves were mistrusted** coloca a oração
-- relativa em uma restrição decrescente. A substituição de **all** por
-- **some** altera essa orientação e o licenciamento pretendido de **any**.

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

-- ## Quantificadores, Autômatos e Definibilidade

-- Podemos registrar uma situação de quantificação como uma palavra sobre o
-- alfabeto binário. Percorremos os elementos de uma lista que representa A e
-- escrevemos `1` quando satisfazem B e `0` quando não satisfazem. No código,
-- esses símbolos são os valores booleanos `true` e `false`. Para que as
-- contagens representem cardinalidades, a lista deve enumerar os elementos de
-- A sem repetições, como ocorre nos exemplos obtidos de `entities`.

-- A função `wordOf` produz a palavra. A função `accepts` conta zeros e uns e
-- consulta o quantificador numérico nessa posição. A linguagem `langOf q`
-- reúne todas as palavras aceitas por `q`. Usamos `Language Bool`, do
-- Mathlib, para representar esse conjunto de palavras e suas operações.

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

-- No exemplo com as meninas do modelo, a palavra contém dois zeros e dois
-- uns. Por isso, **All girls laughed** é falsa e **Some girl laughed** é
-- verdadeira.

-- Reordenar os elementos conserva as duas contagens. O teorema abaixo usa
-- `List.Perm.count_eq` para mostrar que uma permutação de uma palavra aceita
-- também é aceita. A linguagem de um quantificador numérico é, portanto,
-- fechada por permutação, refletindo nas palavras a independência da
-- identidade dos elementos.

theorem langOf_perm (q : NumQuant) {v w : Word}
    (h : v.Perm w) (hv : v ∈ langOf q) :
    w ∈ langOf q := by
  rw [mem_langOf, accepts] at *
  rw [← h.count_eq, ← h.count_eq]
  exact hv

-- As operações lógicas sobre quantificadores também se expressam nas
-- linguagens que eles aceitam. Negar um quantificador aceita exatamente as
-- palavras que ele recusava. Assim, a linguagem de `notNum` é o complemento,
-- indicado por `ᶜ`, da linguagem original.

-- O teorema verifica essa correspondência palavra por palavra.

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

-- O quantificador **all** exige que a palavra não contenha nenhum zero. Suas
-- palavras são sequências de uns, incluindo a palavra vazia. Essa linguagem é
-- o fecho de Kleene da linguagem formada apenas pela palavra `[true]`.

-- A notação `∗` permite concatenar zero ou mais palavras da linguagem.

-- ### Exercise (3 stars): all-kstar ⭐⭐⭐

-- Prove que a linguagem de **all** é `{[true]}∗`.

open Computability in
theorem langOf_allNum :
    langOf allNum = ({[true]} : Language Bool)∗ := by
  sorry

-- Um autômato que aceita exatamente a linguagem de um quantificador computa
-- esse quantificador nas palavras que representam as situações. Como a
-- decisão depende somente das contagens, a linguagem aceita deve ser
-- invariante por permutação.

-- Para quantificadores sobre conjuntos finitos, a caracterização de van
-- Benthem relaciona a definibilidade em primeira ordem a autômatos finitos
-- invariantes por permutação cujo grafo de transições não tem ciclos entre
-- estados distintos. Laços de um estado para ele mesmo são permitidos. A
-- lógica considerada usa apenas igualdade e os predicados da restrição e do
-- escopo, além dos quantificadores usuais.

-- Um teste de paridade precisa alternar entre estados de quantidade par e
-- ímpar. Já **most** exige comparar quantidades arbitrariamente grandes de
-- zeros e uns, o que excede a memória de um autômato finito. Esses
-- quantificadores ficam fora dessa lógica de primeira ordem. Na interpretação
-- direta sobre o modelo finito, entretanto, podemos implementá-los por
-- funções que calculam as contagens necessárias.

end Composition

