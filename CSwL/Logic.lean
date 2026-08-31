-- # Lógica

-- Como preparação para a semântica de fragmentos de inglês, introduzimos a
-- lógica proposicional e a lógica de predicados, e mostramos como implementar
-- sua sintaxe em Lean.

-- ## Lógica proposicional

namespace PL

-- A lógica proposicional (LP) ou cálculo sentencial, é um sistema formal no
-- qual as fórmulas representam proposições que podem ser formadas pela
-- combinação de proposições atômicas usando conectivos lógicos e um sistema
-- de regras de derivação, que permite que certas fórmulas sejam estabelecidas
-- como teoremas do sistema formal.

-- Há duas maneiras de tratar disso em Lean, e é preciso não confundi-las. Uma
-- é **raciocinar em** lógica proposicional: usar os conectivos para enunciar
-- e demonstrar coisas, como já vínhamos fazendo. A outra é **raciocinar
-- sobre** ela: tomar as fórmulas como dado, sobre o qual se computa. Este
-- capítulo faz as duas, nessa ordem, e a primeira seção é a primeira.

-- ### Regras de dedução, e as táticas que são elas

-- Cada conectivo vem com dois tipos de regra: as de **introdução**, que dizem
-- como construir uma prova cuja conclusão usa o conectivo, e as de
-- **eliminação**, que dizem como usar uma prova cuja hipótese o usa. É a
-- organização da dedução natural, e as táticas do Lean são exatamente essas
-- regras — cada uma tem nome próprio na tradição lógica, e vale saber qual é.

-- Nesta seção `P`, `Q` e `R` são proposições quaisquer.

variable (P Q R : Prop)

-- #### Implicação

-- A regra de introdução de `→` diz: para provar `P → Q`, suponha `P` e derive
-- `Q`. É o que `intro` faz — ele move o antecedente para as hipóteses.

example : P → (Q → P) := by
  intro hP _
  exact hP

-- A regra de eliminação é o **modus ponens**: de `P → Q` e de `P`, conclua
-- `Q`. Em Lean isso é aplicação — `h hP` já é a prova de `Q`. A tática
-- `apply` faz o mesmo de trás para frente: ela transforma o objetivo `Q` no
-- objetivo `P`.

example (h : P → Q) (hP : P) : Q := h hP

example (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  intro hP
  apply h₂
  apply h₁
  exact hP

-- #### Conjunção

-- Introdução de `∧`: para provar `P ∧ Q`, prove `P` e prove `Q`. A tática
-- `constructor` parte o objetivo em dois; o construtor anônimo `⟨_, _⟩` faz o
-- mesmo em forma de termo.

example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

-- Eliminação de `∧`: de `P ∧ Q` conclua `P`, e conclua `Q`. São duas regras,
-- e em Lean são as projeções `.1` e `.2`. A tática `obtain` desmonta a
-- hipótese de uma vez, dando nome às duas partes.

example (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

-- #### Disjunção

-- Introdução de `∨`: para provar `P ∨ Q` basta provar um dos dois lados. São
-- duas regras, e as táticas `left` e `right` escolhem qual.

example (hP : P) : P ∨ Q := by
  left
  exact hP

-- Eliminação de `∨` é a regra que dá mais trabalho, e por um bom motivo: de
-- `P ∨ Q` não se sabe qual dos dois vale. Para concluir `R` a partir dela é
-- preciso concluir `R` nos dois casos. A tática `cases` abre exatamente esses
-- dois objetivos.

example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ

-- #### Negação e o absurdo

-- Não há um conectivo primitivo para a negação: `¬P` é notação para
-- `P → False`, onde `False` é a proposição sem nenhuma prova. Isso já entrega
-- as duas regras.

-- A introdução de `¬` é a introdução de `→`: para provar `¬P`, suponha `P` e
-- derive `False`.

example (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)

-- A eliminação é a eliminação de `→`: de `¬P` e de `P` sai `False`. E de
-- `False` sai qualquer coisa — é a regra que a tradição chama de **ex falso
-- quodlibet**, `False.elim` em Lean. As duas juntas são `absurd`.

example (hP : P) (hn : ¬P) : False := hn hP

example (h : False) : P := False.elim h

example (hP : P) (hn : ¬P) : Q := absurd hP hn

-- #### Bi-implicação

-- `P ↔ Q` é a conjunção das duas implicações, e as regras seguem disso:
-- `constructor` parte o objetivo nas duas direções, e `.mp` e `.mpr` são as
-- eliminações — de `P` para `Q` e de `Q` para `P`.

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

example (h : P ↔ Q) (hP : P) : Q := h.mp hP

-- #### O que as regras acima não dão

-- Repare que em nenhum momento se usou "ou `P` vale, ou não vale". Todas as
-- regras até aqui são **construtivas**: uma prova de `P ∨ Q` traz consigo
-- qual dos dois lados vale, e uma prova de `P` é uma construção de `P`. Nessa
-- leitura, `P ∨ ¬P` não é um princípio disponível — afirmá-lo seria dizer
-- que, para toda proposição, sabemos decidir de que lado ela cai.

-- O raciocínio **clássico** acrescenta esse princípio, chamado de terceiro
-- excluído. Em Lean ele existe, e tem nome:

example : P ∨ ¬P := Classical.em P

-- Dele saem as duas táticas que o capítulo vai usar. `by_cases` parte a prova
-- em dois casos, supondo `P` num e `¬P` no outro:

example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exact absurd hP h

-- E `by_contra` prova `P` supondo `¬P` e derivando `False` — a redução ao
-- absurdo:

example (h : ¬¬P) : P := by
  by_contra hn
  exact h hn

-- A distinção volta a importar mais adiante, quando cada fórmula receber um
-- valor entre dois: uma valoração que só admite verdadeiro e falso é, por
-- construção, clássica.

-- ### Exercise (1 star): contrapositive ⭐

-- Prove a contrapositiva, e depois a volta. Só uma das duas direções precisa
-- de raciocínio clássico — descubra qual.

example : (P → Q) → (¬Q → ¬P) := sorry

example : (¬Q → ¬P) → (P → Q) := sorry

-- ### Exercise (2 stars): de-morgan ⭐⭐

-- Uma das leis de De Morgan vale construtivamente; a outra precisa do
-- terceiro excluído.

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := sorry

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := sorry

-- ### Sintaxe

-- Na BNF a seguir, as letras proposicionais são os `atom`, podemos predefinir
-- um certo conjunto de letras como válidas ou um processo de geração de
-- âtomos válidos com o sufixo `'`.

-- atom ::= "p" | "q" | "r" | atom"'" ;
-- F    ::= atom
--   | "¬" F ("negação")
--   | "(" F "∧" F ")" ("conjunção")
--   | "(" F "∨" F ")" ("disjunção") ;

-- gerando fórmulas como `¬¬¬p'''`, `((p ∨ p') ∧ p')`, `(p ∧ (p' ∧ p'''))`.
-- Sem parênteses a gramática é ambígua — `p ∧ p′ ∨ p″` lê-se tanto como
-- `(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural
-- afeta o significado, como na sentença em português "era jovem e bonita ou
-- triste".

-- Um átomo é identificado por um nome, e o nome é uma `String`. Isso dá o
-- inventário ilimitado que a gramática pede sem precisar enumerar símbolo por
-- símbolo: `p`, `q`, `p'` e `chove` são todos átomos, e nada impede inventar
-- mais um.

-- A conjunção e a disjunção são binárias. Poderiam receber uma lista de
-- fórmulas de uma vez — `conj (fs : List Form)` —, mas um construtor que
-- guarda uma `List Form` dentro do próprio tipo o torna um indutivo *nested*,
-- e isso custa caro em Lean: perdem-se `deriving DecidableEq` e a tática
-- `induction`, os dois necessários mais adiante. Com dois argumentos, uma
-- conjunção de três fórmulas é `conj f (conj g h)`, e tudo continua
-- funcionando.

inductive Form where
  | atom (name : String)
  | top
  | bot
  | neg (f : Form)
  | conj (f g : Form)
  | disj (f g : Form)
  deriving DecidableEq, Repr

-- `top`/`bot` são a base da recursão de `conjs`/`disjs` abaixo — uma
-- conjunção vazia é sempre verdadeira, uma disjunção vazia é sempre falsa.
-- Diferente de um átomo de nome `"⊤"` (que a valoração, adiante neste
-- capítulo, `(String → Bool) → Form → Bool`, poderia mandar para `false`,
-- dependendo da atribuição de átomos), `top`/`bot` são construtores próprios:
-- a valoração vai tratá-los como constantes, sempre `true`/`false`, sem
-- depender de nenhuma atribuição — por isso a conjunção vazia imprime
-- `"true"` e a disjunção vazia `"false"` (ver `toStringPolish` abaixo).

-- Notação n-ária recuperada por duas funções, para a valoração e para os
-- fragmentos de língua que virão (uma conjunção/disjunção quase sempre de
-- dois elementos, e uma única vez com mais — o `lfDET The` da verificação de
-- modelos):

def Form.conjs : List Form → Form
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Form.conjs fs)

def Form.disjs : List Form → Form
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Form.disjs fs)

-- `ToString` em notação polonesa (prefixa):

def Form.toStringPolish : Form → String
  | .atom name => name
  | .top => "true"
  | .bot => "false"
  | .neg f => "-" ++ f.toStringPolish
  | .conj f g =>
    "&[" ++ f.toStringPolish ++ "," ++
      g.toStringPolish ++ "]"
  | .disj f g =>
    "v[" ++ f.toStringPolish ++ "," ++
      g.toStringPolish ++ "]"

instance : ToString Form := ⟨Form.toStringPolish⟩

def form1 : Form := .conj (.atom "p") (.neg (.atom "p"))

def form2 : Form :=
  .disj (.atom "p1")
    (.disj (.atom "p2") (.disj (.atom "p3") (.atom "p4")))

-- `form2` não é `v[p1,p2,p3,p4]` — sendo `Form` binário, quatro disjuntos
-- exigem três `disj` encadeados, não uma lista achatada. É exatamente o preço
-- da escolha binária, e a razão de existir `Form.disjs`: `disjs` *constrói*
-- esses `disj` encadeados, não achata a saída — o mesmo `form2` de novo,
-- desta vez a partir da lista:

example :
    Form.disjs
      [.atom "p1", .atom "p2", .atom "p3", .atom "p4"] =
      form2 :=
  rfl

-- Simétrico para `conjs`, com a mesma forma de `form2` só
-- troca `∨` por `∧`:
def form2' : Form :=
  .conj (.atom "p1")
    (.conj (.atom "p2") (.conj (.atom "p3") (.atom "p4")))

example :
    Form.conjs
      [.atom "p1", .atom "p2", .atom "p3", .atom "p4"] =
      form2' :=
  rfl

-- Duas abreviações usuais: `F1 → F2` para `¬(F1 ∧ ¬F2)` ("implicação"), e
-- `F1 ↔ F2` para `(F1 → F2) ∧ (F2 → F1)` ("equivalência").

def Form.impl (f g : Form) : Form := .neg (.conj f (.neg g))
def Form.equi (f g : Form) : Form :=
  .conj (Form.impl f g) (Form.impl g f)

-- ### Exercise (1 star): translate-sentences ⭐

-- Traduza as sentenças a seguir para lógica proposicional, garantindo que as
-- condições de verdade sejam capturadas. Que limitações você encontra?

-- 1. *The wizard polishes his wand and learns a new spell, or he is lazy.*
-- 2. *The peasant will deal with the devil only if he has a plan to outwit him.*
-- 3. *If neither unicorns nor dragons exist, then neither do goblins.*

-- Use `p` para "o mago pole a varinha", `q` para "aprende um feitiço novo",
-- `r` para "está com preguiça"; `s` para "o camponês faz o trato", `t` para
-- "tem um plano"; `u`, `v` e `w` para a existência de unicórnios, dragões e
-- duendes.

def wizardOrLazy : Form :=
  sorry
def peasantOnlyIf : Form :=
  sorry
def noUnicornsNoGoblins : Form :=
  sorry

-- ### Exercise (1 star): exclusive-or ⭐

-- O conectivo `∨` é inclusivo: `p ∨ q` é verdadeiro mesmo quando `p` e `q`
-- são ambos verdadeiros. Em português, "ou" costuma ser exclusivo, como em
-- "Você pode ficar com o sorvete ou com o algodão-doce, mas não com os dois."
-- Defina um conectivo `⊕` para "ou exclusivo", usando os conectivos já
-- definidos.

def Form.xor (f g : Form) : Form :=
  sorry

-- ### Exercise (2 stars): unique-readability ⭐⭐

-- Use o princípio de indução estrutural para provar que as fórmulas de lógica
-- proposicional em notação prefixa são de leitura única.

theorem neg_inj (f g : Form) (h : Form.neg f = Form.neg g) :
    f = g :=
  sorry

theorem conj_inj (f1 f2 g1 g2 : Form)
    (h : Form.conj f1 f2 = Form.conj g1 g2) :
    f1 = g1 ∧ f2 = g2 := sorry

-- Em Lean, essas duas provas são `injection`, sem indução — um termo de tipo
-- indutivo *é* a árvore, e o Lean já sabe, para todo `inductive`, que
-- construtores diferentes produzem valores diferentes, e que um mesmo
-- construtor com argumentos diferentes produz valores diferentes. É a mesma
-- observação de "Indução estrutural", abaixo — não à toa a versão Lean deste
-- exercício é quase vazia: provar leitura única para uma gramática dada como
-- *string* exige indução estrutural genuína; aqui não há string a analisar, o
-- termo Lean já é a árvore.

-- ### Sintaxe e proposição são coisas diferentes

-- `Prop` é o tipo das proposições, e uma proposição não tem estrutura interna
-- que se possa inspecionar: ela é verdadeira ou falsa, e mais nada se
-- pergunta a ela. `Form`, acima, é um `inductive` de **sintaxe**: um valor de
-- `Form` é dado, no sentido de Programação Funcional no Lean — casa padrão,
-- conta operadores, mede profundidade, coleta os átomos que ocorrem nele — é
-- o que pedem os exercícios `count-operators`, `formula-depth` e
-- `collect-atoms`, mais abaixo. Nada disso é possível sobre um `Prop`: não há
-- como perguntar "quantos `∧` tem esta proposição" a um valor de tipo `Prop`,
-- porque `Prop` não guarda a fórmula que o provou, só se ela é verdadeira. A
-- valoração `Form → Bool` — que dá sentido a `Form` como lógica, e não só
-- como árvore — chega adiante, neste mesmo capítulo.

-- Uma fórmula pode ainda ser tomada como objeto de um sistema de prova, e não
-- de uma valoração: em vez de perguntar que valor ela recebe, pergunta-se o
-- que se deriva dela. A biblioteca `cslib` faz isso, em
-- `Cslib.Logic.PL.Proposition`, com dedução natural completa — leitura para
-- quem quiser seguir por esse caminho.

-- ### Indução estrutural

-- O Princípio da Indução Estrutural diz: para provar algo de toda fórmula,
-- basta provar da base (átomos) e do passo indutivo (que a propriedade passa
-- por `¬`, `∧`, `∨`). Onde se raciocina sobre fórmulas como *strings*, ele
-- precisa ser enunciado como teorema à parte; em Lean não é um teorema a
-- enunciar — é o recursor que `inductive Form` já gera de graça:

#check @Form.rec

-- @Form.rec : {motive : Form → Sort u_1} →
--   ((name : String) → motive (Form.atom name)) →
--     motive Form.top →
--       motive Form.bot →
--         ((f : Form) → motive f → motive f.neg) →
--           ((f g : Form) → motive f → motive g → motive (f.conj g)) →
--             ((f g : Form) → motive f → motive g → motive (f.disj g)) → (t : Form) → motive t

-- `Form.rec` — e a tática `induction`, construída sobre ele — já **são** o
-- princípio de indução estrutural, sem que o capítulo precise declará-lo.
-- Duas afirmações que noutro contexto seriam proposições a demonstrar — que
-- toda fórmula tem o mesmo número de parênteses à esquerda e à direita, e a
-- leitura única, que é o exercício acima — viram, aqui, só `induction`:

def Form.leftParens : Form → Nat
  | .atom _ => 0
  | .top => 0
  | .bot => 0
  | .neg f => f.leftParens
  | .conj f g => 1 + f.leftParens + g.leftParens
  | .disj f g => 1 + f.leftParens + g.leftParens

def Form.rightParens : Form → Nat
  | .atom _ => 0
  | .top => 0
  | .bot => 0
  | .neg f => f.rightParens
  | .conj f g => 1 + f.rightParens + g.rightParens
  | .disj f g => 1 + f.rightParens + g.rightParens

theorem Form.leftParens_eq_rightParens (f : Form) :
    f.leftParens = f.rightParens := by
  induction f with
  | atom _ => rfl
  | top => rfl
  | bot => rfl
  | neg _ ih => exact ih
  | conj _ _ ih1 ih2 =>
    simp [Form.leftParens, Form.rightParens, ih1, ih2]
  | disj _ _ ih1 ih2 =>
    simp [Form.leftParens, Form.rightParens, ih1, ih2]

-- Vale notar o que a prova de fato estabelece: `Form` binário já garante um
-- parêntese de abertura por `conj`/`disj`, contado igualmente nas duas
-- funções por construção, de modo que a demonstração formaliza essa contagem
-- em vez de descobrir algo novo sobre a gramática.

-- A leitura única é o caso extremo dessa observação. Provar leitura única
-- para uma gramática dada como *string* exige indução estrutural genuína; em
-- Lean, um termo de `Form` já é a árvore, não uma string a analisar — não há
-- uma segunda leitura possível a excluir, e o exercício `unique-readability`,
-- acima, se reduz a `injection`.

-- ### Exercise (1 star): count-operators ⭐

-- Implemente uma função `opsNr` para contar o número de operadores de uma
-- fórmula. O tipo é `opsNr : Form → Nat`. A chamada `opsNr form1` deve dar
-- `2`.

def Form.opsNr : Form → Nat :=
  sorry

theorem opsNr_test : form1.opsNr = 2 := sorry

-- ### Exercise (1 star): formula-depth ⭐

-- Implemente uma função `depth` para calcular a profundidade da árvore de
-- análise de uma fórmula. O tipo é `depth : Form → Nat`. A chamada
-- `depth form1` deve dar `2`.

def Form.depth : Form → Nat :=
  sorry

theorem depth_test : form1.depth = 2 := sorry

-- ### Exercise (2 stars): collect-atoms ⭐⭐

-- Implemente `propNames : Form → List String` para coletar a lista de nomes
-- de átomos proposicionais que ocorrem numa fórmula. A lista resultante deve
-- estar ordenada e sem repetições.

private def Form.propNamesRaw : Form → List String :=
  sorry

def Form.propNames (f : Form) : List String :=
  sorry

#eval form1.propNames

-- ["p"]

#eval form2.propNames

-- ["p1", "p2", "p3", "p4"]

-- ### Semântica

-- A primeira questão a enfrentar na semântica da lógica proposicional é:
-- quais são as estruturas extralinguísticas de que as fórmulas da lógica
-- proposicional tratam? Nossa resposta é: informação sobre a verdade ou
-- falsidade das proposições atômicas. Essa resposta é codificada nas chamadas
-- **valorações**, funções do conjunto dos átomos para o conjunto `{0, 1}` dos
-- valores de verdade.

-- Aqui uma valoração é uma lista de pares, e um átomo ausente da lista conta
-- como falso.

abbrev Valuation := List (String × Bool)

-- Se `V` é uma valoração, ela se estende a uma função de todas as fórmulas
-- para os valores de verdade. A extensão é definida por recursão sobre a
-- estrutura da fórmula, um caso por construtor:

def Form.eval (f : Form) (v : Valuation) : Bool :=
  match f with
  | .atom name => (v.lookup name).getD false
  | .top => true
  | .bot => false
  | .neg g => !g.eval v
  | .conj g h => g.eval v && h.eval v
  | .disj g h => g.eval v || h.eval v

-- Os construtores `top` e `bot` são constantes: nenhuma valoração os afeta.

#eval form1.eval [("p", true)]

-- false

-- Outra maneira de apresentar a semântica dos conectivos proposicionais é por
-- meio de **tabelas de verdade**, que especificam como o valor de verdade de
-- uma fórmula complexa é calculado a partir dos valores de verdade de seus
-- componentes.

-- F₁  F₂    ¬F₁    F₁ ∧ F₂    F₁ ∨ F₂    F₁ → F₂    F₁ ↔ F₂
-- 1   1      0        1          1          1          1
-- 1   0      0        0          1          0          0
-- 0   1      1        0          1          1          0
-- 0   0      1        0          0          1          1

-- Não é difícil ver que há fórmulas cujo valor não depende da valoração. As
-- fórmulas que valem 1 para toda valoração são chamadas de **tautologias**; a
-- notação usual para "F é uma tautologia" é `⊨ F`. As fórmulas que valem 0
-- para toda valoração são chamadas de **contradições**.

-- Uma fórmula é **satisfatível** se há ao menos uma valoração que a torna
-- verdadeira, e é **contingente** se é satisfatível mas não é uma tautologia.
-- Toda tautologia é satisfatível, mas nem toda fórmula satisfatível é uma
-- tautologia.

-- Para decidir isso basta percorrer todas as valorações relevantes — e são
-- finitas, porque uma fórmula tem finitos átomos. A função a seguir gera a
-- lista de todas as valorações sobre um conjunto de nomes.

def genVals : List String → List Valuation
  | [] => [[]]
  | name :: names =>
      (genVals names).map ((name, true) :: ·)
      ++ (genVals names).map ((name, false) :: ·)

def Form.allVals (f : Form) : List Valuation :=
  genVals f.propNames

#eval form1.allVals

-- [[("p", true)], [("p", false)]]

-- Com isso, as três noções são imediatas.

def Form.tautology (f : Form) : Bool :=
  f.allVals.all (fun v => f.eval v)

def Form.satisfiable (f : Form) : Bool :=
  f.allVals.any (fun v => f.eval v)

def Form.contradiction (f : Form) : Bool :=
  !f.satisfiable

#eval (form1.contradiction,
       (Form.neg form1).tautology,
       form2.satisfiable)

-- (true, true, true)

-- Duas fórmulas `F₁` e `F₂` são **logicamente equivalentes** se têm o mesmo
-- valor sob toda valoração; a notação é `F₁ ≡ F₂`. Segue da definição que
-- todas as tautologias são logicamente equivalentes entre si, e o mesmo vale
-- para as contradições.

-- Fórmulas `P₁, …, Pₙ` **implicam logicamente** a fórmula `C` (`P` de
-- premissa, `C` de conclusão) se toda valoração que torna verdadeiros todos
-- os membros de `P₁, …, Pₙ` também torna `C` verdadeira. A notação é
-- `P₁, …, Pₙ ⊨ C`.

-- Disso sai uma caracterização que dispensa quantificar sobre valorações duas
-- vezes: `F₁` implica `F₂` se e somente se `F₁ ∧ ¬F₂` é uma contradição.

def Form.implies (f g : Form) : Bool :=
  (Form.conj f (.neg g)).contradiction

def Form.equivalent (f g : Form) : Bool :=
  f.implies g && g.implies f

#eval (Form.implies (.atom "p")
         (.disj (.atom "p") (.atom "q")),
       Form.equivalent
         (.neg (.neg (.atom "p"))) (.atom "p"))

-- (true, true)

-- A semântica da lógica proposicional também pode ser dada em formato de
-- **atualização**. Fixe primeiro um conjunto de valorações relevantes: esse é
-- o estado corrente. Depois defina uma função de atualização que deixa apenas
-- as valorações que satisfazem uma dada fórmula.

def update (vals : List Valuation) (f : Form) :
    List Valuation :=
  vals.filter (fun v => f.eval v)

-- Atualizar o estado de todas as valorações relevantes com uma contradição
-- não deixa nada; atualizar com uma tautologia não tira nada.

#eval (update form1.allVals form1).length

-- 0

#eval (update form1.allVals (.neg form1)).length

-- 2

-- Atualizar com uma fórmula contingente tira alguma coisa, e atualizar com
-- sua negação tira o complemento.

#eval (form2.allVals.length,
       (update form2.allVals form2).length,
       (update form2.allVals (.neg form2)).length)

-- (16, 15, 1)

-- Essa é a imagem do conhecimento que cresce por eliminação de
-- possibilidades, que já apareceu no primeiro capítulo: cada afirmação aceita
-- corta o estado.

-- ### Exercise (1 star): valuation-table ⭐

-- Seja `V` dada por `p ↦ 0`, `q ↦ 1`, `r ↦ 1`. Dê os valores das fórmulas
-- seguintes: `¬p ∨ p`, `p ∧ ¬p`, `¬¬(p ∨ ¬r)`, `¬(p ∧ ¬r)`, `p ∨ (q ∧ r)`.

def vpqr : Valuation :=
  [("p", false), ("q", true), ("r", true)]

example :
    (Form.disj (.neg (.atom "p")) (.atom "p")).eval vpqr
      = true :=
  sorry

example :
    (Form.conj (.atom "p") (.neg (.atom "p"))).eval vpqr
      = false :=
  sorry

-- ### Exercise (1 star): negated-tautology ⭐

-- Explique por que a negação de uma tautologia é sempre uma contradição, e
-- vice-versa.

-- ### Exercise (2 stars): implies-list ⭐⭐

-- Estenda a checagem de implicação proposicional para o caso de uma lista de
-- premissas. O tipo é `Form.impliesL : List Form → Form → Bool`.

def Form.impliesL (ps : List Form) (c : Form) :
    Bool :=
  sorry

-- ### A ponte entre as duas leituras

-- O capítulo começou distinguindo raciocinar **em** lógica proposicional de
-- raciocinar **sobre** ela. As duas leituras convivem desde então: `p ∧ q` é
-- uma proposição, do tipo `Prop`, e `Form.conj p q` é um dado, do tipo
-- `Form`. Nada, até aqui, as liga.

-- A ligação é uma função que interpreta cada fórmula como a proposição que
-- ela afirma, dada uma valoração.

def Form.denote (f : Form) (v : Valuation) : Prop :=
  match f with
  | .atom name => (v.lookup name).getD false = true
  | .top => True
  | .bot => False
  | .neg g => ¬ g.denote v
  | .conj g h => g.denote v ∧ h.denote v
  | .disj g h => g.denote v ∨ h.denote v

-- Repare no que cada caso faz: ele troca um construtor de `Form` pelo
-- conectivo correspondente de `Prop`. O `conj` do dado vira o `∧` da
-- proposição, o `neg` vira o `¬`. É a mesma correspondência que a seção sobre
-- sintaxe e proposição pediu para não confundir — e é só aqui, com uma função
-- explícita entre as duas, que ela pode ser enunciada sem confusão.

-- O teorema que fecha o capítulo diz que as duas leituras concordam: computar
-- dá `true` exatamente quando a proposição vale.

theorem Form.eval_iff_denote (f : Form) (v : Valuation) :
    f.eval v = true ↔ f.denote v := by
  induction f with
  | atom name => simp [Form.eval, Form.denote]
  | top => simp [Form.eval, Form.denote]
  | bot => simp [Form.eval, Form.denote]
  | neg g ih =>
      simp only [Form.eval, Form.denote]
      rw [← ih]
      simp
  | conj g h ihg ihh =>
      simp [Form.eval, Form.denote, ihg, ihh]
  | disj g h ihg ihh =>
      simp [Form.eval, Form.denote, ihg, ihh]

-- A ponte também dá o que faltava para o exercício de tradução do começo do
-- capítulo. Traduzir bem é algo que se pode **conferir**: basta enunciar em
-- Lean a condição de verdade pretendida e exigir que a denotação da fórmula
-- coincida com ela. O teorema fecha por `Iff.rfl` — a denotação calcula, e o
-- que sobra dos dois lados é o mesmo termo.

theorem wizardOrLazy_means (v : Valuation) :
    wizardOrLazy.denote v ↔
      ((v.lookup "p").getD false = true
        ∧ (v.lookup "q").getD false = true)
      ∨ (v.lookup "r").getD false = true :=
  Iff.rfl

-- É esse teorema, e não a fórmula sozinha, que responde à pergunta "as
-- condições de verdade foram capturadas?" — a fórmula é uma proposta, e o
-- teorema é a verificação.

-- A prova é indução estrutural sobre a fórmula, com um caso por construtor —
-- a mesma indução que o recursor de `Form` já dava. Em cada caso a hipótese
-- de indução vale para as subfórmulas, e o que resta é conferir que o
-- conectivo booleano e o conectivo proposicional concordam.

-- Vale notar onde a lógica clássica entra. A valoração devolve `Bool`, que
-- tem exatamente dois habitantes; a denotação devolve `Prop`, onde a
-- decidibilidade não é dada. O teorema acima diz que, para as fórmulas desta
-- linguagem, as duas coincidem — ou seja, a semântica de dois valores é
-- clássica por construção, e é por isso que a discussão sobre o terceiro
-- excluído, no começo do capítulo, não reaparece aqui.

end PL

-- ## Lógica de predicados

namespace FOL

-- Frases como "Todo príncipe viu uma dama" não se relacionam em lógica
-- proposicional — ficariam como átomos `p`/`q` totalmente desconectados, sem
-- capturar que a mesma noção de "príncipe" e "viu" está em jogo nas duas.
-- Lógica de predicados acrescenta três ingredientes à proposicional:

-- - uma proposição básica estruturada, um predicado `n`-ário seguido de `n`
--   variáveis;

-- - uma fórmula universalmente quantificada, `∀` seguido de variável e fórmula;

-- - uma fórmula existencialmente quantificada, `∃` seguido de variável e
--   fórmula.

-- Por isso o outro nome, "lógica de primeira ordem" — a quantificação é sobre
-- entidades, objetos de primeira ordem. O livro assume predicados de aridade
-- até 3 (relações unárias, binárias e ternárias — a última para verbos como
-- "dar", com sujeito, objeto e destinatário): "relações com mais de três
-- argumentos quase nunca são necessárias". A BNF completa (usando primos para
-- gerar infinitas variáveis e infinitos predicados de cada aridade, como na
-- lógica proposicional):

-- v    ::= "x" | "y" | "z" | v "′" ;
-- P    ::= "P" | P "′" ;
-- R    ::= "R" | R "′" ;
-- S    ::= "S" | S "′" ;
-- atom ::= P v | R v v | S v v v ;
-- F    ::= atom
--   | "(" v "=" v ")" ("identidade")
--   | "¬" F ("negação")
--   | "(" F "∧" F ")" ("conjunção")
--   | "(" F "∨" F ")" ("disjunção")
--   | "∀" v F ("quantificação universal")
--   | "∃" v F ("quantificação existencial") ;

-- gerando fórmulas como `¬P′x`, `∀xRxx` ("tudo mantém a relação `R` consigo
-- mesmo") e `∀x∃x′Rxx′` ("para todo primeiro há algo que é `R`-ado por ele").

-- ### As regras dos quantificadores

-- Como no capítulo proposicional, duas leituras convivem aqui: os
-- quantificadores do próprio Lean, com que se enuncia e demonstra, e as
-- fórmulas como dado, que é o que `Formula` será. Esta seção é sobre os
-- primeiros, e são duas regras novas — uma para cada quantificador. O domínio
-- dos exemplos é um tipo de três elementos, `Node`, que a seção sobre
-- semântica retoma como domínio de um modelo.

inductive Node where
  | one | two | three
  deriving DecidableEq, Repr

-- A introdução de `∀` diz: para provar que algo vale de todo `x`, tome um `x`
-- arbitrário e prove que vale dele. É `intro` de novo, agora sobre um objeto
-- em vez de uma hipótese.

example (P : Node → Prop) (h : ∀ x, P x) : ∀ y, P y := by
  intro y
  exact h y

-- A eliminação de `∀` é aplicação: de `∀x P x` e de um objeto `d`, sai `P d`.
-- É o `h y` da prova acima.

-- A introdução de `∃` exige exibir a testemunha. A tática `use` faz isso —
-- ela substitui a variável quantificada pelo objeto que se oferece, e deixa
-- como objetivo o que falta provar sobre ele.

example : ∃ x : Node, x = Node.two := by
  use Node.two

-- A eliminação de `∃` é a mais delicada, e pelo mesmo motivo que a de `∨`: de
-- `∃x P x` sabe-se que há uma testemunha, mas não qual. A tática `obtain` a
-- introduz com um nome, junto com a propriedade que ela satisfaz.

example (P Q : Node → Prop)
    (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨d, hP, hQ⟩ := h
  exact ⟨d, hQ⟩

-- Com as duas regras, a validade que a seção anterior enunciou — que de `∀xF`
-- segue `∃xF` quando o domínio é não vazio — pode ser demonstrada, e não
-- apenas afirmada. A não vacuidade do domínio entra como a hipótese
-- `d : Node`, isto é, como a exibição de um habitante.

example (P : Node → Prop) (d : Node)
    (h : ∀ x, P x) : ∃ x, P x :=
  ⟨d, h d⟩

-- Repare que num domínio vazio a prova não existiria: não há testemunha a
-- oferecer. É a mesma exigência que o modelo faz, agora visível no tipo.

-- ### Exercise (2 stars): forall-exists-swap ⭐⭐

-- Uma das duas direções vale, a outra não. Prove a que vale.

example (R : Node → Node → Prop) (h : ∃ y, ∀ x, R x y) :
    ∀ x, ∃ y, R x y := sorry

-- ### Ligação de variáveis

-- Numa fórmula `∀xF` (ou `∃xF`), o quantificador liga toda ocorrência de `x`
-- em `F` que não esteja já ligada por um `∀x`/`∃x` interno a `F`. Uma fórmula
-- é **aberta** se tem ao menos uma ocorrência livre de variável, e
-- **fechada** (também chamada **sentença**) caso contrário. Por exemplo,
-- `(Px ∧ ∃xRxx)` é aberta — o `x` de `Px` está fora do escopo do `∃x` — mas
-- `∃x(Px ∧ ∃xRxx)` é uma sentença.

-- Essa distinção é o que motiva a ambiguidade de escopo de *"Todo príncipe
-- viu uma dama"*: duas leituras, "para cada príncipe existe uma dama (talvez
-- diferente) que ele viu" contra "existe uma dama que todo príncipe viu",
-- formalizadas respectivamente como

-- ∀x(Prince x → ∃y(Lady y ∧ Saw x y))
-- ∃y(Lady y ∧ ∀x(Prince x → Saw x y))

-- — repare que a leitura universal usa `→` como conectivo principal, e a
-- existencial usa `∧`; vale a pena perguntar por quê — o assunto volta com a
-- semântica. Já *"Algum príncipe viu uma dama bonita"* não é ambígua:
-- `∃x∃y(Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.

-- ### Exercise (2 stars): predicate-unique-readability ⭐⭐

-- Prove que as fórmulas desta língua têm a propriedade de leitura única.

-- ### Exercise (1 star): infinite-predicates-bnf ⭐

-- Dê uma gramática BNF para uma língua de lógica de predicados com infinitos
-- símbolos de predicado para cada aridade finita. (Dica: use `‴P`, `‴P′`,
-- `‴P″`, ... para o conjunto de predicados de três lugares, e assim por
-- diante.)

-- ### Exercise (1 star): bound-occurrences ⭐

-- Dê as ocorrências ligadas de `x` na fórmula seguinte.

-- ∃x(Rxy ∨ Sxyz) ∧ Px

-- ### Fórmulas de predicados em Lean

-- O "problema da aridade" (predicados de aridade 1, 2, 3, ... exigiriam um
-- `inductive` por aridade) se resolve como em linguagens como Prolog: um
-- predicado nomeado por `String`, aplicado a uma **lista** de termos — o
-- comprimento da lista já determina a aridade, sem precisar de um tipo por
-- aridade.

-- Uma variável carrega nome e um índice (lista de inteiros, para gerar
-- variáveis "frescas" a partir de uma dada — usadas quando a semântica
-- precisar renomear variáveis ligadas):

structure Variable where
  name : String
  index : List Nat
  deriving DecidableEq, Repr

def Variable.toStringImpl : Variable → String
  | ⟨name, []⟩ => name
  | ⟨name, [i]⟩ => name ++ toString i
  | ⟨name, is⟩ =>
    name ++ String.intercalate "_" (is.map toString)

instance : ToString Variable := ⟨Variable.toStringImpl⟩

def x : Variable := ⟨"x", []⟩
def y : Variable := ⟨"y", []⟩
def z : Variable := ⟨"z", []⟩

-- `Formula α` é parametrizado no tipo dos termos que preenchem os predicados
-- — por ora `α := Variable` (a seção sobre símbolos de função, adiante,
-- introduz `Term`, estruturado, e reaproveita `Formula` trocando o
-- parâmetro).

inductive Formula (α : Type) where
  | atom (name : String) (args : List α)
  | eq (t1 t2 : α)
  | top
  | bot
  | neg (f : Formula α)
  | impl (f1 f2 : Formula α)
  | equi (f1 f2 : Formula α)
  | conj (f1 f2 : Formula α)
  | disj (f1 f2 : Formula α)
  | forall_ (v : Variable) (f : Formula α)
  | exists_ (v : Variable) (f : Formula α)
  deriving Repr

-- A conjunção e a disjunção são binárias, e `top` e `bot` são construtores
-- próprios — o mesmo desenho do tipo das fórmulas proposicionais, pelo mesmo
-- motivo: um construtor que guardasse uma lista de fórmulas dentro do próprio
-- tipo o tornaria um indutivo *nested*, e com isso se perderiam `induction` e
-- `deriving`. O `α` em `atom name (args : List α)` não cria esse problema,
-- porque é parâmetro, não o próprio tipo.

-- A notação n-ária se recupera com duas funções, como lá: uma conjunção vazia
-- é `top`, uma disjunção vazia é `bot`.

def Formula.conjs {α : Type} : List (Formula α) → Formula α
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Formula.conjs fs)

def Formula.disjs {α : Type} : List (Formula α) → Formula α
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Formula.disjs fs)

-- E a instância de `ToString`:

def Formula.toStringImpl [ToString α] : Formula α → String
  | .atom name [] => name
  | .atom name args =>
    name ++ "[" ++
      String.intercalate "," (args.map toString) ++ "]"
  | .eq t1 t2 => s!"{t1}={t2}"
  | .neg f => s!"~{f.toStringImpl}"
  | .impl f1 f2 =>
    s!"({f1.toStringImpl}==>{f2.toStringImpl})"
  | .equi f1 f2 =>
    s!"({f1.toStringImpl}<=>{f2.toStringImpl})"
  | .top => "true"
  | .bot => "false"
  | .conj f1 f2 =>
    s!"({f1.toStringImpl}&{f2.toStringImpl})"
  | .disj f1 f2 =>
    s!"({f1.toStringImpl}|{f2.toStringImpl})"
  | .forall_ v f => s!"A{v} {f.toStringImpl}"
  | .exists_ v f => s!"E{v} {f.toStringImpl}"

instance [ToString α] : ToString (Formula α) :=
  ⟨Formula.toStringImpl⟩

def formula0 : Formula Variable := .atom "R" [x, y]

-- A instância acima recebe outra entre colchetes: para imprimir uma
-- `Formula α` é preciso saber imprimir os `α` que a preenchem, e o
-- `[ToString α]` é essa exigência. Uma instância pode assim depender de
-- outras, e o Lean encadeia a busca — dado `ToString Variable`, ele monta
-- sozinho `ToString (Formula Variable)`.

#eval toString formula0

-- "R[x,y]"

def formula1 : Formula Variable :=
  .forall_ x (.atom "R" [x, x])

#eval toString formula1

-- "Ax R[x,x]"

-- reflexividade de R

def formula2 : Formula Variable :=
  .forall_ x (.forall_ y
    (.impl (.atom "R" [x, y]) (.atom "R" [y, x])))

#eval toString formula2

-- "Ax Ay (R[x,y]==>R[y,x])"

-- simetria de R

-- ### Exercise (2 stars): closed-form ⭐⭐

-- Escreva uma função `closedForm : Formula Variable → Bool` que verifica se
-- uma fórmula é fechada. Comece por uma função que coleta a lista de
-- variáveis livres de uma fórmula: as fechadas são as que têm essa lista
-- vazia.

def freeVarsInFormula : Formula Variable → List Variable :=
  sorry

def closedForm (f : Formula Variable) : Bool :=
  sorry

-- ### Exercise (1 star): implication-as-abbrev ⭐

-- Implicações e equivalências podem ser vistas como abreviações, pois se
-- definem a partir de negação e conjunção. Escreva uma função
-- `withoutIDs : Formula Variable → Formula Variable` que substitui cada
-- fórmula por uma equivalente sem ocorrências de `impl` ou `equi`.

def withoutIDs : Formula Variable → Formula Variable :=
  sorry

-- ### Exercise (2 stars): negation-normal-form ⭐⭐

-- Toda fórmula de lógica de predicados é equivalente a uma fórmula em **forma
-- normal negativa**, onde negações só ocorrem diante de átomos. A receita é
-- "empurrar" as negações através dos quantificadores por `¬∀xF ≡ ∃x¬F` e
-- `¬∃xF ≡ ∀x¬F`, e através de disjunções e conjunções pelas leis de De
-- Morgan: `¬(F1 ∧ F2) ≡ ¬F1 ∨ ¬F2` e `¬(F1 ∨ F2) ≡ ¬F1
-- ∧ ¬F2`. `¬¬F ≡ F`
-- elimina dupla negação. Escreva uma função
-- `nnf :
-- Formula Variable → Formula Variable` que transforma uma fórmula em
-- forma normal negativa. (Dica: use a função do exercício anterior para
-- eliminar `impl`/`equi` primeiro.)

-- **Cuidado ao implementar** (dica de verdade, não parte da nota de rodapé):
-- uma função `nnf`/`nnfNeg` mutuamente recursivas, com `nnfNeg` chamando
-- `nnfNeg (withoutIDs ...)` nos casos de `impl`/`equi`, não termina por
-- recursão estrutural — o Lean não consegue provar que `withoutIDs f` é
-- "menor" que `f` (em geral não é: `withoutIDs` pode crescer o termo).
-- Aplicar `withoutIDs` uma única vez, no início, resolve — mas então as
-- funções internas ainda precisam cobrir os casos `impl`/`equi`, mesmo que
-- nunca sejam de fato alcançados depois desse passo.

def nnf : Formula Variable → Formula Variable := sorry

-- ### Símbolos de função

-- Lógica de predicados, como definida até aqui, não expressa equações de
-- aritmética escolar: um termo como `(5 + 3) × 4` é complexo, não uma
-- variável isolada. A solução é introduzir **constantes de função** para
-- operações arbitrárias — o mesmo movimento de nomear relações binárias
-- arbitrárias em vez de fixar "menor que" como primitivo.

-- Termos complexos, com símbolo de função e lista de argumentos — outro
-- `inductive` nested (a lista de `Term` dentro do próprio `Term`), então sem
-- `deriving DecidableEq`/`induction`, como `Form` teria sido se a gramática
-- da lógica proposicional não fosse binária:

inductive Term where
  | var (v : Variable)
  | struct (name : String) (args : List Term)

def Term.toStringImpl : Term → String
  | .var v => toString v
  | .struct name [] => name
  | .struct name args =>
    name ++ "[" ++
      String.intercalate ","
        (args.map Term.toStringImpl) ++ "]"

instance : ToString Term := ⟨Term.toStringImpl⟩

def tx : Term := .var x
def ty : Term := .var y
def tz : Term := .var z

-- Um termo **livre para** uma variável `v` numa fórmula `F` é um termo que,
-- substituído em toda ocorrência livre de `v` em `F`, não tem nenhuma de suas
-- próprias variáveis capturada por um quantificador de `F`. Substituir sem
-- essa cautela muda o significado: em `(∀yRxy →
-- ∀xRxx)`, o `x` livre da
-- premissa, substituído por `y`, produz `(∀yRyy → ∀xRxx)` — o `y` do termo
-- foi capturado pelo `∀y` que já estava lá. Uma **variante alfabética** (a
-- mesma fórmula, só renomeando variáveis ligadas — aqui, `(∀zRxz → ∀xRxx)`)
-- evita a captura.

-- Com `Term`, `Formula Term` são fórmulas com termos estruturados — o
-- semântica, daqui em diante, usa esse `Formula Term`, não mais
-- `Formula
-- Variable`.

def isVar : Term → Bool
  | .var _ => true
  | .struct _ _ => false

mutual
def varsInTerm : Term → List Variable
  | .var v => [v]
  | .struct _ ts => varsInTerms ts

def varsInTerms : List Term → List Variable
  | [] => []
  | t :: ts => varsInTerm t ++ varsInTerms ts
end

-- O bloco `mutual` aparece aqui pela primeira vez. Ele agrupa definições que
-- se chamam umas às outras: `varsInTerm` chama `varsInTerms` na segunda
-- linha, e `varsInTerms` chama `varsInTerm` na sua. Definidas separadamente,
-- a primeira mencionaria um nome que ainda não existe. Dentro de um `mutual`,
-- o Lean elabora as duas ao mesmo tempo e verifica juntas a terminação — a
-- recursão diminui o termo a cada volta, mesmo alternando entre as duas
-- funções.

-- A necessidade vem da forma do dado: um `Term` carrega uma `List Term`,
-- então percorrer um termo é percorrer uma lista de termos, e vice-versa.
-- Onde os tipos se referem uns aos outros, as funções sobre eles também se
-- referem — e no fragmento de inglês, mais adiante no livro, gramáticas
-- inteiras serão declaradas assim.

-- ### Exercise (1 star): term-parse-tree ⭐

-- Dê uma árvore de análise para o termo `f″[f′[x, y], f‴[z, z, f[x]]]`.

-- ### Exercise (1 star): vars-in-formula ⭐

-- Implemente uma função `varsInForm : Formula Term → List Variable` que dá a
-- lista de variáveis que ocorrem numa fórmula.

def varsInForm : Formula Term → List Variable := sorry

-- ### Exercise (2 stars): open-form ⭐⭐

-- Implemente `freeVarsInForm : Formula Term → List Variable`, que dá a lista
-- de variáveis com ocorrências livres numa fórmula, e sobre ela
-- `openForm : Formula Term → Bool`, que verifica se uma fórmula é aberta (ver
-- a seção sobre ligação de variáveis).

def freeVarsInForm : Formula Term → List Variable := sorry

def openForm (f : Formula Term) : Bool :=
  sorry

-- ### Semântica da lógica de predicados

-- A semântica da lógica de predicados é estática de novo. Por conveniência,
-- nos limitamos a um fragmento de língua com apenas três letras de predicado:
-- `P`, de um lugar, `R`, de dois, e `S`, de três.

-- Como deve ser uma estrutura extralinguística para as constantes `P`, `R` e
-- `S`? Tal estrutura deve conter ao menos um domínio de discurso `D`, formado
-- por entidades individuais, com uma interpretação para `P`, para `R` e para
-- `S`. Essas interpretações são dadas por uma função `I`, que a cada nome de
-- predicado e a cada lista de elementos do domínio associa a afirmação de que
-- a relação vale entre eles.

abbrev Interp (D : Type) := String → List D → Prop

-- Um conjunto de símbolos de relação, com suas aridades, especifica uma
-- linguagem de lógica de predicados `L`. Uma estrutura `M = (D, I)`, formada
-- por um domínio não vazio `D` com uma função de interpretação para os
-- símbolos de relação de `L`, é chamada de **modelo** para `L`. Sempre
-- suporemos que o domínio de um modelo é não vazio.

-- Eis um modelo concreto, com domínio de três elementos. `P` vale de `1` e de
-- `3`; `R` relaciona `1` a `1` e a `2`, `2` a `2`, e `3` a `1` e a `2`.

def M : Interp Node
  | "P", [d] => d = .one ∨ d = .three
  | "R", [d, e] =>
      (d = .one ∧ (e = .one ∨ e = .two))
      ∨ (d = .two ∧ e = .two)
      ∨ (d = .three ∧ (e = .one ∨ e = .two))
  | _, _ => False

-- Dada uma estrutura com função de interpretação `M = (D, I)`, podemos
-- definir uma valoração para as fórmulas da lógica de predicados, desde que
-- saibamos lidar com os valores das variáveis individuais. Seja `V` o
-- conjunto das variáveis da linguagem. Uma função `g : V → D` é chamada de
-- **atribuição de variáveis**, ou valoração.

-- Escrevemos `g[v := d]` para a valoração que é como `g` exceto pelo fato de
-- que `v` recebe o valor `d` — onde `g` poderia ter atribuído um valor
-- diferente.

def Assign (D : Type) := Variable → D

def Assign.update {D : Type} (g : Assign D)
    (v : Variable) (d : D) : Assign D :=
  fun w => if w = v then d else g w

-- Seja `M` um modelo para a linguagem `L`, seja `g` uma atribuição de
-- variáveis para `L` em `M`, e seja `F` uma fórmula de `L`. Estamos prontos
-- para definir a noção `M ⊨ᵍ F`, "F é verdadeira em M sob a atribuição g",
-- ou: "g satisfaz F no modelo M".

-- O que segue é uma definição recursiva de verdade para as fórmulas da lógica
-- de predicados. As cláusulas dos quantificadores são as que fazem a
-- atribuição mudar: `∀v F` vale quando `F` vale para toda escolha de valor de
-- `v`, e `∃v F` quando vale para ao menos uma.

def Formula.holds {D : Type} (I : Interp D)
    (g : Assign D) : Formula Variable → Prop
  | .atom name args => I name (args.map g)
  | .eq t1 t2 => g t1 = g t2
  | .top => True
  | .bot => False
  | .neg f => ¬ Formula.holds I g f
  | .impl f1 f2 =>
      Formula.holds I g f1 → Formula.holds I g f2
  | .equi f1 f2 =>
      Formula.holds I g f1 ↔ Formula.holds I g f2
  | .conj f1 f2 =>
      Formula.holds I g f1 ∧ Formula.holds I g f2
  | .disj f1 f2 =>
      Formula.holds I g f1 ∨ Formula.holds I g f2
  | .forall_ v f =>
      ∀ d : D, Formula.holds I (g.update v d) f
  | .exists_ v f =>
      ∃ d : D, Formula.holds I (g.update v d) f

-- Um caso por construtor, e cada caso troca o construtor pelo conectivo
-- correspondente do Lean — a mesma correspondência que o capítulo
-- proposicional enuncia como ponte entre as duas leituras.

-- Se avaliamos fórmulas fechadas, isto é, sem variáveis livres, a atribuição
-- `g` se torna irrelevante.

-- A definição de verdade faz uso essencial das atribuições e, ainda assim,
-- nos exercícios em que se olha apenas para fórmulas fechadas, a verdade ou a
-- falsidade não depende de qual atribuição se use. Poder-se-ia pensar,
-- portanto, que é possível dispensar as atribuições por completo, contanto
-- que nos limitemos a definir os valores de verdade das fórmulas fechadas da
-- lógica de predicados.

-- O problema é que, ao aplicar a definição de verdade acima a uma sentença,
-- por exemplo a `∀x(Px → ∃yRxy)`, a cláusula que trata do quantificador
-- universal faz referência à noção de verdade para a fórmula `(Px → ∃yRxy)`,
-- que é uma fórmula aberta. Para determinar se ela é verdadeira temos de
-- saber que objeto `x` denota. A situação é inteiramente análoga à
-- interpretação de sentenças de língua natural:

-- Todo mestre tem um aprendiz.
-- Ele tem um aprendiz.

-- Para determinar a verdade da segunda temos de saber quem é o referente do
-- pronome *ele*.

-- Uma sentença da lógica de predicados é **logicamente válida** se é
-- verdadeira em todo modelo; a notação é `⊨ F`. Da convenção de que os
-- domínios de nossos modelos são sempre não vazios segue que `⊨ ∀xF → ∃xF`,
-- para toda `F` com no máximo a variável `x` livre.

-- Uma sentença `C` **se segue logicamente** de uma sentença `P` (`P` de
-- premissa, `C` de conclusão; dizemos também que `P` implica logicamente `C`)
-- se todo modelo que torna `P` verdadeira também torna `C` verdadeira. A
-- notação é `P ⊨ C`.

-- Como julgar afirmações da forma `P ⊨ C`? É claro como podemos refutá-la:
-- achando um contraexemplo. Um contraexemplo a `P ⊨ C` é um modelo `M` com
-- `M ⊨ P` mas não `M ⊨ C`.

-- ### Exercise (2 stars): quantifier-strength ⭐⭐

-- Mostre que `∀x(Ax ∧ Bx)` significa algo mais forte que "todo A é B", e que
-- `∃x(Ax → Bx)` significa algo mais fraco que "algum A é B".

-- ### Exercise (2 stars): translate-quantified ⭐⭐

-- Traduza as sentenças a seguir para lógica de predicados, garantindo que as
-- condições de verdade sejam capturadas.

-- 1. *Someone walks and someone talks.*
-- 2. *No wizard cast a spell or mixed a potion.*
-- 3. *Every ballad that is sung by a princess is beautiful.*
-- 4. *If a knight finds a dragon, he fights it.*

def someoneWalksAndTalks : Formula Variable :=
  sorry

def noWizardCastOrMixed : Formula Variable :=
  sorry

def everyBalladBeautiful : Formula Variable :=
  sorry

def knightFightsDragon : Formula Variable :=
  sorry

-- A fórmula é uma proposta; a verificação é mostrar que ela afirma o que se
-- queria. `Formula.holds` leva uma fórmula à proposição que ela afirma, dada
-- uma interpretação, então basta enunciar a condição de verdade pretendida
-- com os quantificadores do próprio Lean e exigir que as duas coincidam. Como
-- `holds` calcula, cada teorema fecha por `Iff.rfl`.

theorem someoneWalksAndTalks_means {D : Type}
    (I : Interp D) (g : Assign D) :
    Formula.holds I g someoneWalksAndTalks ↔
      ((∃ d : D, I "Walk" [d]) ∧ (∃ d : D, I "Talk" [d])) :=
  sorry

theorem knightFightsDragon_means {D : Type}
    (I : Interp D) (g : Assign D) :
    Formula.holds I g knightFightsDragon ↔
      (∀ a : D, ∀ b : D,
        I "Knight" [a] ∧ I "Dragon" [b] ∧ I "Finds" [a, b] →
        I "Fights" [a, b]) :=
  sorry

-- O segundo é o que torna a discussão abaixo verificável: a força universal
-- dos indefinidos não é uma opinião sobre a tradução, é o que o `∀` do lado
-- direito diz, e o `Iff.rfl` confirma que a fórmula proposta diz o mesmo.

-- ### Exercise (2 stars): valid-consequence ⭐⭐

-- Quais das afirmações seguintes valem? Se uma vale, explique por quê; se
-- não, dê um contraexemplo.

-- 1. `∀xPx ⊨ ∃xPx`
-- 2. `∃x∃yRxy ⊨ ∃xRxx`
-- 3. `∃y∀xRxy ⊨ ∀x∃yRxy`

end FOL

