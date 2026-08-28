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

-- ### Sintaxe

-- Na BNF a seguir, as letras proposicionais são os `atom`, podemos predefinir
-- um certo conjunto de letras como válidas ou um processo de geração de
-- âtomos válidos com o sufixo `'`.

-- atom ::= "p" | "q" | "r" | atom"'" ;
-- F    ::= atom
--   | "¬" F ("negação")
--   | "(" F "∧" F ")" ("conjunção")
--   | "(" F "∨" F ")" ("dijunção") ;

-- gerando fórmulas como `¬¬¬p'''`, `((p ∨ p') ∧ p')`, `(p ∧ (p' ∧ p'''))`.
-- Sem parênteses a gramática é ambígua — `p ∧ p′ ∨ p″` lê-se tanto como
-- `(p ∧ p′) ∨ p″` quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural
-- afeta o significado, como na sentença em português "era jovem e bonita ou
-- triste".

-- A lista infinita de átomos (`p, q, r, p', q', ...`) se traduz melhor em
-- Lean como um átomo com nome (`String`), não como uma enumeração de
-- símbolos. Então ao invés de infinitas letras proposicionais usamos qualquer
-- string como um átomo.

-- Mantemos a cojunção e dijunção na forma binária ao pé da letra porque, em
-- Lean, uma lista custa caro. Um `inductive` com `List Form` dentro de si
-- mesmo (`Cnj (fs : List Form)`) é *nested*, e perde tanto
-- `deriving DecidableEq` quanto a tática `induction` (que os Exercícios
-- 4.11/4.15 pedem, mais adiante).

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
-- Diferente de um átomo de nome `"⊤"` (que a valoração do capítulo 5,
-- `(String → Bool) → Form → Bool`, poderia mandar para `false`, dependendo da
-- atribuição de átomos), `top`/`bot` são construtores próprios: a valoração
-- vai tratá-los como constantes, sempre `true`/`false`, sem depender de
-- nenhuma atribuição — por isso a conjunção vazia imprime `"true"` e a
-- disjunção vazia `"false"` (ver `toStringPolish` abaixo).

-- Notação n-ária recuperada por duas funções, para os capítulos 5–7 (uma
-- conjunção/disjunção quase sempre de dois elementos, e uma única vez com
-- mais — `lfDET The`, no capítulo 8):

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

#eval toString form1

-- "&[p,-p]"

def form2 : Form :=
  .disj (.atom "p1")
    (.disj (.atom "p2") (.disj (.atom "p3") (.atom "p4")))

#eval toString form2

-- "v[p1,v[p2,v[p3,p4]]]"

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

-- ### Exercise (1 star): 4.9 ⭐

-- Ref. CSwFP/4, exercício 4.9 (p. 74).

-- Traduza as sentenças a seguir para lógica proposicional, garantindo que as
-- condições de verdade sejam capturadas. Que limitações você encontra?

-- 1. *The wizard polishes his wand and learns a new spell, or he is lazy.*
-- 2. *The peasant will deal with the devil only if he has a plan to outwit him.*
-- 3. *If neither unicorns nor dragons exist, then neither do goblins.*

def ex49_1 : Form :=
  sorry
def ex49_2 : Form :=
  sorry
def ex49_3 : Form :=
  sorry

-- ### Exercise (1 star): 4.10 ⭐

-- Ref. CSwFP/4, exercício 4.10 (p. 74).

-- O conectivo `∨` é inclusivo: `p ∨ q` é verdadeiro mesmo quando `p` e `q`
-- são ambos verdadeiros. Em português, "ou" costuma ser exclusivo, como em
-- "Você pode ficar com o sorvete ou com o algodão-doce, mas não com os dois."
-- Defina um conectivo `⊕` para "ou exclusivo", usando os conectivos já
-- definidos.

def Form.xor (f g : Form) : Form :=
  sorry

-- ### Exercise (2 stars): 4.11 ⭐⭐

-- Ref. CSwFP/4, exercício 4.11 (p. 74).

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

-- O capítulo 3 definiu `abbrev S := Prop` — uma proposição semântica, sem
-- estrutura interna que se possa inspecionar. `Form`, acima, é um segundo
-- `inductive` de **sintaxe**: um valor de `Form` é dado, no sentido do
-- capítulo 2 — casa padrão, conta operadores, mede profundidade, coleta os
-- átomos que ocorrem nele (Exercícios 4.12–4.14, mais abaixo). Nada disso é
-- possível sobre um `Prop`: não há como perguntar "quantos `∧` tem esta
-- proposição" a um valor de tipo `Prop`, porque `Prop` não guarda a fórmula
-- que o provou, só se ela é verdadeira. A valoração `Form → Bool` — que dá
-- sentido a `Form` como lógica, e não só como árvore — chega no capítulo 5.

-- Há um terceiro objeto que responde à mesma pergunta ("o que é uma
-- fórmula?") de um jeito diferente: `Cslib.Logic.PL.Proposition` (biblioteca
-- `cslib`, já dependência deste projeto). Também é sintaxe — um `inductive`
-- de fórmulas —, mas o que se faz com ela é dedução natural (`Γ ⊢ A`), não
-- valoração. Três respostas, três pontos de vista: `Prop` é a proposição em
-- si, sem estrutura; `Proposition` do `cslib` é sintaxe mais um sistema de
-- prova; `Form` daqui é sintaxe mais uma função `Form → Bool`. Este capítulo
-- e o capítulo 5 seguem a terceira.

-- `Proposition` fica como leitura complementar, não como base do capítulo,
-- por um motivo de vocabulário: a BNF acima tem `¬`/`∧`/`∨` primitivos e
-- introduz `→` só depois, como abreviação; `Proposition` faz o caminho
-- inverso — `imp` é primitivo, `neg` deriva de `imp ·⊥`, exigindo uma
-- instância `[Bot Atom]` no tipo dos átomos que não tem motivação
-- linguística, só satisfaz a typeclass. Adotar `Proposition` obrigaria
-- `opsNr`/`depth` (Exercícios 4.12–4.13) a passar primeiro por essa tradução
-- de vocabulário, antes de bater com os números esperados. Quem quiser ver
-- como um curso de teoria da prova trataria fórmulas proposicionais em Lean,
-- com dedução natural completa, encontra em `Cslib.Logic.PL.Proposition`.

-- ### Indução estrutural

-- O Princípio da Indução Estrutural (Teorema 4.1 de CSwFP) diz: para provar
-- algo de toda fórmula, basta provar da base (átomos) e do passo indutivo
-- (que a propriedade passa por `¬`, `∧`, `∨`). Isso é necessário enunciar
-- como teorema separado quando se raciocina sobre fórmulas como *strings*; em
-- Lean não é um teorema a enunciar — é o recursor que `inductive Form` já
-- gera de graça:

#check @Form.rec

-- @Form.rec : {motive : Form → Sort u_1} →
--   ((name : String) → motive (Form.atom name)) →
--     motive Form.top →
--       motive Form.bot →
--         ((f : Form) → motive f → motive f.neg) →
--           ((f g : Form) → motive f → motive g → motive (f.conj g)) →
--             ((f g : Form) → motive f → motive g → motive (f.disj g)) → (t : Form) → motive t

-- `Form.rec` — e a tática `induction`, construída sobre ele — já **são** o
-- princípio de indução estrutural, sem que o capítulo precise declará-lo. A
-- Proposição 4.2 de CSwFP (número igual de parênteses em toda fórmula) e a
-- Proposição 4.3 (leitura única — o Exercício 4.11 acima é essa prova) viram,
-- aqui, só `induction`:

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

-- Essa é a Proposição 4.2 traduzida — mas com uma ressalva: `Form` binário já
-- garante um parêntese de abertura por `conj`/`disj`, contado igualmente nas
-- duas funções por construção; a prova formaliza essa contagem, não descobre
-- nada de novo sobre a gramática. A Proposição 4.3 e os Exercícios 4.11/4.15
-- (leitura única) são o caso mais extremo dessa observação: provar leitura
-- única para uma gramática dada como *string* exige indução estrutural
-- genuína; em Lean, um termo de `Form` já é a árvore, não uma string a
-- analisar — não há uma segunda leitura possível a excluir, e a prova
-- (Exercício 4.11 acima) se reduz a `injection`.

-- ### Exercise (1 star): 4.12 ⭐

-- Ref. CSwFP/4, exercício 4.12 (p. 75).

-- Implemente uma função `opsNr` para contar o número de operadores de uma
-- fórmula. O tipo é `opsNr : Form → Nat`. A chamada `opsNr form1` deve dar
-- `2`.

def Form.opsNr : Form → Nat :=
  sorry

theorem opsNr_test : form1.opsNr = 2 := sorry

-- ### Exercise (1 star): 4.13 ⭐

-- Ref. CSwFP/4, exercício 4.13 (p. 75).

-- Implemente uma função `depth` para calcular a profundidade da árvore de
-- análise de uma fórmula. O tipo é `depth : Form → Nat`. A chamada
-- `depth form1` deve dar `2`.

def Form.depth : Form → Nat :=
  sorry

theorem depth_test : form1.depth = 2 := sorry

-- ### Exercise (2 stars): 4.14 ⭐⭐

-- Ref. CSwFP/4, exercício 4.14 (p. 75).

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
-- gerar infinitas variáveis e infinitos predicados de cada aridade, como em
-- §4.4):

-- v    −→ x | y | z | v′
-- P    −→ P | P′
-- R    −→ R | R′
-- S    −→ S | S′
-- atom −→ P v | R v v | S v v v
-- F    −→ atom | (v = v) | ¬F | (F ∧ F) | (F ∨ F) | ∀v F | ∃v F

-- gerando fórmulas como `¬P′x`, `∀xRxx` ("tudo mantém a relação `R` consigo
-- mesmo") e `∀x∃x′Rxx′` ("para todo primeiro há algo que é `R`-ado por ele").

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
-- existencial usa `∧`; vale a pena perguntar por quê (retomamos isso no
-- Exercício 5.17). Já *"Algum príncipe viu uma dama bonita"* não é ambígua:
-- `∃x∃y(Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.

-- ### Exercício 4.15 (p. 77) ✎

-- Prove que as fórmulas desta língua têm a propriedade de leitura única.

-- **Resposta.** Como no Exercício 4.11 (§4.4): em Lean, um termo de tipo
-- indutivo *é* a árvore de análise — a prova é `injection` sobre os
-- construtores, não indução estrutural genuína sobre strings. Provar leitura
-- única para uma gramática dada como string exige mostrar que a função string
-- → árvore é bem definida (dá exatamente uma árvore, nunca duas ou nenhuma);
-- a versão Lean não tem essa função a definir, então a "leitura única" vira a
-- afirmação, quase vazia, de que construtores diferentes (ou o mesmo
-- construtor com argumentos diferentes) produzem termos diferentes —
-- exatamente o que `Form.noConfusion`/`injection` dão de graça para qualquer
-- `inductive`.

-- ### Exercício 4.16 (p. 77) ✎

-- Dê uma gramática BNF para uma língua de lógica de predicados com infinitos
-- símbolos de predicado para cada aridade finita. (Dica: use `‴P`, `‴P′`,
-- `‴P″`, ... para o conjunto de predicados de três lugares, e assim por
-- diante.)

-- **Resposta.** A gramática de lógica de predicados acima, estendida com um
-- prefixo de primos por aridade:

-- P0 −→ P0 | P0′        (predicados de aridade 0)
-- P1 −→ P1 | P1′        (predicados de aridade 1)
-- P2 −→ P2 | P2′        (predicados de aridade 2)
-- P3 −→ ‴P | ‴P′         (predicados de aridade 3)
-- ⋮

-- Em Lean, indexar por aridade é mais natural do que empilhar primos: um
-- `structure PredSymbol` com campos `name : String` e `arity : Nat` já
-- representa "infinitos predicados de cada aridade finita" sem precisar de
-- uma família de gramáticas, uma por aridade. Fica como observação —
-- `Formula` (abaixo) não adota `PredSymbol`, e limita a aridade por
-- construção (`atom`, `eq`, ...).

-- ### Exercício 4.17 (p. 78) ✎

-- Dê as ocorrências ligadas de `x` na fórmula seguinte.

-- ∃x(Rxy ∨ Sxyz) ∧ Px

-- **Resposta.** Duas: as duas ocorrências de `x` dentro do escopo do `∃x` (em
-- `Rxy` e em `Sxyz`). A terceira ocorrência de `x`, em `Px`, está fora do
-- escopo desse `∃x` — o parêntese fecha antes de `∧ Px` — e por isso é
-- **livre**, não ligada; a fórmula inteira é aberta. É o ponto fino do
-- exercício: uma mesma variável pode ter, na mesma fórmula, ocorrências
-- ligadas e uma ocorrência livre ao mesmo tempo, desde que estejam em
-- posições diferentes da árvore.

-- ### Fórmulas de predicados em Lean

-- O "problema da aridade" (predicados de aridade 1, 2, 3, ... exigiriam um
-- `inductive` por aridade) se resolve como em linguagens como Prolog: um
-- predicado nomeado por `String`, aplicado a uma **lista** de termos — o
-- comprimento da lista já determina a aridade, sem precisar de um tipo por
-- aridade.

-- Uma variável carrega nome e um índice (lista de inteiros, para gerar
-- variáveis "frescas" a partir de uma dada — usado a partir do capítulo 6):

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
-- — por ora `α := Variable` (o capítulo 4.7 introduz `Term`, estruturado, e
-- reaproveita `Formula` trocando o parâmetro).

inductive Formula (α : Type) where
  | atom (name : String) (args : List α)
  | eq (t1 t2 : α)
  | neg (f : Formula α)
  | impl (f1 f2 : Formula α)
  | equi (f1 f2 : Formula α)
  | conj (fs : List (Formula α))
  | disj (fs : List (Formula α))
  | forall_ (v : Variable) (f : Formula α)
  | exists_ (v : Variable) (f : Formula α)

-- Por que `Formula` toma lista de fórmulas (`conj`/`disj`), diferente do
-- `Form` binário de §4.4? Porque a conjunção/disjunção vazia — `conj []` como
-- `"true"`, `disj []` como `"false"` — é a motivação para tomar lista desde o
-- início, não uma escolha de implementação a evitar. `Form` binário funciona
-- bem porque §4.4 nunca precisa de conjunções de tamanho variável; aqui, a
-- conjunção/disjunção vazia como valor sensato (ver `toStringImpl` abaixo, e
-- a semântica do capítulo 5) depende da lista vazia existir.

-- Diferente do fragmento de inglês (§4.2) — onde `NP`/`VP`/`RCN`/`INF`/
-- `Sent` são **mutuamente recursivos**, mas nenhum toma lista de si mesmo, e
-- por isso mantêm `induction` funcionando — `Formula` é *nested*: a lista
-- `List (Formula α)` dentro do próprio tipo tira tanto `deriving DecidableEq`
-- quanto `induction` automática. É a mesma restrição que levou `Form` a ser
-- binário em §4.4; aqui a lista é essencial, então o custo se paga, e as
-- funções abaixo são recursão explícita.

-- `ToString` — inclusive a escolha de mostrar `conj []` como `"true"` e
-- `disj []` como `"false"` (a razão fica clara na semântica do capítulo 5:
-- são a base neutra de `∧`/`∨`, e como constantes independem de qualquer
-- atribuição de valores aos átomos):

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
  | .conj [] => "true"
  | .conj fs =>
    "(" ++
      String.intercalate " & "
        (fs.map Formula.toStringImpl) ++ ")"
  | .disj [] => "false"
  | .disj fs =>
    "(" ++
      String.intercalate " | "
        (fs.map Formula.toStringImpl) ++ ")"
  | .forall_ v f => s!"A{v} {f.toStringImpl}"
  | .exists_ v f => s!"E{v} {f.toStringImpl}"

instance [ToString α] : ToString (Formula α) :=
  ⟨Formula.toStringImpl⟩

def formula0 : Formula Variable := .atom "R" [x, y]

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

-- #### Exercício 4.18 (p. 81)

-- Escreva uma função `closedForm : Formula Variable → Bool` que verifica se
-- uma fórmula é fechada. (Dica: primeiro escreva uma função que coleta a
-- lista de variáveis livres de uma fórmula. As fórmulas fechadas são as que
-- têm lista de variáveis livres vazia.)

def freeVarsInFormula : Formula Variable → List Variable :=
  sorry

-- ### Exercise (1 star): 4.18-closedForm ⭐

-- A definição de `closedForm`, a partir de `freeVarsInFormula` acima (que
-- fica como exercício aberto).

def closedForm (f : Formula Variable) : Bool :=
  sorry

-- #### Exercício 4.19 (p. 82)

-- Implicações e equivalências podem ser vistas como abreviações, pois se
-- definem a partir de negação e conjunção. Escreva uma função
-- `withoutIDs : Formula Variable → Formula Variable` que substitui cada
-- fórmula por uma equivalente sem ocorrências de `impl` ou `equi`.

def withoutIDs : Formula Variable → Formula Variable :=
  sorry

-- #### Exercício 4.20 (p. 82)

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
-- de §4.4 não fosse binária:

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
-- capítulo 5 em diante usa esse `Formula Term`, não mais `Formula
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

-- #### Exercício 4.21 (p. 83) ✎

-- Dê uma árvore de análise para o termo `f″[f′[x, y], f‴[z, z, f[x]]]`.

-- **Resposta.** A árvore *é* o termo Lean correspondente — sem passo de
-- tradução a fazer:

def ex421Term : Term :=
  .struct "f2" [ .struct "f1" [tx, ty]
               , .struct "f3" [tz, tz, .struct "f" [tx]] ]

#eval toString ex421Term

-- "f2[f1[x,y],f3[z,z,f[x]]]"

-- f2
-- ├── f1
-- │   ├── x
-- │   └── y
-- └── f3
--     ├── z
--     ├── z
--     └── f
--         └── x

-- #### Exercício 4.22 (p. 84)

-- Implemente uma função `varsInForm : Formula Term → List Variable` que dá a
-- lista de variáveis que ocorrem numa fórmula.

def varsInForm : Formula Term → List Variable := sorry

-- #### Exercício 4.23 (p. 84)

-- Implemente

-- freeVarsInForm : Formula Term → List Variable

-- que dá a lista de variáveis com ocorrências livres numa fórmula.

def freeVarsInForm : Formula Term → List Variable := sorry

-- ### Exercise (1 star): 4.24 ⭐

-- Ref. CSwFP/4, exercício 4.24 (p. 84).

-- Implemente `openForm : Formula Term → Bool` que verifica se uma fórmula é
-- aberta (ver seção de ligação de variáveis).

-- A definição de `openForm`, a partir de `freeVarsInForm` acima (que fica
-- como exercício aberto).

def openForm (f : Formula Term) : Bool :=
  sorry

end FOL

