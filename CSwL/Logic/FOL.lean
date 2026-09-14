import Mathlib.Tactic.Use

-- # Lógica de predicados

namespace FOL

-- ## Introdução

-- Se usarmos lógica proposicional para formalizar a frase "Toda maça é
-- vermelha", teremos uma letra proposicional, um átomo indivisível que não
-- nos permitiria capturar a idéia do quantificador e da dependencia declarada
-- entre as *coisas* que são maças e a cor destas mesmas *coisas*. Lógica de
-- predicados acrescenta três ingredientes:

-- - termos para representar indivíduos de um domínio. Os termos poderão ser
--   variáveis ou funções aplicadas sobre termos;

-- - proposições básicas serão predicados `n`-ários sobre termos;

-- - fórmulas universalmente quantificadas, `∀` seguido de variável e fórmula;

-- - fórmulas existencialmente quantificadas, `∃` seguido de variável e fórmula.

-- ## Sintaxe de Lógica de Primeira Ordem

-- Também chamada de "lógica de primeira ordem" (FOL, "first order logic").
-- Vamos assumir que predicados terão aridade de 1 até 3 (relações unárias,
-- binárias e ternárias). Relações com mais de três argumentos quase nunca são
-- necessárias para capturar a semântica de linguagem natural. A BNF completa
-- segue abaixo e gera fórmulas como `¬P x`, `∀ x R x x` e `∀ x ∃ y R x y`.

-- v    ::= "x" | "y" | "z" | v "'" ;
-- P    ::= "P" | P "'" ;
-- R    ::= "R" | R "'" ;
-- S    ::= "S" | S "'" ;
-- atom ::= P v | R v v | S v v v ;
-- F    ::= atom
--   | "(" v "=" v ")" ("identidade")
--   | "¬" F ("negação")
--   | "(" F "∧" F ")" ("conjunção")
--   | "(" F "∨" F ")" ("disjunção")
--   | "∀" v F ("quantificação universal")
--   | "∃" v F ("quantificação existencial") ;

-- Em uma fórmula `∀x F` (ou `∃x F`), o quantificador liga toda ocorrência de
-- `x` em `F` que não esteja já ligada por um `∀x`/`∃x` interno a `F`. Uma
-- fórmula é **aberta** se tem ao menos uma ocorrência livre de variável, e
-- **fechada** (também chamada **sentença**) caso contrário. Por exemplo,
-- `(P x ∧ ∃x, R x x)` é aberta, o `x` de `P x` está fora do escopo do `∃x`.
-- Mas `∃x (P x ∧ ∃x R x x)` é uma sentença.

-- Essa distinção é o que motiva a ambiguidade de escopo de "Todo príncipe viu
-- uma dama". Duas leituras possíveis, "para cada príncipe existe uma dama
-- (talvez diferente) que ele viu" contra "existe uma dama que todo príncipe
-- viu", formalizadas respectivamente como:

-- ∀x (Prince x → ∃y (Lady y ∧ Saw x y))
-- ∃y (Lady y ∧ ∀x (Prince x → Saw x y))

-- Repare que a leitura universal usa `→` como conectivo principal, e a
-- existencial usa `∧`. Já "Algum príncipe viu uma dama bonita" admite apenas
-- uma formalização, `∃x∃y (Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.

-- Como fizemos em pl-syntax, vamos agora definir um tipo para representar
-- fórmulas FOL. Uma variável carrega nome e um índice (lista de naturais
-- usada para gerar variáveis "frescas" a partir de uma dada variável):

structure Variable where
  name : String
  index : List Nat
  deriving DecidableEq

def Variable.format : Variable → Std.Format
  | ⟨name, []⟩ => name
  | ⟨name, [i]⟩ => name ++ toString i
  | ⟨name, is⟩ =>
    name ++ String.intercalate "_" (is.map toString)

instance : Repr Variable := ⟨fun v _ => v.format⟩

def x : Variable := ⟨"x", []⟩
def y : Variable := ⟨"y", []⟩
def z : Variable := ⟨"z", []⟩

-- `Formula α` é parametrizado no tipo dos termos que preenchem os predicados
-- — por ora nossos termos são apenas `Variable`.

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

-- A conjunção e a disjunção são binárias, e `top` e `bot` são construtores
-- próprios — o mesmo que fizemos para as fórmulas proposicionais, pelo mesmo
-- motivo. O `α` em `atom` não cria esse problema, porque é parâmetro, não o
-- próprio tipo. A notação n-ária se recupera com as funções abaixo. Uma
-- conjunção vazia é `top`, uma disjunção vazia é `bot`, como fizemos em LP.

def Formula.conjs {α : Type} : List (Formula α) → Formula α
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Formula.conjs fs)

def Formula.disjs {α : Type} : List (Formula α) → Formula α
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Formula.disjs fs)

-- Um termo do tipo `Formula` não é muito legível, vamos implementar a
-- instância de `Repr` para controlar a exibição destes termos. Note que ela
-- demanda que o tipo `α` tenha também uma instância de `Repr`.

def Formula.format {α} [Repr α] : Formula α → Std.Format
  | .atom name [] => name
  | .atom name args =>
    name ++ "[" ++
      Std.Format.joinSep (args.map (repr ·)) ", " ++ "]"
  | .eq t1 t2 => f!"{repr t1} = {repr t2}"
  | .neg f => f!"~{f.format}"
  | .impl f1 f2 =>
    f!"({f1.format} ==> {f2.format})"
  | .equi f1 f2 =>
    f!"({f1.format} <=> {f2.format})"
  | .top => "true"
  | .bot => "false"
  | .conj f1 f2 =>
    f!"({f1.format} & {f2.format})"
  | .disj f1 f2 =>
    f!"({f1.format} | {f2.format})"
  | .forall_ v f => f!"A {repr v} {f.format}"
  | .exists_ v f => f!"E {repr v} {f.format}"

instance {α} [Repr α] : Repr (Formula α) :=
  ⟨fun f _ => f.format⟩

-- `Repr` é a classe que o `#eval` procura primeiro, e é por isso que basta
-- escrever `#eval formula0`. Ela devolve um `Std.Format`, e não uma `String`.
-- O segundo argumento que a instância ignora é a precedência.

-- A seguir, `formula1` expressa que o predicado `R` é reflexivo enquanto
-- `formula2` expressa que ele é simétrico.

def formula1 : Formula Variable :=
  .forall_ x (.atom "R" [x, x])

def formula2 : Formula Variable :=
  .forall_ x (.forall_ y
    (.impl (.atom "R" [x, y]) (.atom "R" [y, x])))

-- Coletar as variáveis livres de uma fórmula é uma operação que faremos mais
-- de uma vez, com termos de tipos diferentes. Definimos uma só vez, deixando
-- como parâmetro a função que extrai as variáveis de um termo — o que muda de
-- um caso para outro é apenas ela. Nos quantificadores, `filter` remove a
-- variável ligada, e remove **todas** as suas ocorrências.

def Formula.freeVars {α} (vars : α → List Variable) :
    Formula α → List Variable
  | .atom _ args => (args.map vars).flatten
  | .eq t1 t2 => vars t1 ++ vars t2
  | .top => []
  | .bot => []
  | .neg f => f.freeVars vars
  | .impl f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .equi f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .conj f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .disj f1 f2 => f1.freeVars vars ++ f2.freeVars vars
  | .forall_ v f => (f.freeVars vars).filter (· != v)
  | .exists_ v f => (f.freeVars vars).filter (· != v)

-- ### Exercise (2 stars): closed-form ⭐⭐

-- Escreva uma função `closedForm : Formula Variable → Bool` que verifica se
-- uma fórmula é fechada. Aqui cada termo é uma variável, então extrair as
-- variáveis de um termo é devolvê-lo numa lista de um elemento. As fórmulas
-- fechadas são as que têm a lista de livres vazia.

def freeVarsInFormula (f : Formula Variable) :
    List Variable :=
  sorry

def closedForm (f : Formula Variable) : Bool :=
  sorry

-- ### Exercise (1 star): implication-as-abbrev ⭐

-- Implicações e equivalências podem ser vistas como abreviações, pois se
-- definem a partir de negação, conjunção e disjunção — as mesmas
-- equivalências usadas na lógica proposicional. Escreva uma função
-- `withoutIDs : Formula Variable → Formula Variable` que substitui cada
-- fórmula por uma equivalente sem ocorrências de `impl` ou `equi`.

def withoutIDs (frm : Formula Variable) :
    Formula Variable :=
  sorry

-- ### Exercise (2 stars): negation-normal-form ⭐⭐

-- Toda fórmula de lógica de predicados pode ser transformada em uma
-- equivalente na **forma normal da negação** (NNF, "negation normal form"),
-- onde negações só ocorrem diante de átomos. A receita é "empurrar" as
-- negações através dos quantificadores por `¬ ∀x F ≡  ∃x ¬F` e
-- `¬ ∃x F ≡ ∀x ¬F`, e através de disjunções e conjunções pelas leis de De
-- Morgan: `¬(F1 ∧ F2) ≡ ¬F1 ∨ ¬F2` e `¬(F1 ∨ F2) ≡ ¬F1 ∧ ¬F2`. Finalmente,
-- `¬¬F ≡ F` elimina dupla negação. Complete o código da função `nnf`.

-- Dica: a receita acima diz o que fazer com `¬` diante de alguma subfórmula.
-- Isso sugere duas funções, uma para cada situação em que uma subfórmula pode
-- aparecer. As duas se chamam mutuamente, e por isso vão num bloco `mutual`.

-- - `nnfPos f` devolve a NNF de `f`;
-- - `nnfNeg f` devolve a NNF de `¬f`.

-- Trate `impl` e `equi` diretamente nas duas funções, sem passar por
-- `withoutIDs`.

mutual
def nnfPos (frm : Formula Variable) : Formula Variable :=
 sorry

def nnfNeg (frm : Formula Variable) : Formula Variable :=
 sorry
end

def Formula.nnf (f : Formula Variable) : Formula Variable :=
  sorry

-- Termos denotam objetos do domínio, e diferentes termos podem denotar um
-- mesmo objeto como os termos `(5 + 3) × 4`, `8 × 4` e `32`. Para representar
-- termos mais complexos que apenas variáveis, a solução é introduzir símbolos
-- funcionais para as operações entre termos.

inductive Term where
  | var (v : Variable)
  | struct (name : String) (args : List Term)

def Term.format : Term → Std.Format
  | .var v => repr v
  | .struct name [] => name
  | .struct name args =>
    name ++ "[" ++
      Std.Format.joinSep
        (args.map Term.format) "," ++ "]"

instance : Repr Term := ⟨fun t _ => t.format⟩

def tx : Term := .var x
def ty : Term := .var y
def tz : Term := .var z

-- Um termo `t` é **livre para** a variável `v` na fórmula `F` se toda
-- ocorrência livre de `v` em `F` pode ser substituída por `t` sem que nenhuma
-- das variáveis de `t` fique ligada. Por exemplo, `y` é livre para `x` em
-- `Px → ∀x Px`, mas o mesmo termo não é livre para `x` em `∀y Rxy → ∀x Rxx`.
-- Da mesma forma, `g(x,y)` não é livre para `x` em `∀y Rxy → ∀x Rxx`.

-- Um termo livre para uma variável `v` pode ser substituído nas ocorrências
-- livres de `v` sem uma mudança não intencional de significado. Considere a
-- fórmula aberta `∀y Rxy → ∀x Rxx`. Se substituirmos a ocorrência livre de
-- `x` nessa fórmula por `y`, obtemos uma fórmula fechada `∀y Ryy → ∀x Rxx`.
-- Uma variável que originalmente era livre acabou capturada.

-- Se `t` não é livre para `v` em `F`, podemos sempre renomear as variáveis
-- ligadas de `F` para garantir que a substituição de `t` por `v` em `F` tenha
-- o significado correto. Embora `g(y,c)` não seja livre para `x` em
-- `∀y Rxy → ∀x Rxx`, o termo é livre para `x` em `∀z Rxz → ∀x Rxx`, que é uma
-- chamada **variante alfabética** da fórmula original. Uma variante
-- alfabética de uma fórmula é uma fórmula que difere da original apenas por
-- usar variáveis ligadas diferentes.

-- A função `isVar` verifica se um termo é uma variável. As funções
-- `varsInTerm` e `varsInTerms` retornam as variáveis que ocorrem num termo ou
-- numa lista de termos sem duplicatas.

def isVar : Term → Bool
  | .var _ => true
  | .struct _ _ => false

mutual
def varsInTerm : Term → List Variable
  | .var v => [v]
  | .struct _ ts => varsInTerms ts

def varsInTerms (ts : List Term) : List Variable :=
  ts.map varsInTerm |>.flatten |>.eraseDups

end

-- Agora que temos o tipo `Term` podemos usar `Formula Term` ao invés de
-- `Formula Variable`.

-- ### Exercise (1 star): vars-in-formula ⭐

-- Implemente uma função `varsInForm : Formula Term → List Variable` que dá a
-- lista de variáveis que ocorrem numa fórmula. Aqui não se trata de
-- ocorrências **livres**: conte todas, inclusive a variável que cada
-- quantificador liga. Mantenha a lista sem duplicatas, como fazem
-- `varsInTerm` e `varsInTerms`.

def Formula.varsInForm (frm : Formula Term) : List Variable :=
  sorry

-- ### Exercise (2 stars): free-vars-in-formula ⭐⭐

-- Implemente `freeVarsInForm : Formula Term → List Variable`, que dá a lista
-- de variáveis com ocorrências livres numa fórmula.

def Formula.freeVarsInForm (f : Formula Term) : List Variable :=
  sorry

-- ### Exercise (2 stars): open-form ⭐⭐

-- Usando a função `freeVarsInForm`, complete a função `openForm`, que
-- verifica se uma fórmula é aberta. Reaproveite as funções anteriores.

def openForm (f : Formula Term) : Bool :=
  sorry

-- ## Semântica da lógica de predicados

-- Por conveniência, nos limitamos a um fragmento de língua com apenas três
-- letras de predicado: `P` (unário), `R` (binário), e `S` (ternário).

-- Como deve ser uma estrutura extralinguística para as constantes `P`, `R` e
-- `S`? Tal estrutura deve conter ao menos um domínio de discurso `D`, formado
-- por entidades individuais, com uma interpretação para `P`, para `R` e para
-- `S`. Essas interpretações são dadas por uma função `Interp`, que a cada
-- nome de predicado e a cada lista de elementos do domínio associa um valor
-- de verdade.

abbrev Interp (D : Type) := String → List D → Bool

-- Um conjunto de símbolos de relação, com suas aridades, especifica uma
-- linguagem de lógica de predicados `L`. Uma estrutura `M = (D, I)`, formada
-- por um domínio não vazio `D` com uma função de interpretação para os
-- símbolos de relação de `L`, é chamada de **modelo** para `L`. Sempre
-- suporemos que o domínio de um modelo é não vazio.

-- Eis um modelo concreto: dez entidades de contos de fadas, nomeadas por
-- letras. Nada aqui depende da escolha das letras — o que importa é que o
-- domínio seja finito e que cada predicado diga, de cada entidade, se vale ou
-- não.

inductive Entity where
  | A | B | D | E | G | M | R | S | T | Y
deriving Repr, DecidableEq, BEq

def entities : List Entity :=
  [.A, .B, .D, .E, .G, .M, .R, .S, .T, .Y]

-- `S` é Branca de Neve, `A` é Alice, `D` é Dorothy, `G` é Cachinhos Dourados,
-- `M` é o Pequeno Mook, `Y` é Atreyu, `E` é a princesa, `B` e `R` são os
-- anões, e `T` é o gigante.

-- Os predicados unários são a pertinência a uma lista, exatamente como no
-- original. Os binários se dão por enumeração dos pares, ou por uma regra.

def girl     : Entity → Bool := ([Entity.S, .A, .D, .G].contains ·)
def boy      : Entity → Bool := ([Entity.M, .Y].contains ·)
def princess : Entity → Bool := ([Entity.E].contains ·)
def dwarf    : Entity → Bool := ([Entity.B, .R].contains ·)
def giant    : Entity → Bool := ([Entity.T].contains ·)
def child    : Entity → Bool := fun x => girl x || boy x

def love (x y : Entity) : Bool :=
  [(.Y, .E), (.B, .S), (.R, .S)].contains (x, y)

def defeat (x y : Entity) : Bool :=
  dwarf x && giant y

-- A função de interpretação amarra os nomes de predicado ao modelo. Nomes
-- fora da lista, ou usados com o número errado de argumentos, recebem
-- `false`.

def int0 : Interp Entity
  | "Girl",     [x]    => girl x
  | "Boy",      [x]    => boy x
  | "Princess", [x]    => princess x
  | "Dwarf",    [x]    => dwarf x
  | "Giant",    [x]    => giant x
  | "Child",    [x]    => child x
  | "Love",     [x, y] => love x y
  | "Defeat",   [x, y] => defeat x y
  | _, _ => false

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
-- de predicados. Como em lógica proposicional, a definição **calcula**: o
-- resultado é um `Bool`, e o valor de uma fórmula pode ser obtido com
-- `#eval`. As cláusulas dos quantificadores são as que fazem a atribuição
-- mudar: `∀v F` vale quando `F` vale para toda escolha de valor de `v`, e
-- `∃v F` quando vale para ao menos uma.

-- Aqui aparece a diferença em relação à lógica proposicional. Para decidir um
-- quantificador é preciso percorrer o domínio, e percorrer exige que o
-- domínio esteja disponível como uma lista. Por isso `eval` recebe um
-- argumento a mais, `dom`, e usa `List.all` e `List.any` — as versões
-- computáveis de `∀` e `∃`.

def Formula.eval {D : Type} [DecidableEq D]
    (dom : List D) (I : Interp D)
    (g : Assign D) : Formula Variable → Bool
  | .atom name args => I name (args.map g)
  | .eq t1 t2 => g t1 == g t2
  | .top => true
  | .bot => false
  | .neg f => !(Formula.eval dom I g f)
  | .impl f1 f2 =>
    !(Formula.eval dom I g f1) || Formula.eval dom I g f2
  | .equi f1 f2 =>
    Formula.eval dom I g f1 == Formula.eval dom I g f2
  | .conj f1 f2 =>
    Formula.eval dom I g f1 && Formula.eval dom I g f2
  | .disj f1 f2 =>
    Formula.eval dom I g f1 || Formula.eval dom I g f2
  | .forall_ v f =>
    dom.all fun d => Formula.eval dom I (g.update v d) f
  | .exists_ v f =>
    dom.any fun d => Formula.eval dom I (g.update v d) f

-- Um caso por construtor, e cada caso troca o construtor pela operação
-- correspondente sobre `Bool`. Se avaliamos fórmulas fechadas, isto é, sem
-- variáveis livres, a atribuição `g` se torna irrelevante — mas ainda é
-- preciso fornecer alguma.

def g0 : Assign Entity := fun _ => .S

def someDwarfDefeatsSomeGiant : Formula Variable :=
  .exists_ x (.conj (.atom "Dwarf" [x])
    (.exists_ y (.conj (.atom "Giant" [y])
                       (.atom "Defeat" [x, y]))))

def everyChildIsGirlOrBoy : Formula Variable :=
  .forall_ x (.impl (.atom "Child" [x])
    (.disj (.atom "Girl" [x]) (.atom "Boy" [x])))

def everyDwarfLovesAPrincess : Formula Variable :=
  .forall_ x (.impl (.atom "Dwarf" [x])
    (.exists_ y (.conj (.atom "Princess" [y])
                       (.atom "Love" [x, y]))))

#eval (Formula.eval entities int0 g0 someDwarfDefeatsSomeGiant,
       Formula.eval entities int0 g0 everyChildIsGirlOrBoy,
       Formula.eval entities int0 g0 everyDwarfLovesAPrincess)

-- A terceira é falsa no modelo: os anões `B` e `R` amam `S`, que é Branca de
-- Neve, e Branca de Neve não é a princesa. Quem ama a princesa é `Y`, que não
-- é anão.

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

-- A fórmula é uma proposta; a verificação de que ela afirma o que se queria
-- fica para a seção seguinte, que dá o meio de enunciar a condição de verdade
-- pretendida com os quantificadores do próprio Lean e exigir que as duas
-- coincidam.

-- ### Exercise (2 stars): valid-consequence ⭐⭐

-- Quais das afirmações seguintes valem? Se uma vale, explique por quê; se
-- não, dê um contraexemplo.

-- 1. `∀xPx ⊨ ∃xPx`
-- 2. `∃x∃yRxy ⊨ ∃xRxx`
-- 3. `∃y∀xRxy ⊨ ∀x∃yRxy`

-- ## Traduzindo `Formula` para `Prop`

-- Como em lógica proposicional, fechamos o capítulo ligando as duas leituras
-- de uma fórmula. `Formula.eval` calcula um `Bool`; `Formula.denote` produz a
-- proposição que a fórmula afirma. A interpretação muda junto: onde `Interp`
-- devolvia um `Bool`, `Denot` devolve uma `Prop`.

abbrev Denot (D : Type) := String → List D → Prop

def Formula.denote {D : Type} (I : Denot D)
    (g : Assign D) : Formula Variable → Prop
  | .atom name args => I name (args.map g)
  | .eq t1 t2 => g t1 = g t2
  | .top => True
  | .bot => False
  | .neg f => ¬ Formula.denote I g f
  | .impl f1 f2 =>
    Formula.denote I g f1 → Formula.denote I g f2
  | .equi f1 f2 =>
    Formula.denote I g f1 ↔ Formula.denote I g f2
  | .conj f1 f2 =>
    Formula.denote I g f1 ∧ Formula.denote I g f2
  | .disj f1 f2 =>
    Formula.denote I g f1 ∨ Formula.denote I g f2
  | .forall_ v f =>
    ∀ d : D, Formula.denote I (g.update v d) f
  | .exists_ v f =>
    ∃ d : D, Formula.denote I (g.update v d) f

-- Cada caso troca um construtor de `Formula` pelo conectivo correspondente de
-- `Prop` — o `conj` do dado vira o `∧` da proposição, e o `forall_` vira o
-- `∀` do próprio Lean.

-- Com isso podemos voltar às traduções do exercício anterior e verificá-las.
-- Enunciamos a condição de verdade pretendida à direita, com os
-- quantificadores do Lean, e exigimos que coincida com o que a fórmula
-- proposta afirma. Como `denote` calcula, cada teorema fecha por `Iff.rfl`.

theorem someoneWalksAndTalks_means {D : Type}
    (I : Denot D) (g : Assign D) :
    Formula.denote I g someoneWalksAndTalks ↔
      ((∃ d : D, I "Walk" [d]) ∧ (∃ d : D, I "Talk" [d])) :=
  sorry

theorem knightFightsDragon_means {D : Type}
    (I : Denot D) (g : Assign D) :
    Formula.denote I g knightFightsDragon ↔
      (∀ a : D, ∀ b : D,
        I "Knight" [a] ∧ I "Dragon" [b] ∧ I "Finds" [a, b] →
        I "Fights" [a, b]) :=
  sorry

-- O segundo é o que torna verificável a discussão sobre os indefinidos: a
-- força universal de *a knight* e *a dragon* não é uma opinião sobre a
-- tradução, é o que o `∀` do lado direito diz, e o `Iff.rfl` confirma que a
-- fórmula proposta diz o mesmo.

-- Falta o teorema que diz que as duas leituras concordam. Ele precisa de uma
-- hipótese que não aparecia em lógica proposicional: `eval` decide um
-- quantificador percorrendo `dom`, então só podemos esperar que ele concorde
-- com o `∀` do Lean — que fala de **todo** elemento do tipo `D` — se `dom` de
-- fato listar todos eles. É isso que `hdom` exige.

theorem Formula.eval_iff_denote {D : Type} [DecidableEq D]
    (dom : List D) (hdom : ∀ d : D, d ∈ dom)
    (I : Interp D) (g : Assign D) (f : Formula Variable) :
    f.eval dom I g = true ↔
      f.denote (fun n as => I n as = true) g := by
  induction f generalizing g with
  | atom name args => simp [Formula.eval, Formula.denote]
  | eq t1 t2 => simp [Formula.eval, Formula.denote]
  | top => simp [Formula.eval, Formula.denote]
  | bot => simp [Formula.eval, Formula.denote]
  | neg f ih => simp [Formula.eval, Formula.denote, ← ih]
  | impl f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ← ih1, ← ih2]
      cases Formula.eval dom I g f1 <;> simp
  | equi f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ← ih1, ← ih2]
  | conj f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ih1, ih2]
  | disj f1 f2 ih1 ih2 =>
      simp [Formula.eval, Formula.denote, ih1, ih2]
  | forall_ v f ih =>
      simp [Formula.eval, Formula.denote, ih]
      exact ⟨fun h d => h d (hdom d), fun h d _ => h d⟩
  | exists_ v f ih =>
      simp [Formula.eval, Formula.denote, ih]
      exact ⟨fun ⟨d, _, h⟩ => ⟨d, h⟩,
             fun ⟨d, h⟩ => ⟨d, hdom d, h⟩⟩

-- A hipótese `hdom` é a contrapartida formal de uma limitação real: só se
-- pode calcular o valor de uma fórmula quantificada quando o domínio é finito
-- e conhecido. Para domínios infinitos, `denote` continua dizendo o que a
-- fórmula afirma, mas nenhum `#eval` responde.

end FOL

