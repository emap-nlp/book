import Mathlib.Tactic.ByContra
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
import CSwLCompat

-- # Lógica Proposicional

namespace PL

-- ## Introdução

-- Em "Proof" as fórmulas proposicionais foram escritas diretamente como
-- termos do tipo `Prop`, e usando táticas construimos provas de proposições
-- `α` a partir de um conjunto de hipóteses `Γ`. Isto é, mostramos como
-- derivar `α` a partir de `Γ`, isto é `Γ ⊢ α`.

-- Em Lean, `Prop` é um tipo assim como qualquer particular proposição também
-- é um tipo. A variável `h` abaixo pode ser entendida como um identificador
-- para uma "prova qualquer" da proposição `p ∧ q`. E Lean adota o princípio
-- da "irrelevância da prova", ou seja, Lean não distingue diferentes provas
-- de uma proposição. Como consequência, o tipo `Prop` não é computável, não é
-- um "dado" que pode ser manipulado. Por exemplo, não conseguimos extrair os
-- componentes de uma conjunção `a ∧ b`. Lean sabe que todas as provas de
-- `a ∧ b` são irrelevantes e iguais, então ele não permite que você use uma
-- prova como qualquer outro dado de um `Type`. Não podemos, por exemplo,
-- realizar casamento de padrões em `h` abaixo.

sf_expect_failure
  def doesNotWork (p q : Prop) (h : p ∧ q) : Type :=
    match h with
    | And.intro ha hb => ha

-- Nesta seção, queremos manipular fórmulas e decidir quando uma fórmula `α` é
-- consequência lógica de `β`, isto é, `β ⊧ α `. A noção de consequência
-- lógica é semântica. Para toda possível escolha de valores verdade para os
-- símbolos proposicionais em `α` e `β`, sempre que `β` for verdade, `α` deve
-- ser verdade. Para *computar* o valor verdade de uma fórmula, vamos precisar
-- manipula a formula como dado, e calcular seu valor verdade a partir do
-- mapeamento de variáveis proposicionais em valores verdade.

-- Em um problema com um número finito de proposições, e os números costumam
-- ser pequenos o suficiente para que a análise sistemática de todas as
-- combinações de valores verdade seja viável na prática.

-- ## Sintaxe de Lógica Proposicional

-- Para construir fórmulas, não poderemos mais usar a notação de Lean
-- disponível para `Prop`. Quando escrevemos `p ∧ q`, o símbolo `∧` é um
-- operador infixado (aparece no meio dos argumentos) e representa o
-- construtor `And.intro` do tipo `And`. Os operadores, para serem usados de
-- forma infixada, precisam ter um mecanismo de precedência para permitir que
-- termos como `p ∧ q ∧ r` sejam interpretados como `p ∧ (q ∧ r)` e não
-- `(p ∧ q) ∧ r`, ou seja, tenham sempre uma leitura não ambigua. Nada disso
-- estará ao nosso dispor na sintaxe que iremos introduzir nesta seção.

-- Nossas fórmulas serão representadas por termos do tipo indutivo `Formula`.
-- Um átomo é identificado por um nome, e o nome é uma `String`.

inductive Formula where
  | atom (name : String)
  | top
  | bot
  | neg (f : Formula)
  | conj (f g : Formula)
  | disj (f g : Formula)
  deriving DecidableEq, Repr

-- Os contrutores `Formula.top` e `Formula.bot` representam as proposições
-- "sempre verdadeira" e "sempre falsa". São objetos sintáticos que serão
-- sempre interpretados como os valores verdade `true` e `false` na semântica.
-- Com este tipo, podemos representar fórmulas arbitrariamente complexas.

#eval
  let p  : Formula := .atom "p"
  let q  : Formula := .atom "q"
  let f₁ : Formula := .neg (.neg p)
  let f₂ : Formula := .disj (.neg p) q
  Formula.conj f₁ f₂

-- Como não temos símbolos infixados, não temos ambiguidade. As duas possíveis
-- interpretações para a sentença ambigua em português "Maira é jovem e bonita
-- ou triste" seriam:

namespace Maria

def j : Formula := .atom "MJ"
def b : Formula := .atom "MB"
def t : Formula := .atom "MT"

def form₁ := Formula.conj j (.disj b t)
def form₂ := Formula.disj (.conj j b) t

end Maria

-- Na lógica proposicional (PL, "propotional logic"), uma **linguagem
-- proposicional** é o conjunto de todas as fórmulas que podem ser construídas
-- a partir de um **vocabulário** de símbolos não lógicos (os átomos
-- representados por `Formula.atom`). Acima, a partir dos átomos construídos
-- com as strings "MJ", "MB" e "MT", infinitas fórmulas de complexidade
-- arbitrária podem ser construídas pela combinação dos demais construtores de
-- `Formula`. Cada um destes construtores representam um operador lógico.

-- Podemos também pensar que uma dada fórmula (ou conjunto de fórmulas) induz
-- um vocabulário, o conjunto de todos os símbolos que ocorreram na fórmula
-- (ou conjunto de fórmulas). No exemplo anterior, `j`, `b` e `t` são
-- identificadores em Lean para termos do tipo `Formula`, representam fórmulas
-- em PL mas não estão em PL, estão na metalinguagem. As strings "MJ", "MB" e
-- "MT" são os nomes dos átomos usados nas formulas, o vocabulário destas
-- fórmulas.

-- A função `names` abaixo extrai o vocabulário de uma fórmula. A lista
-- resultante deve estar ordenada e sem repetições.

def Formula.namesRaw : Formula → List String
  | .atom name => [name]
  | .top => []
  | .bot => []
  | .neg f => f.namesRaw
  | .conj f g => f.namesRaw ++ g.namesRaw
  | .disj f g => f.namesRaw ++ g.namesRaw

def Formula.names (f : Formula) : List String :=
  sorry

#eval Maria.form₁.names

-- ### Exercise (1 star): collect-atoms ⭐

-- Complete a definição da função `namesL` abaixo, que estende a função
-- `names` para um conjunto de fórmulas. Se sua definição estiver correta, a
-- prova do exemplo deve ser obtida diretamente com a tática `native_decide`.
-- Dica: não repita ordenações.

def Formula.namesL (fs : List Formula) : List String :=
  sorry

example : Formula.namesL [Maria.form₁, Maria.form₂] == ["MB", "MJ", "MT"] :=
  sorry

-- ### Exercise (1 star): collect-atoms-alternative ⭐

-- Complete a definição da função `Formula.names₁` com uma implementação
-- alternativa para `Formula.names` que ao invés de eliminar duplicatas e
-- ordenar no final da recursão, constrói a lista de saída sem duplicatas e
-- ordenada. Se sua definição estiver correta, a prova do exemplo deve ser
-- obtida diretamente com a tática `native_decide`. Dica: não repita
-- ordenações.

def Formula.namesRaw₁ (f : Formula) (sofar : List String) : List String :=
  sorry

def Formula.names₁ (f : Formula) : List String :=
  sorry

#eval Maria.form₁.names₁

example : Maria.form₁.names₁ == ["MB", "MJ", "MT"] :=
  sorry

-- Nem todos os conectivos precisam ser definidos como "primitivos". Como
-- vimos na seção pl-lean a implicação pode ser definida como uma dijunção. E
-- a dupla implicação como uma conjunção de implicações.

def Formula.impl (f g : Formula) : Formula := .disj (.neg f) g
def Formula.iff (f g : Formula) : Formula :=
  .conj (Formula.impl f g) (Formula.impl g f)

-- A conjunção e a disjunção são binárias. Poderiam receber uma lista de
-- fórmulas `conj (fs : List Formula)`, mas um construtor que guarda uma
-- `List Form` dentro do próprio tipo o torna um indutivo *nested*, mais
-- complicado de manipular em Lean. Mas podemos definir funções que recebem
-- listas de fórmulas e constrem conjunções e disjunções. Abaixo `top`/`bot`
-- são a base da recursão de `conjs`/`disjs`.

def Formula.conjs : List Formula → Formula
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Formula.conjs fs)

def Formula.disjs : List Formula → Formula
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Formula.disjs fs)

-- Note que `Formula.bot` é o elemento neutro da dijunção, `bot ∨ a`. E
-- `Formula.top` é o elemento neutro da conjunção, `top ∧ a`. Uma conjunção
-- vazia é sempre verdadeira, uma disjunção vazia é sempre falsa. O que sugere
-- as implementações alternativas a seguir.

def Formula.conjs₁ (fs : List Formula) : Formula :=
  fs.foldl .conj .top

def Formula.disjs₁ (fs : List Formula) : Formula :=
  fs.foldl .disj .bot

-- ### Exercise (1 star): bangu-form ⭐

-- Três pessoas são suspeitas de torcer pelo Bangu F.C. Aparecido entrevistou
-- os três, para tentar descobrir, e obteve os seguintes depoimentos:

-- - Auro: Joaquim não torce pelo BFC e Cláudia torce pelo BFC.

-- - Joaquim: Se Auro não torce pelo BFC, Cláudia também não torce pelo BFC.

-- - Cláudia: Eu torço pelo BFC, mas pelo menos um dos outros não torce pelo
--   BFC.

-- Considerando que as fórmulas atômicas `A`, `J` e `C` representam,
-- respectivamente, que Auro, Joaquim e Cláudia torcem pelo BFC, complete a
-- formalização dos três depoimentos construindo as expressões correspondentes
-- do tipo `Formula`.

namespace Bangu

def A : Formula := .atom "Auro"
def J : Formula := .atom "Joaquim"
def C : Formula := .atom "Claudia"

def depo1 : Formula := sorry
def depo2 : Formula := sorry
def depo3 : Formula := sorry

end Bangu

-- ### Exercise (1 star): exclusive-or ⭐

-- A expressão `p ∨ q` é verdadeira mesmo quando `p` e `q` são ambos
-- verdadeiros. Em português, "ou" costuma ser exclusivo, como em "Você pode
-- ficar com o sorvete ou com o algodão-doce, mas não com os dois." Defina um
-- conectivo `xor` para "ou exclusivo", usando os conectivos já definidos.

def Formula.xor (f g : Formula) : Formula :=
  sorry

-- Um termo do tipo `Formula` é um dado. Nenhum dos exercícios abaixo seriam
-- possíveis em `Prop`. Não há como perguntar "quantos `∧` tem esta
-- proposição" a um valor de tipo `Prop`, porque `Prop` não guarda a fórmula
-- que o provou. Vamos definir duas fórmulas para usar nos exercícios
-- seguintes.

def form1 : Formula :=
  .conj (.atom "p") (.neg (.atom "p"))

def form2 : Formula :=
  .disjs [.atom "p1", .atom "p2", .atom "p3", .atom "p4"]

def form3 : Formula :=
  let p : Formula := .atom "p"
  let q : Formula := .atom "q"
  .iff (.impl p q ) (.disj (.neg p) q)

-- ### Exercise (1 star): count-operators ⭐

-- Implemente uma função `countOps` para contar o número de operadores lógicos
-- de uma fórmula. A tática `decide` é como pedir ao Lean para executar a
-- decisão de uma proposição boleana e, se o resultado for true, transformar
-- esse resultado em uma prova.

def Formula.countOps : Formula → Nat :=
  sorry

example : form2.countOps = 3 := by decide

-- ### Exercise (1 star): formula-depth ⭐

-- Implemente uma função `depth` para calcular a profundidade da árvore de
-- análise de uma fórmula.

def Formula.depth : Formula → Nat :=
  sorry

example : form2.depth = 3 := by decide

-- ## Semântica de Lógica Proposicional

-- Todas as regras de derivação que usamos em "Proof" são justificadas por uma
-- noção semântica de **consequência lógica**. Entendemos que `P` deve ser
-- verdade sempre que `P ∧ Q` for verdade, para qualquer possível tradução de
-- `P` e `Q` de volta para expressões em uma linguagem natural, por isso
-- aceitamos `P ∧ Q ⊧ P`. Para formalizar esta noção de "todas as possíveis
-- traduções", vamos precisar de um processo para avaliar fórmulas lógicas em
-- valores verdade.

-- A partir de um mapeamento inicial de símbolos proposicionais em valores
-- boleanos, o tipo `Bool` em Lean, obtemos de forma recursiva o valor verdade
-- de qualquer termo do tipo `Formula`. Os construtores `Formula.top` e
-- `Formula.bot` são constantes, nenhuma valoração os afeta. Podemos perceber
-- que, de todos os casos da recursão, só o caso do átomo (construtor
-- `Formula.atom`) consulta a valoração passada; os outros casos apenas
-- combinam os valores verdade das subfórmulas.

/-- The evaluation of a formula `f`, given the function `value`
    that gives each atom its truth value. -/
def Formula.eval (f : Formula) (value : String → Bool) : Bool :=
  match f with
  | .atom name => value name
  | .top => true
  | .bot => false
  | .neg g => !g.eval value
  | .conj g h => g.eval value && h.eval value
  | .disj g h => g.eval value || h.eval value

-- A função `Formula.eval` faz a recursão e recebe como parâmetro a função que
-- dá o valor verdade de um átomo. Toda a semântica que construímos a seguir
-- passa por `Formula.eval`.

-- Chamamos as fórmulas que são sempre verdade para qualquer valoração de suas
-- variáveis proposicionais de **tautologias**, ou, simplesmente, fórmulas
-- **válidas**. Se `α` é uma tautologia, significa que `⊨ α`, não depende de
-- nenhuma hipótese para ser verdade. As fórmulas que são sempre falsas para
-- toda valoração são chamadas de **contradições** (ou insatisfatíveis). Uma
-- fórmula é **satisfatível** se há pelo menos uma valoração que a torna
-- verdadeira. Uma fórmula é **contingente** se existe pelo menos uma
-- valoração que torna a fórmula verdadeira e pelo menos uma que a torna
-- falsa. Podemos concluir que se `α` é uma contradição, então `⊨ ¬ α` (sua
-- negação é válida). Toda tautologia é satisfatível, mas nem toda fórmula
-- satisfatível é uma tautologia.

-- ### Exercise (1 star): valuations ⭐

-- Construa as valorações `v₁` e `v₂` de tal forma que os exemplos possam ser
-- provados com a tática `decide` os exemplos seguintes.

namespace TestVals

def p : Formula := .atom "p"
def q : Formula := .atom "q"
def r : Formula := .atom "r"

def form1 : Formula := .neg (.disj (.conj p r) (.neg q))
def form2 : Formula := .disj (.impl q p) (.conj r (.neg q))
def form3 : Formula := .impl (.conj q (.neg p)) (.neg r)

def v₁ (v : String) : Bool :=
 sorry

def v₂ (v : String) : Bool :=
 sorry

example : form1.eval v₁ = true  := sorry
example : form1.eval v₂ = false := sorry
example : form2.eval v₁ = false := sorry
example : form3.eval v₂ = true  := sorry

end TestVals

-- A seguir, definimos a função `allVals` que gera a lista de todas as
-- valorações possíveis sobre o vocabulário de uma `Formula`.

abbrev Valuation := List (String × Bool)

/-- return an evaluation function from `Valuation`. -/
def Valuation.toFun (vs : Valuation) : String → Bool :=
  fun n => (vs.lookup n).getD false

def genVals : List String → List Valuation
  | [] => [[]]
  | n :: ns =>
    let vs := (genVals ns)
    vs.map ((n, true) :: ·) ++ vs.map ((n, false) :: ·)

/-- return all possible valuations for `f`. -/
def Formula.allVals (f : Formula) : List Valuation :=
  genVals f.names

-- Com estas funções, podemos construir a tabela verdade de uma fórmula.

#eval
 let as := form1.allVals
 List.zip as (as.map (fun vs => form1.eval vs.toFun))

-- Para decidir se uma fórmula é tautologia, satisfatível ou contradição,
-- podemos percorrer todas as valorações possíveis, que são finitas, porque
-- uma fórmula tem finitos átomos.

def Formula.tautology (f : Formula) : Bool :=
  f.allVals.all (fun v => f.eval v.toFun)

def Formula.satisfiable (f : Formula) : Bool :=
  f.allVals.any (fun v => f.eval v.toFun)

def Formula.contradiction (f : Formula) : Bool :=
  !f.satisfiable

#eval form1.contradiction
#eval (Formula.neg form1).tautology
#eval form1.satisfiable

-- E como já sabemos da seção pl-lean, podemos mostrar que `form3` é uma
-- tautologia.

#eval form3.tautology

-- ### Exercise (1 star): ex-pl-contingent ⭐

-- Complete a definição de fórmula contingente. Para provar o exemplo, use
-- `native_decide`.

def Formula.contingent (f : Formula) : Bool :=
  sorry

example : (Formula.atom "q").satisfiable := by
  sorry

-- ### Exercise (1 star): ex-pl-satisfiable ⭐

-- Complete a definição de `F` que só deverá usar os átomos `p` e `q`. E prove
-- o exemplo.

namespace ExSat

def p : Formula := .atom "p"
def q : Formula := .atom "q"

def F : Formula := sorry

example : F.satisfiable ∧ F.depth = 4 := by
  sorry

end ExSat

-- A seguir, escrevemos implies para a relação de consequência lógica,
-- chamando atenção para a relação entre `P ⊨ Q` e `⊨ P → Q`. Uma proposição
-- `Q` é consequência lógica de `P` se, e somente se, a implicação `P → Q` é
-- uma tautologia. Se `P → Q ≡ ¬ P ∨ Q ≡ ¬ (P ∧ ¬ Q)` então podemos também
-- dizer que `P ⊧ Q` se e somente se `⊨ ¬ (P ∧ ¬ Q)`.

-- Podemos estender para uma consequência lógica de fórmulas
-- `{P₁, …, Pₙ} ⊧ α`, indicando que toda valoração que torna as fórmulas
-- `P₁, …, Pₙ` verdadeiras também torna `α` verdadeira. O que equivale afirmar
-- que a implicação da conjunção das premissas na conclusão é válida
-- `⊧ (P₁ ∧ … ∧ Pₙ) → α`.

-- Duas fórmulas `α` e `β` são **logicamente equivalentes**, escrevemos
-- `α ≡ β`, se têm o mesmo valor de verdade para toda valoração possível.
-- Segue da definição que todas as tautologias são logicamente equivalentes
-- entre si, e o mesmo vale para as contradições.

def Formula.implies (f g : Formula) : Bool :=
  (Formula.conj f (.neg g)).contradiction

def Formula.equivalent (f g : Formula) : Bool :=
  f.implies g && g.implies f

-- ### Exercise (1 star): ex-pl-equiv ⭐

-- Complete os exemplos com fórmulas equivalentes mas sintaticamente
-- diferentes de `F0`, `F1` e `F2`. Todos os `example` podem ser provados com
-- a tática `native_decide`. Suas fórmulas devem usar apenas os átomos `p` e
-- `q` já definidos.

namespace ExEquiv
def p : Formula := .atom "p"
def q : Formula := .atom "q"

def F0 : Formula := .neg (.neg p)
def F1 : Formula := .impl p q
def F2 : Formula := .neg (.iff p q)

example : F0.equivalent sorry :=
 sorry

example : F1.equivalent sorry :=
 sorry

example : F2.equivalent
   sorry :=
 sorry
end ExEquiv

-- ### Exercise (2 stars): implies-from-list ⭐⭐

-- Nossa definição `Formula.implies` relaciona duas fórmulas. Complete a
-- definição abaixo para que possamos falar de `Γ ⊧ α`, a consequência lógica
-- de um conjunto de fórmulas.

def Formula.impliesL (hs : List Formula) (c : Formula) : Bool :=
  sorry

-- ### Exercise (2 stars): pl-consequence ⭐⭐

-- Formalize as consequências lógicas abaixo completando o código como novos
-- exemplos usnado termos do tipo `Formula`. As duas primeiras já foram
-- formalizada.

-- 1. `p ⊧ p ∨ q`
-- 2. `p, q ⊧ ¬ p`
-- 3. `p → q ⊧ ¬p → ¬q`
-- 4. `¬q ⊧ p→q`
-- 5. `¬p, q→p ⊧ ¬q`

-- Em todos os casos, para fechar ou não as provas, você só precisa da tática
-- `native_decide`. Note que quando existe consequência lógica, o tipo `Bool`
-- pode ser promovido à `Prop` automaticamente pelo Lean, então você não
-- precisa escrever `P.implies Q = true`, basta `P.implies Q`. Mas quando
-- queremos mostrar que a consequência não é verdadeira, precisamos de
-- `P.implies Q = false`.

namespace Cons

def p : Formula := .atom "p"
def q : Formula := .atom "q"

example : p.implies (.disj p q) :=
  by native_decide

example : Formula.impliesL [p,q] (.neg p) = false :=
  by native_decide

-- FILL IN HERE

end Cons

-- ### Exercise (1 star): bangu-proof ⭐

-- Complete a definição de `banguSolution` para que a fórmula represente a
-- solução do problema dos torcedores do Bangu F.C. assumindo que os 3
-- depoimentos foram verdadeiros. A prova do exemplo é completada com
-- `native_decide`.

namespace Bangu

def banguSolution : Formula := sorry

example : Formula.impliesL [depo1, depo2, depo3] banguSolution = true :=
  sorry

end Bangu

-- A semântica da lógica proposicional também pode ser dada na forma de
-- atualizações sobre valorações. Fixe primeiro um conjunto de valorações como
-- estado corrente e depois defina uma função de atualização que deixa apenas
-- as valorações que satisfazem uma dada fórmula.

def update (vals : List Valuation) (f : Formula) : List Valuation :=
  vals.filter (fun v => f.eval v.toFun)

-- Atualizar o estado de todas as valorações com uma contradição não deixa
-- nada; atualizar com uma tautologia não tira nada. Atualizar com uma fórmula
-- contingente tira alguma coisa, e atualizar com sua negação tira o
-- complemento.

#eval form1.allVals
#eval (update form1.allVals form1)
#eval (update form1.allVals (.neg form1))
#eval (update form2.allVals (.neg form2))

-- ## Traduzindo `Formula` para `Prop`

-- Dadas as definições da sintaxe e semântica de `PL`, Podemos provar alguns
-- meta-teoremas sobre elas. Nos capítulos seguintes, estes resultados não
-- serão necessariamente úteis, mas mostram que nossas definições estão
-- consistentes. Os teoremas a seguir estão no nível da linguagem Lean, isto
-- quer dizer que não são teoremas na linguagem `PL` mas sobre a linguagem
-- `PL`. Abaixo provamos dois teoremas. O teorema `top_equiv_taut` diz que
-- toda tautologia é equivalente a `Formula.top`. O teorema
-- `neg_taut_is_contradiction` diz que se uma fórmula é uma tautologia, sua
-- negação é uma contradição.

namespace MetaTheorems
open Formula

theorem top_equiv_taut (f : Formula) : f.tautology ↔ f.equivalent top := by
  have hv : (conj top (neg f)).allVals = f.allVals := rfl
  simp only [equivalent, implies,
   contradiction, satisfiable, tautology, hv, eval]
  simp [List.all_eq_true]

theorem neg_taut_is_contradiction (f : Formula) :
  f.tautology ↔ (Formula.neg f).contradiction := by
  have hv : (neg f).allVals = f.allVals := rfl
  simp only [contradiction, satisfiable, tautology, eval, hv]
  simp [List.all_eq_true]

-- E também podemos provar o princípio da contraposição. Temos que `F₁ ⊧ F₂`
-- se e somente se `¬ F₂ ⊧ ¬F₁`. Expandindo a definição de `Formula.implies` e
-- `Formula.satisfiable`, temos o enunciado do teorema
-- `contraposition_principle₁`. A prova dele é direta, corresponde a avaliação
-- da definição de `Formula.eval` seguida da aplicação da comutativade da
-- conjunção boleana. Mas ele não é o princípio diretamente.

theorem contraposition_principle₁ (F₁ F₂ : Formula) (v : Valuation) :
    (conj F₁ (neg F₂)).eval v.toFun =
    (conj (neg F₂) (neg (neg F₁))).eval v.toFun := by
  simp [Formula.eval]
  exact Bool.and_comm _ _

-- O teorema `contraposition_principle₂`, por outro lado, corresponde
-- exatamente ao enunciado do princípio. Mas, para prová-lo, precisamos de
-- alguns passos adicionais. Primeiro precisamos provar que todas as
-- valorações possíveis para `F₁` coincidem com as de `F₂`. esta é nossa
-- hipótese `hv`. Também precisamos mostrar que se duas listas são permutações
-- entre si, então ordená-las irá produzir a mesma lista. Este é o teorema
-- auxiliar `mergeSort_eq_of_perm`. A notação `List.perm_append_comm.dedup`
-- corresponde a uma composição de provas. Lean resolve para a composição de
-- `List.Perm.dedup` com `List.perm_append_comm`. Como o leitor pode imaginar,
-- estes resultados auxiliares combinados com alguns outros teoremas
-- adicionais, seriam suficientes para melhor automação da prova de
-- `contraposition_principle₂` e outros teoremas ainda mais relevantes sobre
-- `PL`. Mas nosso objetivo é somente ilustrar a capacidade de Lean em provar
-- estes resultados. Finalmente, sugerimos que o leitor consulte (FRO, 2026)
-- ou navegue pelas definições no seu editor, se desejar entender os todos os
-- teoremas e tácticas usadas nas provas a seguir.

theorem mergeSort_eq_of_perm {xs ys : List String}
    (h : xs.Perm ys)
    : xs.mergeSort (· ≤ ·) = ys.mergeSort (· ≤ ·) :=
    ((List.mergeSort_perm xs _).trans
     (h.trans (List.mergeSort_perm ys _).symm)).eq_of_pairwise'
    (List.pairwise_mergeSort' _ _) (List.pairwise_mergeSort' _ _)

theorem contraposition_principle₂ (F₁ F₂ : Formula) :
    F₁.implies F₂ ↔ (Formula.neg F₂).implies (.neg F₁) := by
  have hv :
    (conj F₁ (neg F₂)).allVals = (conj (neg F₂) (neg (neg F₁))).allVals := by
    simp [Formula.allVals, Formula.names, Formula.namesRaw]
    exact congrArg genVals
      (mergeSort_eq_of_perm List.perm_append_comm.dedup)
  simp only [Formula.implies, Formula.contradiction,
    Formula.satisfiable, hv, Formula.eval]
  constructor
  all_goals
  · intro h
    simpa [Bool.and_comm, Bool.not_not] using h

end MetaTheorems

-- Finalmente, o mapeamento de `Formula` em `Prop` pode ser definido como uma
-- função que interpreta cada fórmula como a proposição que ela afirma, dado
-- um mapeamento de átomos em `Bool`.

def Formula.denote (f : Formula) (v : String → Bool) : Prop :=
  match f with
  | .atom name => v name
  | .top => True
  | .bot => False
  | .neg g => ¬ g.denote v
  | .conj g h => g.denote v ∧ h.denote v
  | .disj g h => g.denote v ∨ h.denote v

-- Repare no que cada caso faz: ele troca um construtor de `Formula` pelo
-- conectivo correspondente de `Prop`. O `Formula.conj` do dado vira o `∧` da
-- proposição, o `Formula.neg` vira o `¬`. O teorema que fecha o capítulo diz
-- que as duas leituras concordam. Dada uma valoração, computar o valor
-- verdade de uma fórmula resulta em `true` exatamente quando a proposição
-- resultande da fórmula para a mesma valoração tem prova.

open Formula in

theorem Formula.eval_iff_denote (f : Formula) (v : String → Bool) :
    f.eval v = true ↔ f.denote v := by
  induction f with
  | atom name => simp [eval, denote]
  | top => simp [eval, eval, denote]
  | bot => simp [eval, eval, denote]
  | neg g ih =>
      simp only [eval, eval, denote] at ih ⊢
      rw [← ih]
      simp
  | conj g h ihg ihh =>
      simp only [eval, eval, denote] at ihg ihh ⊢
      simp [ihg, ihh]
  | disj g h ihg ihh =>
      simp only [eval, eval, denote] at ihg ihh ⊢
      simp [ihg, ihh]

end PL

