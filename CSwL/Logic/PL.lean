import Mathlib.Tactic.ByContra
import CSwLCompat

-- # Lógica proposicional

namespace PL

-- ## Introdução

-- Em "Proof" as fórmulas proposicionais foram escritas diretamente como
-- termos do tipo `Prop`, e usando táticas construimos provas de proposições
-- `α` a partir de um conjunto de hipóteses `Γ`. Isto é, em Lean mostramos
-- como derivar `α` a partir de `Γ`, isto é `Γ ⊢ α`, de forma sintática.

-- Mas em Lean, `Prop` é um tipo e proposições particulares também são tipos.
-- A variável `h` abaixo pode ser entendida como um identificador para uma
-- "prova qualquer" da proposição `p ∧ q`. E Lean adota o princípio da
-- "irrelevância da prova", ou seja, Lean não distingue diferentes provas de
-- uma proposição. Como consequência, o tipo `Prop` não é computável, não é um
-- "dado" que pode ser manipulado. Por exemplo, não conseguimos extrair os
-- componentes de uma conjunção `a ∧ b`. Lean sabe que todas as provas de
-- `a ∧ b` são irrelevantes e iguais, então ele não permite que você use uma
-- prova para tomar decisões no mundo dos dados programáveis (`Type`). Em
-- outras palavras, não podemos realizar casamento de padrões em `h` abaixo.

sf_expect_failure
  section
  variable (p q : Prop)
  
  variable (h : p ∧ q)
  #check p ∧ q
  #check h
  
  def doesNotWork (h : p ∧ q) : Type :=
    match h with
    | And.intro ha hb => ha
  
  end

-- Nesta seção, queremos manipular fórmulas e decidir quando uma fórmula `α` é
-- consequência lógica de `β`, isto é `β ⊧ α `. A noção de consequência lógica
-- é semântica. Para toda possível escolha de valores verdade para os símbolos
-- proposicionais em `α` e `β`, sempre que `β` for verdade, `α` deve ser
-- verdade. Para *computar* o valor verdade de uma fórmula, vamos precisar
-- manipula a formula como dado, e calcular seu valor verdade a partir do
-- mapeamento de variáveis proposicionais em valores verdade. Em tempo, a
-- relação dentre duas fórmulas pode ser naturalmente estendida para uma
-- relação entre um conjunto de fórmulas `Γ` e uma fórmula, `Γ ⊧ α`.

-- Em um problema com um número finito de proposições, e os números costumam
-- ser pequenos o suficiente para que a análise sistemática de todas as
-- combinações de valores verdade seja viável na prática. Para demonstrar que
-- todo número par maior que dois pode ser escrito como uma soma de dois
-- números primos esta estratégia não seria válida.

-- ## Sintaxe de Lógica Proposicional

-- Formalmente, a sintaxe da LP é definida pela BNF abaixo. As variáveis
-- proposicionais (ou símbolos sentenciais) são os `atom`. O uso do sufixo `'`
-- no não-terminal `atom` é uma forma conveniente de expressar que podemos
-- gerar quantos átomos forem necessários.

-- atom ::= "p" | "q" | "r" | atom"'" ;
-- F    ::= atom
--   | "¬" F ("negação")
--   | "(" F "∧" F ")" ("conjunção")
--   | "(" F "∨" F ")" ("disjunção")
--   | "(" F "→" F ")" ("implicação")
--   | "(" F "↔" F ")" ("se-somente-se") ;

-- Com esta gramática, podemos gerar fórmulas como `¬¬¬p'''`,
-- `((p ∨ p') ∧ p')`, `(p ∧ (p' ∧ p'''))`. Sem parênteses a gramática pode
-- gerar strings ambíguas: `p ∧ p′ ∨ p″` lê-se tanto como `(p ∧ p′) ∨ p″`
-- quanto como `p ∧ (p′ ∨ p″)`, e a ambiguidade estrutural afeta o
-- significado, como na sentença "era jovem e bonita ou triste". Nem todos os
-- conectivos precisam ser definidos como "primitivos". O conectivo `→`
-- poderia ser definido como uma abreviação para `p → q ≃ ¬ p ∨ q`.

-- A gramática acima será representada pelo tipo indutivo `Form`. Um átomo é
-- identificado por um nome, e o nome é uma `String`. Isso dá o inventário
-- ilimitado que a gramática pede sem precisar enumerar símbolo por símbolo.

inductive Form where
  | atom (name : String)
  | top
  | bot
  | neg (f : Form)
  | conj (f g : Form)
  | disj (f g : Form)
  deriving DecidableEq

-- Vale observar que a biblioteca `cslib` define o tipo
-- `Cslib.Logic.PL.Proposition` que poderia ser usado nesta seção, mas isto
-- introduziria uma complexidade desnecessária. Acima escolhemos não declarar
-- os símbolos `→` e `↔` como construtores do tipo, eles serão funções que
-- criam `Form` a partir de `Form`.

def Form.impl (f g : Form) : Form := .disj (.neg f) g
def Form.equi (f g : Form) : Form :=
  .conj (Form.impl f g) (Form.impl g f)

-- A conjunção e a disjunção são binárias. Poderiam receber uma lista de
-- fórmulas `conj (fs : List Form)`, mas um construtor que guarda uma
-- `List Form` dentro do próprio tipo o torna um indutivo *nested*, mais
-- complicado de manipular em Lean. Mas podemos definir funções que recebem
-- listas de fórmulas e constrem conjunções e disjunções. Abaixo `top`/`bot`
-- são a base da recursão de `conjs`/`disjs`. Uma conjunção vazia é sempre
-- verdadeira, uma disjunção vazia é sempre falsa.

def Form.conjs : List Form → Form
  | [] => .top
  | [f] => f
  | f :: fs => .conj f (Form.conjs fs)

def Form.disjs : List Form → Form
  | [] => .bot
  | [f] => f
  | f :: fs => .disj f (Form.disjs fs)

-- ### Exercise (1 star): bangu-form ⭐

-- Três pessoas são suspeitas de torcer pelo Bangu F.C. Aparecido entrevistou
-- os três, para tentar descobrir, e obteve os seguintes depoimentos:

-- - Auro: Joaquim não torce pelo BFC e Cláudia torce pelo BFC.

-- - Joaquim: Se Auro não torce pelo BFC, Cláudia também não torce pelo BFC.

-- - Cláudia: Eu torço pelo BFC, mas pelo menos um dos outros não torce pelo
--   BFC.

-- Termine a formalização dos depoimentos construindo uma expressão no tipo
-- `Form`.

def A : Form := Form.atom "Auro"
def J : Form := Form.atom "Joaquim"
def C : Form := Form.atom "Claudia"

def depo1 : Form := sorry
def depo2 : Form := sorry
def depo3 : Form := sorry

-- ### Exercise (1 star): exclusive-or ⭐

-- A expressão `p ∨ q` é verdadeira mesmo quando `p` e `q` são ambos
-- verdadeiros. Em português, "ou" costuma ser exclusivo, como em "Você pode
-- ficar com o sorvete ou com o algodão-doce, mas não com os dois." Defina um
-- conectivo `xor` para "ou exclusivo", usando os conectivos já definidos.

def Form.xor (f g : Form) : Form :=
  sorry

-- O tipo `Form` é um `inductive`. Um valor de `Form` é dado. Nenhum dos
-- exercícios abaixo seriam possíveis em `Prop`. Não há como perguntar
-- "quantos `∧` tem esta proposição" a um valor de tipo `Prop`, porque `Prop`
-- não guarda a fórmula que o provou. Vamos definir duas fórmulas para usar
-- nos exercícios seguintes.

def form1 : Form :=
  .conj (.atom "p") (.neg (.atom "p"))

def form2 : Form :=
  Form.disjs [.atom "p1", .atom "p2", .atom "p3", .atom "p4"]

#eval form2

-- ### Exercise (1 star): count-operators ⭐

-- Implemente uma função `opsNr` para contar o número de operadores de uma
-- fórmula. a tática `decide` é como pedir ao Lean para executar a decisão de
-- uma proposição booleana e, se o resultado for true, transformar esse
-- resultado em uma prova.

def Form.opsNr : Form → Nat :=
  sorry

example : form2.opsNr = 3 := by decide

-- ### Exercise (1 star): formula-depth ⭐

-- Implemente uma função `depth` para calcular a profundidade da árvore de
-- análise de uma fórmula.

def Form.depth : Form → Nat :=
  sorry

example : form2.depth = 3 := by decide

-- ### Exercise (2 stars): collect-atoms ⭐⭐

-- Implemente `propNames` para coletar a lista de nomes de átomos
-- proposicionais que ocorrem numa fórmula. A lista resultante deve estar
-- ordenada e sem repetições.

private def Form.propNamesRaw : Form → List String :=
  sorry

def Form.propNames (f : Form) : List String :=
  sorry

-- ## Semântica de Lógica Proposicional

-- Todas as regras de derivação que usamos em "Proof" são justificadas por uma
-- noção semântica de **consequência lógica**. Entendemos que `P` deve ser
-- verdade sempre que `P ∧ Q` for verdade, para qualquer possível tradução de
-- `P` e `Q` de volta para expressões em uma linguagem natural, por isso
-- aceitamos `P ∧ Q ⊧ P`. Para formalizar esta noção de "todas as possíveis
-- traduções", vamos precisar de um processo para avaliar fórmulas lógicas em
-- valores verdade.

-- Vamos chamar de **valorações** um mapeamento de símbolos proposicionais no
-- conjunto dos booleanos, que em Lean correspondem aos valores `True` e
-- `False` do tipo `Bool`.

-- Podemos representar uma valoração como uma lista de pares, e um átomo
-- ausente da lista conta como falso.

abbrev Valuation := List (String × Bool)

-- Se `V` é uma valoração, ela se estende a uma função que mapea qualquer
-- fórmula para um valor de verdade. A extensão é definida por recursão sobre
-- a estrutura da fórmula, um caso por construtor. Os construtores `top` e
-- `bot` são constantes, nenhuma valoração os afeta. Se um átomo ocorrer mais
-- de uma vez, vamos assumir que seu valor verdade é a primeira ocorrência
-- dele na lista, isto corresponde ao comportamento da função `List.lookup`.

def Form.eval (f : Form) (v : Valuation) : Bool :=
  match f with
  | .atom name => (v.lookup name).getD false
  | .top => true
  | .bot => false
  | .neg g => !g.eval v
  | .conj g h => g.eval v && h.eval v
  | .disj g h => g.eval v || h.eval v

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

-- ### Exercise (1 star): taut-contradiction ⭐

-- Construa as valorações `vs1` e `vs2` de tal forma que os exemplos possam
-- ser provados com a tática `decide`.

def form3 : Form :=
  .disj (.atom "p") (.conj (.atom "q") (.atom "r"))

def form4 : Form :=
  .neg (.conj (.atom "p") (.neg (.atom "q")))

def form5 : Form :=
  .conj (.atom "a") (.impl (.neg (.atom "b")) (.atom "c"))

def vs1 : List (String × Bool) := sorry
def vs2 : List (String × Bool) := sorry

example : form3.eval vs1 = true := by sorry
example : form4.eval vs1 = true := by sorry
example : form5.eval vs2 = true := by sorry

-- A função a seguir gera a lista de todas as valorações sobre o conjunto dos
-- nomes de átomos presentes em um termo do tipo `Form`. Com estas funções,
-- podemos construir a tabela verdade de uma fórmula.

def genVals : List String → List Valuation
  | [] => [[]]
  | n :: ns =>
    let vs := (genVals ns)
    vs.map ((n, true) :: ·) ++ vs.map ((n, false) :: ·)

def Form.allVals (f : Form) : List Valuation :=
  genVals f.propNames

#eval List.zip form1.allVals (form2.allVals.map (form2.eval ·))

-- Para decidir se uma fórmula é tautologia, satisfatível ou contradição,
-- podemos percorrer todas as valorações possíveis, que são finitas, porque
-- uma fórmula tem finitos átomos.

def Form.tautology (f : Form) : Bool :=
  f.allVals.all (fun v => f.eval v)

def Form.satisfiable (f : Form) : Bool :=
  f.allVals.any (fun v => f.eval v)

def Form.contradiction (f : Form) : Bool :=
  ¬ f.satisfiable

#eval (form1.contradiction, (Form.neg form1).tautology, form1.satisfiable)

-- ### Exercise (1 star): def-contingente ⭐

-- Complete a definição de fórmula contingente. Para provar o exemplo, use
-- `native_decide`.

def Form.contingent (f : Form) : Bool :=
  sorry

example : (Form.atom "q").satisfiable = true := by
  sorry

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

def Form.implies (f g : Form) : Bool :=
  (Form.conj f (.neg g)).contradiction

def Form.equivalent (f g : Form) : Bool :=
  f.implies g && g.implies f

-- ### Exercise (2 stars): equiv-cases ⭐⭐

-- Complete a definição de `Feq2` com uma fómula equivalente a `Feq1` e feche
-- o exemplo com `native_decide`.

def p : Form := Form.atom "p"
def q : Form := Form.atom "q"

def Feq1 : Form := Form.neg (.equi p q)
def Feq2 : Form := sorry

example : Feq1.equivalent Feq2 := by
  sorry

-- A semântica da lógica proposicional também pode ser dada em formato de
-- **atualização**. Fixe primeiro um conjunto de valorações como estado
-- corrente e depois defina uma função de atualização que deixa apenas as
-- valorações que satisfazem uma dada fórmula.

def update (vals : List Valuation) (f : Form) : List Valuation :=
  vals.filter (fun v => f.eval v)

-- Atualizar o estado de todas as valorações com uma contradição não deixa
-- nada; atualizar com uma tautologia não tira nada. Atualizar com uma fórmula
-- contingente tira alguma coisa, e atualizar com sua negação tira o
-- complemento.

#eval form1.allVals
#eval (update form1.allVals form1)
#eval (update form1.allVals (.neg form1))
#eval (update form2.allVals (.neg form2))

-- ### Exercise (2 stars): implies-list ⭐⭐

-- Estenda a checagem de implicação proposicional para o caso de uma lista de
-- premissas. O tipo é `Form.impliesL : List Form → Form → Bool`.

def Form.impliesL (ps : List Form) (c : Form) : Bool :=
  sorry

-- ### Exercise (1 star): bangu-proof ⭐

-- Complete a definição de `banguSolution` para que a fórmula represente a
-- solução do problema dos torcedores do Bangu F.C. assumindo que os 3
-- depoimentos foram verdadeiros. A prova do exemplo é completada com
-- `native_decide`.

def banguSolution : Form := sorry

example : Form.impliesL [depo1, depo2, depo3] banguSolution = true :=
  by sorry

-- ## Traduzindo `Form` para `Prop`

-- O mapeamento de `Form` em `Prop` pode ser definido como uma função que
-- interpreta cada fórmula como a proposição que ela afirma, dada uma
-- valoração.

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
-- proposição, o `neg` vira o `¬`. O teorema que fecha o capítulo diz que as
-- duas leituras concordam. Dada uma valoração, computar o valor verdade de
-- uma fórmula resulta em `true` exatamente quando a proposição resultande da
-- fórmula para a mesma valoração tem prova.

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

end PL

