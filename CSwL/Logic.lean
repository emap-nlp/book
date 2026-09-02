import CSwLCompat
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

-- # Lógica

-- Como preparação para a semântica de fragmentos de inglês, introduzimos a
-- lógica proposicional e a lógica de predicados, e mostramos como implementar
-- sua sintaxe em Lean.

-- ## Lógica proposicional

namespace PL

-- ### Introdução

-- A lógica proposicional (ou cálculo sentencial) trata de fórmulas
-- construídas a partir de variáveis proposicionais usando os conectivos `¬`,
-- `∧`, `∨`, `→` e `↔`. Intuitivamente, uma variável proposicional `p`
-- representa uma sentença ou proposição que pode ser verdadeira ou falsa.
-- Queremos usar lógica proposicional para fugir das impressões das linguas
-- naturais. Formalizar proposições e provas quando podemos concluir uma
-- proposição a partir de outras proposições tomadas como premissas.

-- Como primeiro exemplo, a sentença "traços de potássio foram observados"
-- pode ser traduzida para a linguagem formal como o símbolo `K`. Já para a
-- sentença fortemente relacionada "traços de potássio não foram observados",
-- podemos usar `¬ K`. Aqui `¬` é o nosso símbolo de negação, lido como "não".
-- Poderíamos também pensar em traduzir "traços de potássio não foram
-- observados" por algum símbolo novo `J`, mas preferimos decompor sentenças
-- em suas partes atômicas tanto quanto possível. Para uma sentença não
-- relacionada, "a amostra continha cloro" escolhemo o símbolo `C`. Assim, as
-- seguintes sentenças compostas podem ser formalizadas.

-- - A sentença "Se traços de potássio foram observados, então a amostra não
--   continha cloro." é formalizada como `(K → (¬C))` com símbolo `→`
--   significando "if ... then ...".

-- - A sentença "A amostra continha cloro, e traços de potássio foram
--   observados." é formalizada como `(C ∧ K)` com símbolo `∧` significando a
--   conjunção "e".

-- - A sentença "Ou traços de potássio não foram observados, ou a amostra não
--   continha cloro." formalizamos como `((¬K) ∨ (¬C))` com símbolo `∨`
--   significando a disjunção "ou".

-- - E a sentença "Nem a amostra continha cloro, nem traços de potássio foram
--   observados." é formalizada como `(¬(C ∨ K))` ou `((¬C) ∧ (¬K))`, são
--   **equivalentes**.

-- Sempre que nos é dada a verdade ou falsidade das partes atômicas de uma
-- sentença, podemos calcular a verdade ou falsidade da sentença. Suponha, por
-- exemplo, que um químico saia do laboratório e anuncie que observou traços
-- de potássio, mas que a amostra não continha cloro. A partir destas
-- afirmações, podemos então determinar quais das sentenças acima são
-- verdadeiras ou falsas. De fato, podemos construir uma tabela analisando os
-- valores das sentenças para cada possível combinação possível dos valores
-- verdade das proposições atômicas.

-- - `K`
-- - `C`
-- - `(¬(C ∨ K))`
-- - `((¬C) ∧ (¬K))`
-- - F
-- - F
-- - T
-- - T
-- - F
-- - T
-- - F
-- - T
-- - T
-- - F
-- - F
-- - F
-- - T
-- - F
-- - F
-- - F

-- _Quiz:_

-- Três irmãs - Ana, Maria e Cláudia — foram a uma festa com vestidos de cores
-- diferentes. Uma vestiu azul, a outra pranco, e a terceira, preto.

-- Chegando à festa, o anfitrião perguntou quem era cada uma delas.

-- - A de azul respondeu: "Ana é a que está de branco";
-- - A de branco disse: "Eu sou Maria";
-- - A de preto respondeu: "Cláudia é quem está de branco".

-- O anfitrião foi capaz cada irmã considerando que:

-- - Ana sempre diz a verdade;
-- - Maria às vezes diz a verdade;
-- - Cláudia nunca diz a verdade.

-- Podemos formalizar o problema anterior em LP. Uma das motivação é tornar a
-- argumentação precisa e convincente e, se possível, mecânica.

-- Para isso, primeiro precisamos identificar as proposições mais elementares
-- do problema e associar cada proposição a um símbolo. Em seguida, precisamos
-- formalizar cada afirmação (ou enunciado) do problema como uma fórmula em
-- LP. Vamos chamar de `Γ` o conjunto destas fórmulas. Também precisamos
-- formalizar a resposta em uma fórmula em LP, vamos chamar de `α`.

-- Finalmente, precisamos de um método para definir se a fórmula `α` é
-- **consequência** das premissas `Γ`. Um dos métodos possíveis é semântico.
-- Quando para toda possível escolha de valores verdade para os símbolos
-- proposicionais, sempre que todas as premissas forem **verdade** a conclusão
-- deve ser **verdade**. Usamos a notação `Γ ⊧ α` para indicar que `α` é
-- consequência das premissas.

-- No problema dos vestidos, o número de personagens e atributos é finito,
-- portanto há apenas um número finito de possíveis proposições. Os números
-- também são pequenos o suficiente para que análise sistemática de todas as
-- combinações de valores verdade seja possível. Para demonstrar que todo
-- número par maior que dois pode ser escrito como uma soma de números primos
-- esta estratégia não seria válida.

-- ### Lógica Proposicional em Lean

-- O Lean possui `Prop`, como tipo predefinido, cujos elementos são
-- proposições. Os conectivos lógicos `∧`, `∨`, `→`, `↔` e `¬` estão
-- disponíveis diretamente no Lean, de modo que uma fórmula proposicional pode
-- ser representada como uma proposição em Lean. Isso nos fornece uma ponte
-- conveniente entre a semântica da linguagem natural e o raciocínio formal.
-- Podemos traduzir o conteúdo semântico de uma sentença para uma proposição
-- em Lean e, em seguida, usar Lean para verificar se uma conclusão decorre de
-- um conjunto de hipóteses.

-- Continuando a partir do quiz anterior. Para começar, vamos introduzir
-- variábeis do tipo `Prop`, cada uma delas representado uma proposição. São 3
-- pessoas e 3 cores. Vamos representar "Ana veste azul" por `Aa` e assim por
-- diante.

variable (
   Aa Ab Ap
   Ma Mb Mp
   Ca Cb Cp  : Prop)

-- A ideia é que as condições do problema sejam traduzidas em fórmulas
-- proposicionais. Por exemplo, podemos formalizar a sentença "Ana veste azul,
-- branco ou preto" com a fórmula em LP.

#check Aa ∨ Ab ∨ Ap

-- Aqui cabe a observação de que a formalização em LP não foi obtida
-- diretamente a partir da construção linguística original, uma oração
-- coordenando seus constituintes no predicado. Intuitivamente, a sentença foi
-- antes interpretada como três orações coordenadas (proposições completas),
-- "Ana veste azul ou Ana vestre branco ou Ana veste preto".

-- A formalização completa do problema deve levar em consideração não apenas o
-- que foi dito explicitamente mas algumas condições implicitamente assumidas.
-- Definimos a estrutura `Premissas` por conveniência, ao invés de uma
-- variável por premissa.

structure Premissas : Prop where
   -- cada pessoa veste algum vestido
   hA : Aa ∨ Ab ∨ Ap
   hM : Ma ∨ Mb ∨ Mp
   hC : Ca ∨ Cb ∨ Cp

   -- cada vestido é de alguma pessoa
   ha : Ma ∨ Aa ∨ Ca
   hb : Ab ∨ Mb ∨ Cb
   hp : Ap ∨ Mp ∨ Cp

   -- uma pessoa veste apenas um vestido
   hA1 : (Aa → ¬ Ab ∧ ¬ Ap) ∧ (Ab → ¬ Aa ∧ ¬ Ap) ∧ (Ap → ¬ Aa ∧ ¬ Ab)
   hM1 : (Ma → ¬ Mb ∧ ¬ Mp) ∧ (Mb → ¬ Ma ∧ ¬ Mp) ∧ (Mp → ¬ Ma ∧ ¬ Mb)
   hC1 : (Ca → ¬ Cb ∧ ¬ Cp) ∧ (Cb → ¬ Ca ∧ ¬ Cp) ∧ (Cp → ¬ Ca ∧ ¬ Cb)

   -- cada vestido é de apenas uma pessoa
   ha1 : (Ma → ¬ Aa ∧ ¬ Ca) ∧ (Ca → ¬ Aa ∧ ¬ Ma) ∧ (Aa → ¬ Ma ∧ ¬ Ca)
   hb1 : (Mb → ¬ Ab ∧ ¬ Cb) ∧ (Cb → ¬ Ab ∧ ¬ Mb) ∧ (Ab → ¬ Mb ∧ ¬ Cb)
   hp1 : (Mp → ¬ Ap ∧ ¬ Cp) ∧ (Cp → ¬ Ap ∧ ¬ Mp) ∧ (Ap → ¬ Mp ∧ ¬ Cp)

   -- resposta 1
   h1 : Aa → Ab
   h2 : Ca → ¬ Ab

   -- resposta 2
   h3 : ¬ Ab

   -- resposta 3
   h4 : Ap → Cb
   h5 : Cp → ¬ Cb

-- Podemos então enunciar o problema do quiz na forma do teorema abaixo. Neste
-- caso,

theorem vestidos (h : Premissas Aa Ab Ap Ma Mb Mp Ca Cb Cp)
  : Ap ∧ Cb ∧ Ma := sorry

-- Consultar o tipo deste teorema com `#check vestidos` nos revela que ele tem
-- o formato de uma implicação, que pode ser lido como `Γ ⊢ α` Do conjunto `Γ`
-- de premissas em `Premissas` posso **derivar** `Ap ∧ Cb ∧ Ma`. A leitura é
-- sintática. Podemos construir a prova de `α` a partir da aplicação de regras
-- de dedução a partir das fómulas de `Γ`.

-- Chamamos "sistema dedutivo" um conjunto das regras de dedução. Existem
-- vários sistemas dedutivos. A formalização de Prop em Lean corresponde a
-- implementação do sistema chamado **dedução natural** definido por Gerhard
-- Gentzen em 1930s.

-- Neste sistema dedutivo, cada conectivo vem com dois tipos de regra: as de
-- **introdução**, que dizem como construir uma prova cuja conclusão usa o
-- conectivo, e as de **eliminação**, que dizem como usar uma prova cuja
-- hipótese o usa.

variable {P Q R : Prop}

-- A regra de introdução de `→` diz que para provar `P → Q`, supomos `P` e
-- derivamos `Q`. A tatica `intro` move o antecedente para as hipóteses. A
-- regra de eliminação é a chamada regra **modus ponens**. De `P → Q` e de
-- `P`, conclua `Q`. Em Lean isso é aplicação `h hP` já é a prova de `Q`. A
-- tática `apply` faz o mesmo de trás para frente, ela transforma o objetivo
-- `Q` no objetivo `P`.

example : P → (Q → P) := by
  intro hP hQ
  exact hP

example (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  intro hP
  apply h₂
  apply h₁
  exact hP

example (h : P → Q) (hP : P) : Q := h hP

-- Para a conjunção. Provar `P ∧ Q` depende de uma prova de `P` e `Q`. A
-- tática `constructor` parte o objetivo em dois; o construtor anônimo
-- `⟨_, _⟩` faz o mesmo em forma de termo. A eliminação de `∧` em `P ∧ Q`
-- significa que podemos concluir `P` ou `Q`. São duas regras, e em Lean são
-- as projeções `.1` (ou `.left`) e `.2` (ou `.right`). A tática `obtain`
-- desmonta a hipótese de uma vez, dando nome às duas partes.

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
example (hP : P) (hQ : Q) : P ∧ Q := And.intro hP hQ

example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

example (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

-- Para provar `P ∨ Q` basta provar um dos dois lados. São duas regras, e as
-- táticas `left` e `right` escolhem qual. A eliminação de `∨` é a prova por
-- casos. De `P ∨ Q` não se sabe qual dos dois vale. Para concluir `R` a
-- partir dela é preciso concluir `R` nos dois casos. A tática `cases` abre
-- exatamente esses dois objetivos.

example (hP : P) : P ∨ Q := by
  left
  exact hP

example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hP => right; exact hP
  | inr hQ => left; exact hQ

-- Não há um conectivo primitivo para a negação: `¬ P` é notação para
-- `P → False` onde `False` é a proposição sem nenhuma prova. A introdução de
-- `¬` é a introdução de `→`, para provar `¬P`, suponha `P` e derive `False`.
-- A eliminação é a eliminação de `→`. A regra que a tradição chama de **ex
-- falso quodlibet** (princípio da explosão), é uma regra que dita que, a
-- partir de uma contradição ou de uma premissa falsa, qualquer conclusão pode
-- ser deduzida. `False.elim` em Lean. As duas juntas são `absurd`.

example (h : P → Q) : ¬Q → ¬P := by
  intro hnQ hP
  exact hnQ (h hP)

example (hP : P) (hn : ¬P) : False := hn hP
example (h : False) : P := False.elim h
example (hP : P) (hn : ¬P) : Q := absurd hP hn

-- A `P ↔ Q` é a conjunção das duas implicações, e as regras seguem disso. A
-- tática `constructor` parte o objetivo nas duas direções, e `.mp` e `.mpr`
-- são as eliminações de `P → Q` e de `Q → P`.

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

example (h : P ↔ Q) (hP : P) : Q := h.mp hP

-- Até aqui não usamos em nenhum momento "ou `P` vale ou não vale". Todas as
-- regras até aqui são **construtivas**, uma prova de `P ∨ Q` traz consigo
-- qual dos dois lados foi usado. Uma prova de `P` é uma construção de `P`. O
-- raciocínio **clássico** acrescenta o princípio chamado de terceiro
-- excluído. Dele saem as duas táticas. A primeira é `by_cases`, que parte a
-- prova em dois casos, supondo `P` num e `¬P` no outro. E a tatica
-- `by_contra` prova `P` supondo `¬P` e derivando `False`, a redução ao
-- absurdo.

example : P ∨ ¬P := Classical.em P

example : ¬¬P → P := by
  intro h
  by_cases hP : P
  · exact hP
  · exact absurd hP h

example (h : ¬¬P) : P := by
  by_contra hn
  exact h hn

-- ### Exercise (1 star): contrapositive ⭐

-- Prove a contrapositiva. Só uma das direções precisa de raciocínio clássico.

example : (P → Q) ↔ (¬Q → ¬P) := sorry

-- ### Exercise (2 stars): de-morgan ⭐⭐

-- Uma das leis de De Morgan vale construtivamente; a outra precisa do
-- terceiro excluído.

example : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := sorry

example : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := sorry

-- ### Exercise (1 star): exchange-prop ⭐

-- Complete a representação do argumento abaixo em linguagem lógica.

-- Se o câmbio cair, temos inflação. Se as exportações crescerem, diminuímos o
-- déficit. O câmbio cai ou diminuímos o déficit. Logo, temos inflação ou as
-- exportações crescem.

section

variable (
  p -- o câmbio cai
  q -- temos inflação
  r -- as exportações crescem
  s -- Diminuimos o déficit
  : Prop)

def exchange : Prop :=
  sorry → (q ∨ r)

end

-- ### Exercise (2 stars): dresses ⭐⭐

-- Complete a prova do teorema que resposta do quiz anterior.

theorem vestidos₁ (h : Premissas Aa Ab Ap Ma Mb Mp Ca Cb Cp)
  : Ap ∧ Cb ∧ Ma := by
  obtain
    ⟨hA, hM, hC, ha, hb, hp, hA1, hM1,
     hC1, ha1, hb1, hp1, h1, h2, h3, h4, h5⟩ := h

  -- Ana não está de azul: se estivesse, por `h1` ela estaria de branco, mas Ana
  -- não está de branco por `h3`.
  have hnAa : ¬ Aa := by
    sorry

  have hAp : Ap := by
   cases hA with
   | inl hAa => exact absurd hAa hnAa
   | inr hx =>
     cases hx with
     | inl hAb => exact absurd hAb h3
     | inr hAp => exact hAp

  have hCb : Cb := sorry

  have hnCa : ¬ Ca := sorry

  have hMa : Ma := by
    sorry

  exact ⟨hAp, hCb, hMa⟩

-- ### Sintaxe

-- Em Lean, `Prop` é um tipo e proposições particulares também são tipos. A
-- variável `h` abaixo pode ser entendida como um identificador para uma
-- "prova qualquer" da proposição `Aa ∨ Ab ∨ Ap`.

#check Aa ∨ Ab ∨ Ap
variable (h : Aa ∨ Ab ∨ Ap)

-- Mas Lean adota o princípio da "irrelevância da prova", ou seja, Lean não
-- distingue diferentes provas de uma proposição. Como consequência, o tipo
-- `Prop` não é computável, não é um "dado" que pode ser manipulado. Por
-- exemplo, não conseguimos extrair os componentes de uma conjunção `a ∧ b`,
-- para fora do tipo `Prop`. Lean proíbe a extração de `Prop` para `Type`, ele
-- sabe que todas as provas de `a ∧ b` são irrelevantes e iguais, então ele
-- não permite que você use uma prova para tomar decisões no mundo dos dados
-- programáveis (`Type`).

sf_expect_failure
  variable (a b : Prop)
  
  def cannotExtractLeft (h : a ∧ b) : Type :=
    match h with
    | And.intro ha hb => ha

-- Como vamos precisar manipular fórmulas lógicas, teremos que definir um tipo
-- de dado para representar fórmulas proposicionais.

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
-- conectivos precisam ser definidos como "primitivos". Em algumas
-- apresentações, o conectivo `→` é definido como uma abreviação para
-- `p → q ≃ ¬ p ∨ q`.

-- Como anteriormente, iremos formalizar a gramática acima como um tipo
-- indutivo. Um átomo é identificado por um nome, e o nome é uma `String`.
-- Isso dá o inventário ilimitado que a gramática pede sem precisar enumerar
-- símbolo por símbolo.

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
-- os símbolos `→` e `↔` como construtores do tipo, eles serão funçòes que
-- criam `Form` a partir de `Form`.

def Form.impl (f g : Form) : Form := .disj (.neg f) g
def Form.equi (f g : Form) : Form :=
  .conj (Form.impl f g) (Form.impl g f)

-- A conjunção e a disjunção são binárias. Poderiam receber uma lista de
-- fórmulas `conj (fs : List Form)`, mas um construtor que guarda uma
-- `List Form` dentro do próprio tipo o torna um indutivo *nested*, mais
-- complicado em Lean. Mas podemos definir funções que recebem listas de
-- fórmulas e constrem conjunções e disjunções. Abaixo `top`/`bot` são a base
-- da recursão de `conjs`/`disjs`. Uma conjunção vazia é sempre verdadeira,
-- uma disjunção vazia é sempre falsa.

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
-- fórmula.

def Form.opsNr : Form → Nat :=
  sorry

theorem opsNr_test : form1.opsNr = 2 := by decide

-- ### Exercise (1 star): formula-depth ⭐

-- Implemente uma função `depth` para calcular a profundidade da árvore de
-- análise de uma fórmula.

def Form.depth : Form → Nat :=
  sorry

theorem depth_test : form1.depth = 2 := sorry

-- ### Exercise (2 stars): collect-atoms ⭐⭐

-- Implemente `propNames` para coletar a lista de nomes de átomos
-- proposicionais que ocorrem numa fórmula. A lista resultante deve estar
-- ordenada e sem repetições.

private def Form.propNamesRaw : Form → List String :=
  sorry

def Form.propNames (f : Form) : List String :=
  sorry

-- ### Semântica

-- Vimos que a noção de "derivação" é diretamente implementada no Lean. Isto
-- é, dizemos que `P ∧ Q ⊢ P` porque conseguimos construir uma prova de `P` a
-- partir da existência de uma prova de `P ∧ Q`.

-- Mas as regras de derivação que usamos correspondem a (ou são justificadas
-- por) uma noção semântica de **consequência lógica**, `P ∧ Q ⊧ P`.
-- Entendemos que `P` deve ser verdade sempre que `P ∧ Q` for verdade, para
-- qualquer possível tradução de `P` e `Q` de volta para expressões em uma
-- linguagem natural. Para formalizar esta noção de "todas as possíveis
-- traduções", vamos precisar de um processo para avaliar fórmulas lógicas em
-- valores verdade.

-- Vamos chamar de **valorações** um mapeamento de símbolos proposicionais no
-- conjunto dos booleanos, que em Lean correspondem aos valores `True` e
-- `False` do tipo `Bool`.

-- Uma valoração é uma lista de pares, e um átomo ausente da lista conta como
-- falso.

abbrev Valuation := List (String × Bool)

-- Se `V` é uma valoração, ela se estende a uma função que mapea qualquer
-- fórmula para um valor de verdade. A extensão é definida por recursão sobre
-- a estrutura da fórmula, um caso por construtor. Os construtores `top` e
-- `bot` são constantes, nenhuma valoração os afeta.

def Form.eval (f : Form) (v : Valuation) : Bool :=
  match f with
  | .atom name => (v.lookup name).getD false
  | .top => true
  | .bot => false
  | .neg g => !g.eval v
  | .conj g h => g.eval v && h.eval v
  | .disj g h => g.eval v || h.eval v

-- Chamamos de **tautologias** (válidas) as fórmulas que são sempre verdade,
-- independente da valoração. A notação usual para "`α` é uma tautologia" é
-- `⊨ α`. As fórmulas que são sempre falsas para toda valoração são chamadas
-- de **contradições** (ou insatisfatíveis) e podemos concluir que se `α` é
-- uma contradição, então `⊨ ¬ α` (sua negação é válida). Uma fórmula é
-- **satisfatível** se há ao menos uma valoração que a torna verdadeira,
-- escrevemos `⊭ α` se existe pelo menos uma valoração que torna `α` falsa.
-- Uma fórmula é **contingente** se é satisfatível mas não é uma tautologia.
-- Toda tautologia é satisfatível, mas nem toda fórmula satisfatível é uma
-- tautologia.

def taut  : Form :=  (.disj (.atom "p") (.neg (.atom "p")))
def unsat : Form :=  (.conj (.atom "p") (.neg (.atom "p")))

#eval taut.eval [("p1", True)]
#eval taut.eval [("p1", False)]
#eval unsat.eval [("p", False)]
#eval unsat.eval [("p", True)]

-- A função a seguir gera a lista de todas as valorações sobre o conjunto dos
-- nomes de átomos presentes em um termo do tipo `Form`. Com estas funções,
-- podemos construir a tabela verdade de uma fórmula.

def genVals : List String → List Valuation
  | [] => [[]]
  | name :: names =>
      (genVals names).map ((name, true) :: ·)
      ++ (genVals names).map ((name, false) :: ·)

def Form.allVals (f : Form) : List Valuation :=
  genVals f.propNames

#eval List.zip form2.allVals (form2.allVals.map (form2.eval ·))

-- Para decidir se uma fórmula é tautologia, satisfatível ou contradição,
-- podemos percorrer todas as valorações relevantes, que são finitas, porque
-- uma fórmula tem finitos átomos.

def Form.tautology (f : Form) : Bool :=
  f.allVals.all (fun v => f.eval v)

def Form.satisfiable (f : Form) : Bool :=
  f.allVals.any (fun v => f.eval v)

def Form.contradiction (f : Form) : Bool :=
  !f.satisfiable

#eval (form1.contradiction,
       (Form.neg form1).tautology,
       form2.satisfiable)

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

-- A nossa definição de `Form.impl` acima pode ser justificada pelas
-- equivalência abaixo. A relação de equivalência entre fórmulas é transitiva.

#eval
  let p := (.atom "p")
  let q := (.atom "q")

  let α := (Form.impl p q)
  let β := Form.disj (.neg p) q
  let γ := Form.neg $ .conj p (.neg q)

  let r1 := [Form.equivalent α β, Form.equivalent β γ, Form.equivalent α γ]
  let r2 := [Form.implies p (.disj p q), (Form.impl p (.disj p q)).tautology]
  let r3 := [Form.implies (.disj p q) p, (Form.impl (.disj p q) p).tautology]
  let r4 := [Form.implies (Form.conj p (.neg p)) q]
  (r1, r2, r3, r4)

-- A semântica da lógica proposicional também pode ser dada em formato de
-- **atualização**. Fixe primeiro um conjunto de valorações relevantes como
-- estado corrente e depois defina uma função de atualização que deixa apenas
-- as valorações que satisfazem uma dada fórmula.

def update (vals : List Valuation) (f : Form) : List Valuation :=
  vals.filter (fun v => f.eval v)

-- Atualizar o estado de todas as valorações relevantes com uma contradição
-- não deixa nada; atualizar com uma tautologia não tira nada. Atualizar com
-- uma fórmula contingente tira alguma coisa, e atualizar com sua negação tira
-- o complemento.

#eval (update form1.allVals form1)
#eval (update form1.allVals (.neg form1))
#eval (form2.allVals.length,
       (update form2.allVals form2).length,
       (update form2.allVals (.neg form2)))

-- ### Exercise (1 star): valuation-table ⭐

-- Seja `V` dada por `p ↦ 0`, `q ↦ 1`, `r ↦ 1`. Dê os valores das fórmulas
-- seguintes: `¬p ∨ p`, `p ∧ ¬p`, `¬¬(p ∨ ¬r)`, `¬(p ∧ ¬r)`, `p ∨ (q ∧ r)`.

namespace ValuationTableEx

def p := Form.atom "p"
def q := Form.atom "q"
def r := Form.atom "r"

def vs : Valuation :=
  [("p", false), ("q", true), ("r", true)]

example :
 (Form.disj (.neg p) p).eval vs = sorry :=
 by decide

example :
 (Form.neg (.neg (.conj p (.neg r)))).eval vs = sorry :=
 by decide

example :
 (Form.neg (.conj p (.neg r))).eval vs = sorry :=
 by decide

example :
 (Form.disj p (.conj q r)).eval vs = sorry :=
 by decide

end ValuationTableEx

-- ### Exercise (1 star): negated-tautology ⭐

-- Explique por que a negação de uma tautologia é sempre uma contradição, e
-- vice-versa.

-- ### Exercise (2 stars): implies-list ⭐⭐

-- Estenda a checagem de implicação proposicional para o caso de uma lista de
-- premissas. O tipo é `Form.impliesL : List Form → Form → Bool`.

def Form.impliesL (ps : List Form) (c : Form) : Bool :=
  sorry

-- ### A ponte entre as duas leituras

-- O capítulo começou distinguindo raciocinar em lógica proposicional de
-- raciocinar sobre fórmulas dela. Temos que `p ∧ q` é uma proposição, do tipo
-- `Prop` e `Form.conj p q` é um termo (dado) do tipo `Form`. A ligação é uma
-- função que interpreta cada fórmula como a proposição que ela afirma, dada
-- uma valoração.

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
-- duas leituras concordam: computar dá `true` exatamente quando a proposição
-- vale.

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

-- ### Exercise (1 star): bangu-proof ⭐

-- Identificar os torcedores do Bangu e os não torcedores, supondo que todos
-- os depoimentos são verdadeiros.

#eval Form.impliesL [depo1, depo2, depo3] A
#eval Form.impliesL [depo1, depo2, depo3] J
#eval Form.impliesL [depo1, depo2, depo3] C

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

