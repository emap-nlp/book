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

-- A lógica proposicional (LP, ou cálculo sentencial) trata de fórmulas
-- construídas a partir de variáveis proposicionais usando os conectivos `¬`,
-- `∧`, `∨`, `→` e `↔`. Intuitivamente, uma variável proposicional `p`
-- representa uma sentença ou proposição que pode ser verdadeira ou falsa.
-- Queremos usar lógica proposicional para fugir das impressões das línguas
-- naturais. Formalizar proposições e provas quando podemos concluir uma
-- proposição a partir de outras proposições tomadas como premissas.

-- Como primeiro exemplo, adaptado de Enderton (2001), a sentença "traços de
-- potássio foram observados" pode ser traduzida para a linguagem formal como
-- o símbolo `K`. Já para a sentença fortemente relacionada "traços de
-- potássio não foram observados", podemos usar `¬ K`. Aqui `¬` é o nosso
-- símbolo de negação, lido como "não". Poderíamos também pensar em traduzir
-- "traços de potássio não foram observados" por algum símbolo novo `J`, mas
-- preferimos decompor sentenças em suas partes atômicas tanto quanto
-- possível. Para uma sentença não relacionada, "a amostra continha cloro"
-- escolhemos o símbolo `C`. Assim, as seguintes sentenças compostas podem ser
-- formalizadas.

-- - A sentença "Se traços de potássio foram observados, então a amostra não
--   continha cloro." é formalizada como `(K → (¬C))` com símbolo `→`
--   significando "se ... então ...".

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
-- - F
-- - T
-- - F
-- - F
-- - F
-- - T
-- - T
-- - F
-- - F

-- _Quiz:_

-- Três irmãs - Ana, Maria e Cláudia — foram a uma festa com vestidos de cores
-- diferentes. Uma vestiu azul, a outra branco, e a terceira, preto.

-- Chegando à festa, o anfitrião perguntou quem era cada uma delas.

-- - A de azul respondeu: "Ana é a que está de branco";
-- - A de branco disse: "Eu sou Maria";
-- - A de preto respondeu: "Cláudia é quem está de branco".

-- O anfitrião foi capaz de identificar cada irmã considerando que:

-- - Ana sempre diz a verdade;
-- - Maria às vezes diz a verdade;
-- - Cláudia nunca diz a verdade.

-- Podemos formalizar o problema anterior em LP. Uma das motivações é tornar a
-- argumentação precisa e convincente e, se possível, mecânica.

-- Para isso, primeiro precisamos identificar as proposições mais elementares
-- do problema e associar cada proposição a um símbolo. Em seguida, precisamos
-- formalizar cada afirmação (ou enunciado) do problema como uma fórmula em
-- LP. Vamos chamar de `Γ` o conjunto destas fórmulas. Também precisamos
-- formalizar a resposta em uma fórmula em LP, vamos chamar de `α`.

-- Finalmente, precisamos de um método para definir se a fórmula `α` é
-- **consequência lógica** das premissas `Γ`. Um dos métodos possíveis é
-- semântico. Quando para toda possível escolha de valores verdade para os
-- símbolos proposicionais, sempre que todas as premissas forem **verdade** a
-- conclusão deve ser **verdade**. Usamos a notação `Γ ⊧ α` para indicar que
-- `α` é consequência lógica das premissas.

-- No problema dos vestidos, o número de personagens e atributos é finito,
-- portanto há apenas um número finito de possíveis proposições. Os números
-- também são pequenos o suficiente para que análise sistemática de todas as
-- combinações de valores verdade seja viável na prática. Para demonstrar que
-- todo número par maior que dois pode ser escrito como uma soma de dois
-- números primos esta estratégia não seria válida.

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
-- variáveis do tipo `Prop`, cada uma delas representado uma proposição. São 3
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
-- "Ana veste azul ou Ana veste branco ou Ana veste preto".

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
-- de dedução a partir das fórmulas de `Γ`.

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
  sorry
end

-- ### Exercise (2 stars): dresses ⭐⭐

-- Complete a prova do teorema que responde o quiz anterior.

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
-- os símbolos `→` e `↔` como construtores do tipo, eles serão funções que
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

theorem opsNr_test : form1.opsNr = 2 := sorry

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
-- **satisfatível** se há ao menos uma valoração que a torna verdadeira. Uma
-- fórmula é **contingente** se é satisfatível mas não é uma tautologia. Toda
-- tautologia é satisfatível, mas nem toda fórmula satisfatível é uma
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

-- ### Exercise (1 star): bangu-proof ⭐

-- Como podemos identificar os torcedores do Bangu e os não torcedores,
-- supondo que todos os depoimentos são verdadeiros?

-- ### Traduzindo `Form` para `Prop`

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

end PL

-- ## Lógica de predicados

namespace FOL

-- Frases como "Todo príncipe viu uma dama" não podem ser expressas em lógica
-- proposicional — ficariam como átomos `p`/`q` totalmente desconectados, sem
-- capturar que a mesma entidade que é "príncipe" foi a que realizou o ato de
-- ver. Lógica de predicados acrescenta três ingredientes:

-- - proposições básicas, predicados `n`-ário seguidos de `n` variáveis;
-- - fórmulas universalmente quantificadas, `∀` seguido de variável e fórmula;
-- - fórmulas existencialmente quantificadas, `∃` seguido de variável e fórmula.

-- Também chamada de "lógica de primeira ordem" (FOL, "first order logic")
-- está relacionado a quantificação ser sobre entidades, objetos de primeira
-- ordem. Vamos assumir que predicados aridade até 3 (relações unárias,
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

-- Em Lean, o mesmo tipo `Prop` em Lean pode ser usado na representação de
-- fórmulas de primeira ordem. Também veremos como as fórmulas podem ser
-- manipuladas como dados.

-- ### As regras dos quantificadores em Lean

-- O Lean se baseia em na teoria dos tipos, na qual se assume que cada
-- variável pertence a algum tipo. Você pode pensar em um tipo como um
-- "universo" ou um "domínio de discurso", no sentido da lógica de primeira
-- ordem.

-- Seguindo a apresentação de Lógica Proposicional, quatro novas regras
-- precisam ser explicadas, duas para cada quantificador.

section

variable (U : Type)
variable (P Q : U → Prop)

-- A introdução de `∀` diz que para provar que algo vale de todo `x`, tome um
-- `x` arbitrário e prove que vale para ele. É a mesma `intro` agora sobre um
-- objeto em vez de uma hipótese. A eliminação de `∀` é aplicação: de
-- `∀ x P x` e de um objeto `d`, sai `P d`.

example (h : ∀ x, P x) : ∀ y, P y := by
  intro y
  exact h y

-- A introdução de `∃` exige exibir a testemunha. A tática `use` substitui a
-- variável quantificada pelo objeto passado, e deixa como objetivo o que
-- falta provar sobre ele.

example (y : U) (h : P y) : ∃ x, P x :=
  Exists.intro y h

example (y : U) (h : P y) : ∃ x, P x := by
  use y

-- A eliminação de `∃` é a mais delicada. De `∃ x P x` sabe-se que há uma
-- testemunha, mas não sabemos qual elemento do domínio ela é. A tática
-- `obtain` aplica o teorema `Exists.elim`, introduz com um nome, junto com a
-- propriedade que ele satisfaz.

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  apply Exists.elim h
  intro d hd
  use d
  exact hd.2

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  obtain ⟨d, hP, hQ⟩ := h
  exact ⟨d, hQ⟩

-- Podemos ainda considera uma lógica de múltiplos tipos, onde podemos ter
-- múltiplos universos. Por exemplo, podemos querer usar a lógica de primeira
-- ordem para geometria, com quantificadores sobre pontos e linhas. Mas acima
-- restringimos os predicados a um único universo `U`.

-- A demonstração abaixo não é válida se não declararmos uma variável `u : U`,
-- mesmo que `u` não apareça no enunciado do teorema. Isso destaca uma
-- diferença entre a lógica de primeira ordem e a lógica implementada em Lean.
-- Na dedução natural, podemos provar `∀ x P x → ∃ x P x`, o que mostra que
-- nosso sistema de prova assume implicitamente que o universo tem pelo menos
-- um objeto. Em contraste, a afirmação `(∀ x : U, P x) → ∃ x : U, P x` não é
-- demonstrável em Lean. Em outras palavras, em Lean, é possível que um tipo
-- esteja vazio, e, portanto, a prova acima requer uma suposição explícita de
-- que existe um elemento `u : U`.

variable (u : U)

example: (∀ x , P x) → ∃ x, P x := by
 intro h
 use u
 exact h u

end

-- ### Exercise (2 stars): forall-exists-swap ⭐⭐

-- Prove o primeiro exemplo.

example {U : Type} (R : U → U → Prop) :
  (∃ y, ∀ x, R x y) → (∀ x, ∃ y, R x y) :=
 sorry

-- Explique porque a volta da implicação não vale.

-- ### Ligação de variáveis

-- Numa fórmula `∀x F` (ou `∃x F`), o quantificador liga toda ocorrência de
-- `x` em `F` que não esteja já ligada por um `∀x`/`∃x` interno a `F`. Uma
-- fórmula é **aberta** se tem ao menos uma ocorrência livre de variável, e
-- **fechada** (também chamada **sentença**) caso contrário. Por exemplo,
-- `(Px ∧ ∃x Rxx)` é aberta, o `x` de `Px` está fora do escopo do `∃x`. Mas
-- `∃x (Px ∧ ∃x Rxx)` é uma sentença.

-- Essa distinção é o que motiva a ambiguidade de escopo de "Todo príncipe viu
-- uma dama". Duas leituras possíveis, "para cada príncipe existe uma dama
-- (talvez diferente) que ele viu" contra "existe uma dama que todo príncipe
-- viu", formalizadas respectivamente como:

-- ∀x (Prince x → ∃y (Lady y ∧ Saw x y))
-- ∃y (Lady y ∧ ∀x (Prince x → Saw x y))

-- Repare que a leitura universal usa `→` como conectivo principal, e a
-- existencial usa `∧`. Já "Algum príncipe viu uma dama bonita" admite apenas
-- uma formalização, `∃x∃y (Prince x ∧ Lady y ∧ Beautiful y ∧ Saw x y)`.

-- Nota editorial (Alexandre (arademaker)):
--     Em Lean, indexar por aridade é mais natural do que empilhar primos: um
--     `structure PredSymbol` com campos `name : String` e `arity : Nat` já
--     representa "infinitos predicados de cada aridade finita" sem precisar
--     de uma família de gramáticas, uma por aridade. Fica como observação,
--     `Formula` (abaixo) não adota `PredSymbol`.

-- ### O tipo Fórmulas de FOL

-- Uma variável carrega nome e um índice (lista de naturais usada para gerar
-- variáveis "frescas" a partir de uma dada variável):

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

-- E a instância de `Repr` para exibirmos fórmulas de forma legível. Note que
-- ela demanda que o tipo `α` tenha também uma instância de `Repr`.

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

#eval Formula.neg formula2
#eval (Formula.neg formula2).nnf

-- ### Símbolos de função

-- Termos denotam objetos do domínio, e diferentes termos podem denotar um
-- mesmo objeto como o termo `(5 + 3) × 4`, `8 × 4` e `32`. Para representar
-- termos mais complexos que apenas variáveis, a solução é introduzir símbolos
-- funcionais para as operações entre termos. Da mesma forma como escolhemos
-- representar relações binárias quaisquer, ao invés de fixar símbolos
-- específicos para relações como "menor que".

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

-- ### Semântica da lógica de predicados

-- Por conveniência, nos limitamos a um fragmento de língua com apenas três
-- letras de predicado: `P` (unário), `R` (binário), e `S` (ternário).

-- Como deve ser uma estrutura extralinguística para as constantes `P`, `R` e
-- `S`? Tal estrutura deve conter ao menos um domínio de discurso `D`, formado
-- por entidades individuais, com uma interpretação para `P`, para `R` e para
-- `S`. Essas interpretações são dadas por uma função `Interp`, que a cada
-- nome de predicado e a cada lista de elementos do domínio associa a
-- afirmação de que a relação vale entre eles.

abbrev Interp (D : Type) := String → List D → Prop

-- Um conjunto de símbolos de relação, com suas aridades, especifica uma
-- linguagem de lógica de predicados `L`. Uma estrutura `M = (D, I)`, formada
-- por um domínio não vazio `D` com uma função de interpretação para os
-- símbolos de relação de `L`, é chamada de **modelo** para `L`. Sempre
-- suporemos que o domínio de um modelo é não vazio.

-- Eis um modelo concreto, com domínio de três elementos. `P` vale para `1` ou
-- `3`; `R` relaciona `1` a `1` e `2`, `2` a `2`, e `3` a `1` e `2`.

def M : Interp Nat
  | "P", [d] => d = 1 ∨ d = 3
  | "R", [d, e] =>
      (d = 1 ∧ (e = 1 ∨ e = 2))
      ∨ (d = 2 ∧ e = 2)
      ∨ (d = 3 ∧ (e = 1 ∨ e = 2))
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
-- correspondente do Lean. Se avaliamos fórmulas fechadas, isto é, sem
-- variáveis livres, a atribuição `g` se torna irrelevante.

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

