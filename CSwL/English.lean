import CSwL.Logic.FOL

-- # Um fragmento de inglês

namespace English

-- ## Formas Linguísticas e Traduções para Lógica

-- — Não vejo ninguém na estrada — disse Alice.

-- — Quem dera eu tivesse olhos assim — observou o Rei, em tom lamentoso. —
-- Poder ver Ninguém! E a essa distância, ainda por cima!

-- (Carroll, 1865)

-- Da sentença **Alice walked on the road** segue-se que alguém caminhou na
-- estrada, mas de **No one walked on the road** não se segue que alguém
-- caminhou na estrada. Por isso lógicos como Gottlob Frege (1848–1925),
-- Bertrand Russell (1872–1970), Alfred Tarski (1902–1983) e Willard Van Orman
-- Quine (1908–2000) sustentaram que a estrutura dessas duas sentenças tem de
-- ser diferente, e que não basta dizer que ambas são composições de um
-- sujeito e um predicado.

-- Os lógicos que usaram a lógica de predicados de primeira ordem para
-- analisar a estrutura lógica da língua natural se impressionaram com o fato
-- de que as traduções lógicas de sentenças com expressões quantificadas não
-- pareciam acompanhar a estrutura linguística. Nas traduções lógicas, as
-- expressões quantificadas pareciam ter desaparecido. A tradução lógica de
-- (1) não revela nenhum constituinte correspondente ao sintagma nominal
-- quantificado que faz de sujeito.

-- (1)  Every dwarf loved Goldilocks.

-- (2)  ∀x (Dwarf x → Love x g)

-- Na tradução (2) o constituinte **every dwarf** desapareceu; ele foi
-- contextualmente eliminado. Frege observa que uma expressão quantificada
-- como **every dwarf** não dá origem a um conceito por si só — **eine
-- selbständige Vorstellung** —, e só pode ser interpretada no contexto da
-- tradução da sentença inteira. Considerando este exemplo em particular, a
-- paráfrase literal de (2) é:

-- Todos os objetos do domínio de discurso têm a propriedade de ou não ser
-- anões, ou ser objetos que amaram Goldilocks.

-- Nessa reformulação da sentença (1), o sintagma **every dwarf** não ocorre
-- mais.

-- As propriedades lógicas das sentenças que envolvem expressões quantificadas
-- — e descrições, analisadas em termos de quantificadores — sugeriam, de
-- fato, que o modo como um sintagma nominal simples, como um nome próprio, se
-- combina com um predicado é logicamente diferente do modo como um sintagma
-- nominal quantificado ou uma descrição definida se combina com um predicado.
-- Isso levou à crença de que a forma linguística das expressões da língua
-- natural era enganosa.

-- A aplicação das ferramentas lógicas de abstração e redução do cálculo
-- lambda nos permite ver que essa conclusão era injustificada. Traduzindo a
-- língua natural em expressões de uma lógica tipada, veremos que os
-- constituintes da língua natural correspondem a expressões tipadas que se
-- combinam umas com as outras como funções e argumentos. Depois da redução
-- completa dos resultados, as expressões quantificadas e outros constituintes
-- podem ter sido contextualmente eliminados, mas essa eliminação é resultado
-- do processo de redução, e não da suposta forma enganosa da sentença
-- original. Assim, embora as traduções lógicas completamente reduzidas de
-- sentenças da língua natural possam ser enganosas em algum sentido, as
-- expressões originais, não reduzidas, não são.

-- Como exemplo do modo como as ferramentas do cálculo lambda aplainam as
-- aparências lógicas, considere a lógica da combinação de sujeitos e
-- predicados. Nos casos mais simples — como **Goldilocks laughed** —
-- poderíamos dizer que o predicado toma o sujeito como argumento. Mas isso
-- não funciona para sujeitos quantificados, como em **no one laughed**. Tudo
-- se resolve, porém, se dissermos que o sujeito sempre toma o predicado como
-- seu argumento, e fizermos isso valer também para os sujeitos simples,
-- elevando logicamente seu estatuto de argumento a função. Com expressões
-- lambda isso é bastante fácil: traduzimos **Goldilocks** não como a
-- constante `g`, e sim como a expressão `λP ↦ P g`. Essa expressão denota uma
-- função de propriedades em valores de verdade, e pode portanto tomar a
-- tradução de um predicado como argumento. A tradução de **no one** é do
-- mesmo tipo:

-- λP ↦ ¬∃x (Person x ∧ P x)

-- Antes da redução, as traduções de **Goldilocks laughed** e de **no one
-- laughed** se parecem muito. As semelhanças só desaparecem depois que as
-- duas traduções são reduzidas às suas formas mais simples.

-- Em FOL como linguagem de representação demonstramos isso construindo
-- fórmulas da lógica de predicados como traduções das sentenças da língua
-- natural geradas pelo fragmento de Um fragmento do inglês. Essa tradução é o
-- primeiro passo para interpretar indiretamente as expressões da língua
-- natural. O passo seguinte, em Uma estrutura de primeira ordem, é atribuir
-- às fórmulas da lógica de predicados um objeto modelo-teórico como
-- denotação. Desse modo, a expressão da língua natural representada recebe
-- uma interpretação modelo-teórica. No caminho, veremos as limitações desse
-- procedimento.

-- ## Um fragmento do Inglês

-- Suponha que queiramos escrever regras gramaticais para sentenças do inglês
-- como as seguintes:

-- 1. The girl laughed.
-- 2. No dwarf admired some princess that shuddered.
-- 3. Every girl that some boy loved cheered.
-- 4. The wizard that helped Snow White defeated the giant.

-- O que precisamos é de uma regra para a estrutura sujeito–predicado das
-- sentenças, uma regra para a estrutura interna dos sintagmas nominais, uma
-- regra para os substantivos comuns com ou sem orações relativas, e é mais ou
-- menos só isso. A gramática a seguir dá conta dos exemplos:

-- S   ::= NP VP ;
-- NP  ::= "Snow White" | "Alice" | "Dorothy" | "Goldilocks" | "Little Mook" | "Atreyu"
--       | "everyone" | "someone" | DET CN | DET RCN ;
-- DET ::= "a" | "the" | "every" | "some" | "no" ;
-- CN  ::= "girl" | "boy" | "princess" | "dwarf" | "giant" | "wizard" | "sword" | "dagger" ;
-- ADJ ::= "fake" | "happy" | "evil" ;
-- RCN ::= CN "that" VP | CN "that" NP TV | ADJ CN ;
-- VP  ::= "laughed" | "cheered" | "shuddered" | TV NP | DV NP NP ;
-- TV  ::= "loved" | "admired" | "helped" | "defeated" | "caught" ;
-- DV  ::= "gave" ;

-- Isto é muito básico e grosseiro, claro, mas dá uma idéia de como seria uma
-- gramática para um fragmento do inglês.

-- A tradução para Lean é direta: cada não-terminal da gramática vira um tipo
-- indutivo, e cada alternativa de uma regra vira um construtor desse tipo. Um
-- valor do tipo `Sent` não é uma sequência de palavras, é a árvore de análise
-- de uma sentença — a estrutura que a gramática atribui a ela.

-- Começamos pelos não-terminais cujas alternativas são todas palavras. Eles
-- não dependem de nenhum outro não-terminal, e por isso podem ser declarados
-- isoladamente. Junto de cada um declaramos a instância de `ToString` que
-- devolve a palavra correspondente.

inductive DET where
  | a | the | every | some | no
deriving Repr

instance : ToString DET :=
  ⟨fun | .a => "a" | .the => "the" | .every => "every"
       | .some => "some" | .no => "no"⟩

inductive CN where
  | girl | boy | princess | dwarf | giant | wizard
  | sword | dagger
deriving Repr

instance : ToString CN :=
  ⟨fun | .girl => "girl" | .boy => "boy"
       | .princess => "princess" | .dwarf => "dwarf"
       | .giant => "giant" | .wizard => "wizard"
       | .sword => "sword" | .dagger => "dagger"⟩

inductive ADJ where
  | fake | happy | evil
deriving Repr

instance : ToString ADJ :=
  ⟨fun | .fake => "fake" | .happy => "happy"
       | .evil => "evil"⟩

inductive TV where
  | loved | admired | helped | defeated | caught
deriving Repr

instance : ToString TV :=
  ⟨fun | .loved => "loved" | .admired => "admired"
       | .helped => "helped" | .defeated => "defeated"
       | .caught => "caught"⟩

inductive DV where
  | gave
deriving Repr

instance : ToString DV := ⟨fun | .gave => "gave"⟩

inductive That where
  | that
deriving Repr

instance : ToString That := ⟨fun | .that => "that"⟩

-- O tipo `That` tem um único construtor e não carrega informação alguma. Ele
-- está ali porque a palavra **that** ocupa uma posição na regra de `RCN`, e
-- queremos que a árvore de análise registre essa posição como registra as
-- outras.

-- Os quatro não-terminais restantes se referem uns aos outros: `S` usa `NP` e
-- `VP`, `NP` usa `RCN`, `RCN` usa `VP` e `NP`, e `VP` usa `NP`. Nenhum deles
-- pode ser declarado antes dos outros, e por isso os quatro vão para um mesmo
-- bloco `mutual`, como fizemos em FOL para funções que se chamam mutuamente.

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks
    | littleMook | atreyu
    | everyone | someone
    | npDet (det : DET) (cn : CN)
    | npDetRel (det : DET) (rcn : RCN)
  deriving Repr

  inductive RCN where
    | rcnSubj (cn : CN) (compl : That) (vp : VP)
    | rcnObj (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcnAdj (adj : ADJ) (cn : CN)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vpTrans (tv : TV) (np : NP)
    | vpDitrans (dv : DV) (iobj dobj : NP)
  deriving Repr
end

-- Os nomes dos construtores dizem qual alternativa da regra cada um
-- implementa. Em `RCN`, `rcnSubj` é a oração relativa em que o substantivo
-- modificado faz o papel de sujeito — **girl that laughed** —, e `rcnObj`
-- aquela em que ele faz o papel de objeto — **girl that some boy loved**.
-- Essa diferença vai reaparecer quando dermos a semântica do fragmento.

-- Falta o caminho de volta: dada a árvore, recuperar a sentença de
-- superfície. As funções que fazem isso se chamam umas às outras exatamente
-- como os tipos, e por isso também vão para um bloco `mutual`.

mutual
  def Sent.toText : Sent → String
    | .sent np vp => s!"{np.toText} {vp.toText}"

  def NP.toText : NP → String
    | .snowWhite => "Snow White"
    | .alice => "Alice"
    | .dorothy => "Dorothy"
    | .goldilocks => "Goldilocks"
    | .littleMook => "Little Mook"
    | .atreyu => "Atreyu"
    | .everyone => "everyone"
    | .someone => "someone"
    | .npDet det cn => s!"{det} {cn}"
    | .npDetRel det rcn => s!"{det} {rcn.toText}"

  def RCN.toText : RCN → String
    | .rcnSubj cn compl vp => s!"{cn} {compl} {vp.toText}"
    | .rcnObj cn compl np tv =>
      s!"{cn} {compl} {np.toText} {tv}"
    | .rcnAdj adj cn => s!"{adj} {cn}"

  def VP.toText : VP → String
    | .laughed => "laughed"
    | .cheered => "cheered"
    | .shuddered => "shuddered"
    | .vpTrans tv np => s!"{tv} {np.toText}"
    | .vpDitrans dv iobj dobj =>
      s!"{dv} {iobj.toText} {dobj.toText}"
end

instance : ToString Sent := ⟨Sent.toText⟩
instance : ToString NP := ⟨NP.toText⟩
instance : ToString RCN := ⟨RCN.toText⟩
instance : ToString VP := ⟨VP.toText⟩

-- A árvore de análise de **The dwarf that Snow White helped admired every
-- princess** é a seguinte.

-- S
-- ├── NP
-- │   ├── DET — the
-- │   └── RCN
-- │       ├── CN — dwarf
-- │       ├── That — that
-- │       ├── NP — Snow White
-- │       └── TV — helped
-- └── VP
--     ├── TV — admired
--     └── NP
--         ├── DET — every
--         └── CN — princess

-- O termo Lean correspondente é este.

def sent1 : Sent :=
  .sent (.npDetRel .the
          (.rcnObj .dwarf .that .snowWhite .helped))
        (.vpTrans .admired (.npDet .every .princess))

-- É por isso que cada tipo do fragmento deriva `Repr`: avaliar `sent1` no
-- editor exibe o termo, isto é, a árvore, construtor por construtor.
-- `ToString` faz o caminho oposto e devolve a sentença de superfície.

#eval toString sent1

-- "the dwarf that Snow White helped admired every princess"

-- Ir da sentença de superfície para a árvore é o problema inverso, chamado de
-- **análise sintática**. Não o trataremos aqui: neste capítulo as árvores são
-- construídas à mão, e o que nos interessa é o que fazer com elas depois de
-- construídas.

-- ### Estender uma gramática

-- Um tipo indutivo em Lean é fechado: os construtores listados na declaração
-- são todos os que existem, e não há como acrescentar um depois. É isso que
-- torna as funções sobre `Sent` verificáveis — o compilador sabe que uma
-- função que trata os cinco construtores de `VP` trata todos os casos. Mas é
-- também o que impede que uma gramática seja estendida do jeito mais óbvio,
-- acrescentando uma alternativa a uma regra que já existe.

-- Há duas situações, e elas se comportam de maneiras diferentes.

-- Acrescentar uma **palavra** a uma categoria — um adjetivo, um verbo
-- transitivo — exige mesmo redeclarar o tipo daquela categoria, porque a
-- palavra é um construtor novo. Por isso o léxico acima já está completo:
-- `ADJ` traz **fake**, **happy** e **evil** desde a declaração.

-- Acrescentar uma **regra**, por outro lado, pode ser feito sem tocar no que
-- já existe. Em vez de acrescentar um construtor a `Sent`, declaramos uma
-- categoria nova que contém a antiga:

inductive Coord where
  | and
deriving Repr

instance : ToString Coord := ⟨fun | .and => "and"⟩

inductive SentAnd where
  | base (s : Sent)
  | coord (left : SentAnd) (c : Coord) (right : SentAnd)
deriving Repr

def SentAnd.toText : SentAnd → String
  | .base s => toString s
  | .coord l c r => s!"{l.toText} {c} {r.toText}"

instance : ToString SentAnd := ⟨SentAnd.toText⟩

-- O construtor `base` diz que toda sentença do fragmento original é uma
-- sentença do fragmento estendido, e `coord` acrescenta a regra nova,
-- `S ::= S COORD S`. Nada de `Sent` foi redeclarado, e as funções já escritas
-- sobre `Sent` continuam valendo — `SentAnd.toText` chama `toString` sobre o
-- `Sent` de dentro.

def sent2 : SentAnd :=
  .coord (.base (.sent .alice .laughed)) .and
         (.base (.sent .dorothy .cheered))

#eval toString sent2

-- "Alice laughed and Dorothy cheered"

-- Os dois exercícios a seguir estendem o fragmento por esse caminho.

-- ### Exercise (2 stars): preposition-phrase ⭐⭐

-- Estenda o fragmento com sintagmas preposicionais, de modo que a sentença
-- **A dwarf defeated a giant with a sword** seja gerada de duas maneiras
-- estruturalmente diferentes, enquanto há apenas uma maneira de gerar **A
-- dwarf defeated Little Mook with a sword**.

-- A preposição **with** tem o nome de uma palavra reservada de Lean. Para
-- usá-la assim mesmo como nome de construtor, basta cercá-la de guilhemets:
-- `«with»`. Fora da declaração, `.with` já é lido como o construtor e
-- dispensa os guilhemets.

inductive Prep where
  | «with»
deriving Repr

instance : ToString Prep := ⟨fun | .with => "with"⟩

inductive PP where
  | pp (p : Prep) (np : NP)
deriving Repr

instance : ToString PP :=
  ⟨fun | .pp p np => s!"{p} {np}"⟩

inductive NPP where
  | withPP (det : DET) (cn : CN) (pp : PP)
deriving Repr

inductive VPP where
  | base (vp : VP)
  | objPP (tv : TV) (np : NPP)
  | vpPP (tv : TV) (np : NP) (pp : PP)
deriving Repr

inductive SentPP where
  | sent (np : NP) (vp : VPP)
deriving Repr

-- Repare que `NPP` tem um único construtor, e que tanto `objPP` quanto `vpPP`
-- exigem um sintagma preposicional. É isso que garante que a gramática
-- estendida não gere duas vezes as sentenças que a original já gerava: uma
-- sentença sem sintagma preposicional só pode passar por `base`.

-- Complete as funções que devolvem a sentença de superfície.

def NPP.toText : NPP → String :=
  sorry

instance : ToString NPP := ⟨NPP.toText⟩

def VPP.toText : VPP → String :=
  sorry

instance : ToString VPP := ⟨VPP.toText⟩

def SentPP.toText : SentPP → String :=
  sorry

instance : ToString SentPP := ⟨SentPP.toText⟩

-- Agora construa as três árvores: as duas leituras de **A dwarf defeated a
-- giant with a sword** e a única de **A dwarf defeated Little Mook with a
-- sword**.

def withSword : PP := .pp .with (.npDet .a .sword)

-- O sintagma preposicional modifica o objeto.
def giantSword1 : SentPP :=
  sorry

-- O sintagma preposicional modifica o sintagma verbal.
def giantSword2 : SentPP :=
  sorry

-- Única leitura possível.
def mookSword : SentPP :=
  sorry

theorem giantSword_ambiguous :
    toString giantSword1 = toString giantSword2 :=
  sorry

theorem giantSword_surface :
    toString giantSword1 =
      "a dwarf defeated a giant with a sword" :=
  sorry

theorem mookSword_surface :
    toString mookSword =
      "a dwarf defeated Little Mook with a sword" :=
  sorry

-- As duas primeiras árvores são diferentes e imprimem a mesma sentença: é a
-- ambiguidade pedida.

-- ### Exercise (2 stars): complex-relative-clauses ⭐⭐

-- Estenda o fragmento com orações relativas complexas, em que a oração
-- relativa coordena dois sintagmas verbais ou dois pares sintagma
-- nominal–verbo transitivo. O fragmento deve gerar, entre outras, a sentença
-- **The dwarf that Snow White helped and Goldilocks admired cheered**. Que
-- problemas você encontra?

inductive RCNC where
  | vpAnd (cn : CN) (compl : That)
      (left : VP) (c : Coord) (right : VP)
  | objAnd (cn : CN) (compl : That)
      (np1 : NP) (tv1 : TV) (c : Coord)
      (np2 : NP) (tv2 : TV)
deriving Repr

inductive NPC where
  | base (np : NP)
  | npDetRel (det : DET) (rcn : RCNC)
deriving Repr

inductive SentC where
  | sent (np : NPC) (vp : VP)
deriving Repr

-- Complete as funções de superfície e construa a sentença do enunciado.

def RCNC.toText : RCNC → String :=
  sorry

instance : ToString RCNC := ⟨RCNC.toText⟩

def NPC.toText : NPC → String :=
  sorry

instance : ToString NPC := ⟨NPC.toText⟩

def SentC.toText : SentC → String :=
  sorry

instance : ToString SentC := ⟨SentC.toText⟩

def dwarfHelpedAdmired : SentC :=
  sorry

theorem dwarfHelpedAdmired_surface :
    toString dwarfHelpedAdmired =
      "the dwarf that Snow White helped and " ++
        "Goldilocks admired cheered" :=
  sorry

-- ## FOL como Linguagem de representação

-- A lógica de predicados nos dá representações para dois tipos: o tipo das
-- entidades é representado pelos termos, e o tipo dos valores de verdade
-- pelas fórmulas. Chamaremos de `LF` — **forma lógica** — o tipo das fórmulas
-- de primeira ordem cujos termos são termos estruturados, o `FOL.Formula` de
-- FOL com `FOL.Term` no lugar do parâmetro.

open FOL

abbrev LF := Formula Term

-- Supondo que estejamos tratando de um fragmento que gera sentenças
-- declarativas cujos significados podem ser representados na lógica de
-- predicados, é razoável dar o tipo `LF` às representações das sentenças.

-- Para traduzir o fragmento de Um fragmento do inglês para a lógica de
-- predicados, tudo o que temos a fazer é achar traduções apropriadas para
-- todas as categorias da gramática. Mas a primeira regra, `S ::= NP VP`, já
-- nos apresenta uma dificuldade. Ao procurar traduções de `NP` e traduções de
-- `VP`, devemos representar o `NP` como uma função que toma a representação
-- do `VP` como argumento, ou o contrário?

-- De todo modo, as representações de `VP` terão um tipo funcional, pois
-- sintagmas verbais denotam propriedades. Um tipo razoável para a função que
-- representa um `VP` é `Term → LF`: alimentada com um termo, ela devolve uma
-- forma lógica. Os nomes próprios podem então receber o tipo dos termos. Tome
-- o exemplo **Goldilocks laughed**. O verbo **laughed** é representado pela
-- função que leva o termo `x` à fórmula `laugh[x]`. Obtemos assim uma forma
-- lógica apropriada para a sentença, se `x` for um termo para **Goldilocks**.

-- A dificuldade apontada em Formas linguísticas e traduções para lógica é que
-- sintagmas como **no boy** e **every girl** não se encaixam nesse padrão. Lá
-- também dissemos que isso se resolve supondo que tais sintagmas se traduzem
-- como funções que tomam representações de `VP` como argumento. Uma tradução
-- apropriada para **everyone** seria uma função de tipo `(Term → LF) → LF`:
-- alimentada com a representação de um `VP`, ela devolve uma forma lógica. O
-- resultado da discussão é que, na representação de uma estrutura
-- `S ::= NP VP`, a representação do `NP` deve ser a função e a do `VP` o
-- argumento. Os tipos das quatro funções de tradução são, portanto, estes:

-- lfSent : Sent → LF
-- lfNP   : NP   → (Term → LF) → LF
-- lfVP   : VP   → Term → LF
-- lfRCN  : RCN  → Term → LF

-- Como `NP`, `VP` e `RCN` se referem uns aos outros, as quatro funções se
-- chamam umas às outras, e vão para um bloco `mutual`. Antes dele, porém, vêm
-- as funções de tradução que não dependem de nenhuma outra.

-- As categorias lexicais são as mais simples. Um substantivo comum tem o
-- mesmo tipo que um sintagma verbal, e um adjetivo também.

def lfCN : CN → Term → LF
  | .girl, t => .atom "girl" [t]
  | .boy, t => .atom "boy" [t]
  | .princess, t => .atom "princess" [t]
  | .dwarf, t => .atom "dwarf" [t]
  | .giant, t => .atom "giant" [t]
  | .wizard, t => .atom "wizard" [t]
  | .sword, t => .atom "sword" [t]
  | .dagger, t => .atom "dagger" [t]

def lfADJ : ADJ → Term → LF
  | .fake, t => .atom "fake" [t]
  | .happy, t => .atom "happy" [t]
  | .evil, t => .atom "evil" [t]

-- Um verbo transitivo relaciona duas entidades, e um verbo bitransitivo,
-- três. O primeiro argumento é sempre o do sujeito; no verbo bitransitivo, o
-- segundo é o do objeto indireto e o terceiro o do objeto direto.

def lfTV : TV → Term → Term → LF
  | .loved, t1, t2 => .atom "love" [t1, t2]
  | .admired, t1, t2 => .atom "admire" [t1, t2]
  | .helped, t1, t2 => .atom "help" [t1, t2]
  | .defeated, t1, t2 => .atom "defeat" [t1, t2]
  | .caught, t1, t2 => .atom "catch" [t1, t2]

def lfDV : DV → Term → Term → Term → LF
  | .gave, t1, t2, t3 => .atom "give" [t1, t2, t3]

-- ### Variáveis novas

-- A tradução de um determinante toma dois argumentos de tipo `Term → LF` —
-- formas lógicas com um buraco de termo dentro — e produz uma forma lógica.
-- No caso dos quantificadores, o primeiro argumento é a **restrição** e o
-- segundo o **escopo**.

-- lfDET : DET → (Term → LF) → (Term → LF) → LF

-- A tradução dos determinantes precisa ser feita com algum cuidado, porque
-- envolve construir uma forma lógica em que uma variável fica ligada. Para
-- garantir a ligação correta, temos de nos assegurar de que a variável
-- recém-introduzida não seja capturada por um quantificador já presente na
-- forma lógica. Mas, se refletirmos sobre como as variáveis são introduzidas,
-- veremos que elas sempre aparecem junto de quem as liga, e que nenhuma
-- ligação é vazia. Basta então colher os índices das ocorrências ligadas.

def boundIndices : LF → List Nat
  | .atom _ _ => []
  | .eq _ _ => []
  | .top => []
  | .bot => []
  | .neg f => boundIndices f
  | .impl f1 f2 => boundIndices f1 ++ boundIndices f2
  | .equi f1 f2 => boundIndices f1 ++ boundIndices f2
  | .conj f1 f2 => boundIndices f1 ++ boundIndices f2
  | .disj f1 f2 => boundIndices f1 ++ boundIndices f2
  | .forall_ v f => v.index ++ boundIndices f
  | .exists_ v f => v.index ++ boundIndices f

-- Para calcular um índice novo, basta escolher um índice fora dessa lista.
-- Todas as variáveis são introduzidas pelo mesmo mecanismo: se começarmos com
-- variáveis da forma `⟨"x", [0]⟩` e só introduzirmos variáveis novas da mesma
-- forma, podemos supor que toda variável que ocorre na forma lógica tem esse
-- feitio. O `0` inicial em `foldr max 0` garante que a lista sobre a qual
-- tomamos o máximo não seja vazia.

-- Os argumentos de `lfDET` não são formas lógicas, e sim funções à espera de
-- um termo. Para ver que variáveis elas carregam, aplicamos cada uma a um
-- termo qualquer que não contenha variável alguma.

def dummy : Term := .struct "" []

def freshIndex (ps : List (Term → LF)) : Nat :=
  let used :=
    (ps.map (fun p => boundIndices (p dummy))).flatten
  used.foldr max 0 + 1

def freshVar (ps : List (Term → LF)) : Variable :=
  ⟨"x", [freshIndex ps]⟩

-- Podemos agora dar a tradução dos determinantes. Os indefinidos **a** e
-- **some** recebem a mesma tradução.

def lfDET : DET → (Term → LF) → (Term → LF) → LF
  | .a, p, q =>
    let v := freshVar [p, q]
    .exists_ v (.conj (p (.var v)) (q (.var v)))
  | .some, p, q =>
    let v := freshVar [p, q]
    .exists_ v (.conj (p (.var v)) (q (.var v)))
  | .every, p, q =>
    let v := freshVar [p, q]
    .forall_ v (.impl (p (.var v)) (q (.var v)))
  | .no, p, q =>
    let v := freshVar [p, q]
    .neg (.exists_ v (.conj (p (.var v)) (q (.var v))))
  | .the, p, q =>
    let i := freshIndex [p, q]
    let v1 : Variable := ⟨"x", [i]⟩
    let v2 : Variable := ⟨"x", [i + 1]⟩
    .exists_ v1
      (.conj
        (.forall_ v2
          (.equi (p (.var v2)) (.eq (.var v1) (.var v2))))
        (q (.var v1)))

-- Para o determinante definido usamos a teoria das descrições definidas
-- proposta por Bertrand Russell (Russell, 1905). Russell propôs traduzir
-- **The king of France is bald** como a conjunção de **existe exatamente uma
-- pessoa que é rei da França** e **essa pessoa é careca**, o que se exprime
-- assim na lógica de predicados:

-- ∃x (∀y (King[y] <=> x = y) & Bald[x])

-- Nem todo determinante do inglês admite uma tradução para a lógica de
-- predicados. **Most** é o exemplo clássico: não há como dizer, com os
-- quantificadores `∀` e `∃`, que a maioria dos anões riu. Determinantes como
-- **at least n** e **at most n** têm tradução, mas as formas lógicas ficam
-- muito pesadas. É por isso que `DET` traz apenas os cinco determinantes
-- acima.

-- ### O bloco mutuamente recursivo

-- Falta traduzir as quatro categorias que se referem umas às outras. Os nomes
-- próprios são traduzidos como símbolos funcionais de aridade zero, isto é,
-- como constantes: **Snow White** é o termo `SnowWhite`.

-- Os sintagmas **everyone** e **someone** não têm um termo que lhes
-- corresponda. Eles são traduzidos como quantificadores restritos à
-- propriedade de ser uma pessoa, e é justamente essa a forma de que falamos
-- na primeira seção: uma função que toma a representação do sintagma verbal
-- como argumento.

-- Usamos a conjunção para juntar a forma lógica de um substantivo comum e a
-- de uma oração relativa numa forma lógica para o substantivo comum complexo.

mutual
  def lfSent : Sent → LF
    | .sent np vp => lfNP np (lfVP vp)

  def lfNP : NP → (Term → LF) → LF
    | .snowWhite, p => p (.struct "SnowWhite" [])
    | .alice, p => p (.struct "Alice" [])
    | .dorothy, p => p (.struct "Dorothy" [])
    | .goldilocks, p => p (.struct "Goldilocks" [])
    | .littleMook, p => p (.struct "LittleMook" [])
    | .atreyu, p => p (.struct "Atreyu" [])
    | .everyone, p =>
      let v := freshVar [p]
      .forall_ v
        (.impl (.atom "person" [.var v]) (p (.var v)))
    | .someone, p =>
      let v := freshVar [p]
      .exists_ v
        (.conj (.atom "person" [.var v]) (p (.var v)))
    | .npDet det cn, p => lfDET det (lfCN cn) p
    | .npDetRel det rcn, p => lfDET det (lfRCN rcn) p

  def lfVP : VP → Term → LF
    | .laughed, t => .atom "laugh" [t]
    | .cheered, t => .atom "cheer" [t]
    | .shuddered, t => .atom "shudder" [t]
    | .vpTrans tv np, subj =>
      lfNP np (fun obj => lfTV tv subj obj)
    | .vpDitrans dv np1 np2, subj =>
      lfNP np1 (fun iobj =>
        lfNP np2 (fun dobj => lfDV dv subj iobj dobj))

  def lfRCN : RCN → Term → LF
    | .rcnSubj cn _ vp, t => .conj (lfCN cn t) (lfVP vp t)
    | .rcnObj cn _ np tv, t =>
      .conj (lfCN cn t)
        (lfNP np (fun subj => lfTV tv subj t))
    | .rcnAdj adj cn, t => .conj (lfADJ adj t) (lfCN cn t)
end

-- A tradução do adjetivo em `rcnAdj` é a conjunção: um **happy wizard** é
-- alguém que é feliz e é mago. Isso está certo para **happy** e para
-- **evil**, e está errado para **fake**: um **fake wizard** justamente não é
-- um mago. Adjetivos desse tipo pedem uma semântica que a lógica de
-- predicados não alcança, e o fragmento os traduz assim porque em Lean uma
-- função tem de estar definida em todos os casos — a tradução existe, mas não
-- é uma boa tradução.

-- Vejamos três exemplos.

def lf1 : LF :=
  lfSent (.sent (.npDet .some .dwarf)
                (.vpTrans .defeated (.npDet .some .giant)))

def lf2 : LF :=
  lfSent (.sent (.npDetRel .the
                  (.rcnObj .wizard .that .dorothy .admired))
                .laughed)

def lf3 : LF :=
  lfSent (.sent (.npDetRel .the
                  (.rcnSubj .princess .that
                    (.vpTrans .helped .alice)))
                .shuddered)

#eval lf1

-- ∃x2 (dwarf[x2] & ∃x1 (giant[x1] & defeat[x2, x1]))

#eval lf2

-- ∃x1 (∀x2 ((wizard[x2] & admire[Dorothy, x2]) <=> x1 = x2) & laugh[x1])

#eval lf3

-- ∃x1 (∀x2 ((princess[x2] & help[x2, Alice]) <=> x1 = x2) & shudder[x1])

-- ### Exercise (2 stars): fragment-translations ⭐⭐

-- Construa as árvores de análise das quatro sentenças a seguir, todas geradas
-- pelo fragmento.

-- 1. Every girl that laughed helped a boy.
-- 2. No giant that shuddered defeated every dwarf.
-- 3. Every princess loved every dwarf that defeated a giant.
-- 4. Every boy admired a girl that no wizard helped.

-- Os teoremas conferem que cada árvore devolve a sentença certa. Depois
-- disso, `#eval lfSent tr1` exibe a forma lógica da primeira.

def tr1 : Sent :=
  sorry

def tr2 : Sent :=
  sorry

def tr3 : Sent :=
  sorry

def tr4 : Sent :=
  sorry

theorem tr1_surface :
    toString tr1 =
      "every girl that laughed helped a boy" :=
  sorry

theorem tr2_surface :
    toString tr2 =
      "no giant that shuddered defeated every dwarf" :=
  sorry

theorem tr3_surface :
    toString tr3 =
      "every princess loved every dwarf " ++
        "that defeated a giant" :=
  sorry

theorem tr4_surface :
    toString tr4 =
      "every boy admired a girl that no wizard helped" :=
  sorry

-- Temos agora representações de sentenças declarativas da língua natural como
-- fórmulas da lógica de predicados. Falta dizer quando essas fórmulas são
-- verdadeiras.

-- ## Uma Estrutura de Primeira Ordem

-- Tudo o que precisamos para especificar uma estrutura de primeira ordem é um
-- domínio de entidades e interpretações apropriadas para os nomes próprios e
-- para os predicados. Começamos construindo um pequeno domínio de exemplo,
-- formado pelos indivíduos `A`, …, `Z`, mais uma entidade especial.

inductive Entity where
  | A | B | C | D | E | F | G | H | I
  | J | K | L | M | N | O | P | Q | R
  | S | T | U | V | W | X | Y | Z
  | Unspec
deriving Repr, DecidableEq

-- A entidade especial `Unspec` terá um papel importante no tratamento das
-- relações subespecificadas: ela nos permitirá definir relações com algumas
-- posições de argumento deixadas em aberto.

-- Para avaliar uma fórmula quantificada é preciso percorrer o domínio, e
-- percorrer exige uma coleção. Como em FOL, o tipo indutivo declara quais são
-- os objetos e a lista os exibe na ordem em que serão percorridos.

def entities : List Entity :=
  [.A, .B, .C, .D, .E, .F, .G, .H, .I,
   .J, .K, .L, .M, .N, .O, .P, .Q, .R,
   .S, .T, .U, .V, .W, .X, .Y, .Z,
   .Unspec]

theorem mem_entities (e : Entity) : e ∈ entities := by
  cases e <;> decide

-- O teorema `mem_entities` diz que na lista estão todos os elementos do tipo,
-- e voltaremos a ele no fim da seção.

-- Os nomes próprios são interpretados simplesmente como entidades.

def snowWhite : Entity := .S
def alice : Entity := .A
def dorothy : Entity := .D
def goldilocks : Entity := .G
def littleMook : Entity := .M
def atreyu : Entity := .Y

-- Substantivos comuns como **girl** e **dwarf**, e verbos intransitivos como
-- **laugh** e **shudder**, são interpretados como propriedades de entidades.
-- Verbos transitivos como **love** são interpretados como relações entre
-- entidades.

-- Para propriedades e relações sobre `Entity`, poderíamos usar um tipo geral
-- `List Entity → Bool`. Isso nos permitiria falar de relações de qualquer
-- aridade de maneira uniforme, mas não seria conveniente para a composição do
-- significado: na sintaxe, um verbo transitivo combina primeiro com o objeto
-- direto e depois com o sujeito, e um verbo bitransitivo combina com um
-- objeto indireto e um objeto direto, e então com o sujeito. Queremos,
-- portanto, que os verbos denotem funções que tomam seus argumentos um a um.
-- Definimos assim os tipos dos predicados de um, dois e três lugares.

abbrev OnePlacePred := Entity → Bool
abbrev TwoPlacePred := Entity → Entity → Bool
abbrev ThreePlacePred := Entity → Entity → Entity → Bool

-- Como Conjuntos e Relações mostrou, um predicado de um lugar é a função
-- característica de um conjunto, e é natural pensá-lo como a lista das
-- entidades para as quais ele vale. Definimos então funções de conversão que
-- transformam listas em predicados.

def list1 (xs : List Entity) : OnePlacePred :=
  fun x => xs.contains x

def list2 (ps : List (Entity × Entity)) : TwoPlacePred :=
  fun x y => ps.contains (x, y)

def list3 (ts : List (Entity × Entity × Entity)) :
    ThreePlacePred :=
  fun x y z => ts.contains (x, y, z)

-- Com elas, o léxico se escreve como listas.

def girl : OnePlacePred := list1 [.S, .A, .D, .G]
def boy : OnePlacePred := list1 [.M, .Y]
def princess : OnePlacePred := list1 [.E]
def dwarf : OnePlacePred := list1 [.B, .R]
def giant : OnePlacePred := list1 [.T]
def wizard : OnePlacePred := list1 [.W, .V]
def sword : OnePlacePred := list1 [.F]
def dagger : OnePlacePred := list1 [.X]

-- Com esses predicados podemos definir outros, como o de ser uma pessoa ou
-- uma coisa: uma pessoa é um menino, uma menina, uma princesa, um anão, um
-- gigante ou um mago, e uma coisa é tudo o que não é pessoa nem o objeto
-- especial `Unspec`. É conveniente ter também homens e mulheres: supomos que
-- as mulheres são as princesas e que os homens são os anões, os gigantes e os
-- magos.

def child : OnePlacePred := fun x => girl x || boy x
def person : OnePlacePred := fun x =>
  child x || princess x || dwarf x || giant x || wizard x
def man : OnePlacePred := fun x =>
  dwarf x || giant x || wizard x
def woman : OnePlacePred := princess
def male : OnePlacePred := fun x => man x || boy x
def female : OnePlacePred := fun x => woman x || girl x
def thing : OnePlacePred := fun x =>
  !(person x || x == .Unspec)

-- Como os verbos intransitivos também denotam propriedades, seus significados
-- são representados igualmente por predicados de um lugar.

def laugh : OnePlacePred := list1 [.A, .G, .E]
def cheer : OnePlacePred := list1 [.M, .D]
def shudder : OnePlacePred := list1 [.S]

-- Os verbos transitivos denotam relações entre entidades, e é conveniente
-- pensar um predicado de dois lugares como a lista dos pares para os quais
-- ele vale. Dois deles não são dados por uma lista fixa: **admire** vale de
-- toda pessoa para Goldilocks, e **defeat** vale de todo anão para todo
-- gigante, além dos dois pares em que Alice derrota um mago.

def love : TwoPlacePred :=
  list2 [(.Y, .E), (.B, .S), (.R, .S)]

def help : TwoPlacePred :=
  list2 [(.W, .W), (.V, .V), (.S, .B), (.D, .M)]

def admire : TwoPlacePred := fun x y =>
  person x && y == .G

def defeat : TwoPlacePred := fun x y =>
  (dwarf x && giant y) || list2 [(.A, .W), (.A, .V)] x y

-- Os significados dos verbos bitransitivos são representados por predicados
-- de três lugares, da mesma maneira.

def give : ThreePlacePred :=
  list3 [(.T, .S, .X), (.A, .E, .S)]

-- THE FOLLOWING DETAILS CAN BE SKIPPED (Argumentos deixados em aberto)
-- A entidade `Unspec` serve para definir relações subespecificadas. Podemos,
-- por exemplo, acrescentar um verbo **kill** e interpretá-lo como uma relação
-- de três lugares em que o primeiro argumento dá o agente, o segundo a vítima
-- e o terceiro o instrumento. Nos casos em que não há instrumento ou agente,
-- deixamos o argumento em aberto.

def kill : ThreePlacePred :=
  list3 [(.Y, .T, .F), (.Unspec, .D, .X),
         (.Unspec, .M, .Unspec)]

-- O que essa entrada diz é que Atreyu matou o gigante com a espada, que
-- Dorothy foi esfaqueada — deixando em aberto quem a esfaqueou — e que Little
-- Mook simplesmente morreu.

-- Usar `Unspec` para deixar argumentos implícitos pode ser explorado de
-- maneira mais geral. Um exemplo são as passivas. A passivização é um
-- processo de redução de argumentos: o agente da ação é suprimido. Sem entrar
-- nas propriedades sutis das construções passivas, podemos especificar uma
-- função de passivização semântica assim:

def passivize (r : TwoPlacePred) : OnePlacePred :=
  fun x => r .Unspec x

-- A redução de argumentos não aparece só nas passivas. Outro caso é uma
-- análise dos pronomes reflexivos segundo a qual **himself** e **herself**
-- diferem semanticamente de **him** e **her** por não serem interpretados
-- como variáveis individuais: eles denotam funções que reduzem argumentos.
-- Considere a sentença **Snow White admired herself**. O reflexivo
-- **herself** é interpretado como uma função que toma o predicado de dois
-- lugares **admired** e o transforma num predicado de um lugar, que toma o
-- sujeito como argumento e exprime que essa entidade admira a si mesma.

def self {α β : Type} (p : α → α → β) : α → β :=
  fun x => p x x

-- Essa análise tem duas consequências desejáveis. A primeira é que a
-- localidade dos reflexivos cai por terra sozinha: como `self` se aplica a um
-- predicado e unifica argumentos desse predicado, não há como um argumento
-- ser unificado com outro de fora da mesma oração. Em **Snow White thinks
-- that Alice admired herself**, portanto, **herself** só pode se referir a
-- Alice, e não a Snow White. A segunda é que reflexivos em posição de sujeito
-- ficam excluídos: em **Herself admired Snow White**, a interpretação
-- composicional aplica primeiro **admired** a Snow White, o que dá um
-- predicado de um lugar, e aplicar `self` a ele falha, porque `self` espera
-- um predicado de dois lugares. Não sobram duas posições de argumento a
-- unificar.
-- END DETAILS

-- ### Exercise (2 stars): reflexive-ditransitive ⭐⭐

-- Nos verbos bitransitivos, um reflexivo pode ser tanto o objeto direto
-- quanto o objeto indireto:

-- 1. Alice introduced herself to the rabbit.
-- 2. Little Mook gave the figs to himself.

-- Defina as funções `self3DO` e `self3IO`, de tipo
-- `ThreePlacePred → TwoPlacePred`, que unificam o sujeito com o objeto direto
-- e com o objeto indireto, respectivamente. Lembre que, num predicado de três
-- lugares, o primeiro argumento é o do sujeito, o segundo o do objeto
-- indireto e o terceiro o do objeto direto.

-- Para testar as duas funções, `introduced x y z` diz que `x` apresentou `z`
-- a `y`: Alice apresentou a si mesma ao anão `B`, e Snow White apresentou a
-- princesa ao mesmo anão.

def introduced : ThreePlacePred :=
  list3 [(.A, .B, .A), (.S, .B, .E)]

def self3DO (p : ThreePlacePred) : TwoPlacePred :=
  sorry

def self3IO (p : ThreePlacePred) : TwoPlacePred :=
  sorry

theorem self3DO_introduced :
    self3DO introduced .A .B = true :=
  sorry

theorem self3IO_introduced :
    self3IO introduced .A .B = false :=
  sorry

-- ### Interpretando os símbolos

-- Já temos em a semântica de FOL tudo o que é preciso para avaliar fórmulas:
-- `FOL.Interp` interpreta os símbolos de predicado, `FOL.FInterp` os símbolos
-- funcionais, `FOL.Assign` as variáveis, e `FOL.Formula.eval` percorre a
-- fórmula. Falta apenas ligar os nomes que a tradução produz às relações que
-- acabamos de definir.

def intFairy : Interp Entity
  | "girl", [x] => girl x
  | "boy", [x] => boy x
  | "princess", [x] => princess x
  | "dwarf", [x] => dwarf x
  | "giant", [x] => giant x
  | "wizard", [x] => wizard x
  | "sword", [x] => sword x
  | "dagger", [x] => dagger x
  | "person", [x] => person x
  | "laugh", [x] => laugh x
  | "cheer", [x] => cheer x
  | "shudder", [x] => shudder x
  | "love", [x, y] => love x y
  | "admire", [x, y] => admire x y
  | "help", [x, y] => help x y
  | "defeat", [x, y] => defeat x y
  | "give", [x, y, z] => give x y z
  | _, _ => false

-- Os nomes próprios foram traduzidos como constantes, isto é, como símbolos
-- funcionais de aridade zero. É `FOL.FInterp` que diz qual entidade cada um
-- nomeia, e `Unspec` é o valor natural para os símbolos que a estrutura não
-- nomeia.

def fintFairy : FInterp Entity
  | "SnowWhite", [] => snowWhite
  | "Alice", [] => alice
  | "Dorothy", [] => dorothy
  | "Goldilocks", [] => goldilocks
  | "LittleMook", [] => littleMook
  | "Atreyu", [] => atreyu
  | _, _ => .Unspec

-- Como vimos em FOL, um símbolo que a interpretação não menciona é avaliado
-- como `false`. No fragmento isso acontece com **catch** e com os adjetivos:
-- a estrutura simplesmente não diz nada sobre eles, e toda sentença que os
-- use será falsa.

-- Falta a atribuição de valores às variáveis. As fórmulas que a tradução
-- produz são sentenças, sem variáveis livres, e para elas a atribuição é
-- irrelevante — mas `FOL.Formula.eval` ainda exige alguma.

def ass0 : Assign Entity := fun _ => .A

-- Agora podemos avaliar. A fórmula que diz que a relação de amor é reflexiva
-- é falsa nesta estrutura, como seria de esperar.

def loveReflexive : LF :=
  .forall_ x (.atom "love" [tx, tx])

#eval loveReflexive.eval entities intFairy ass0
        (liftAssign fintFairy)

-- false

-- ### Exercise (2 stars): check-sentence ⭐⭐

-- Junte as duas metades. Defina a função que decide se uma sentença do
-- fragmento é verdadeira nesta estrutura: ela deve traduzir a sentença para
-- uma forma lógica e avaliar essa forma lógica no domínio `entities`, com as
-- interpretações `intFairy` e `fintFairy` e com a atribuição `ass0`.

def checkSentence (s : Sent) : Bool :=
  sorry

theorem goldilocksLaughed :
    checkSentence (.sent .goldilocks .laughed) = true :=
  sorry

theorem dorothyLaughed :
    checkSentence (.sent .dorothy .laughed) = false :=
  sorry

theorem someDwarfDefeatedSomeGiant :
    checkSentence
      (.sent (.npDet .some .dwarf)
             (.vpTrans .defeated (.npDet .some .giant)))
      = true :=
  sorry

theorem everyoneCheered :
    checkSentence (.sent .everyone .cheered) = false :=
  sorry

-- Temos assim um procedimento de interpretação indireta para o fragmento, em
-- dois passos: primeiro construímos uma forma lógica a partir da expressão da
-- língua natural, depois avaliamos essa forma lógica em relação a uma
-- estrutura.

-- Falta cobrar a promessa feita a `mem_entities`. `FOL.Formula.eval` decide
-- um quantificador percorrendo uma lista, e só concorda com o `∀` de Lean se
-- essa lista contiver todos os elementos do domínio — é o que a hipótese
-- `hdom` de `FOL.Formula.eval_iff_denote` exige, e é exatamente o que
-- `mem_entities` fornece.

theorem eval_iff_denote_fairy (I : Interp Entity)
    (g : Assign Entity) (f : Formula Term) :
    f.eval entities I g (liftAssign fintFairy) = true ↔
      f.denote (fun n as => I n as = true) g
        (liftAssign fintFairy) :=
  Formula.eval_iff_denote entities mem_entities I
    (liftAssign fintFairy) g f

-- Nesta estrutura, portanto, as duas leituras de qualquer fórmula concordam:
-- o `Bool` que `checkSentence` calcula e a proposição que a sentença afirma
-- são a mesma coisa. Isso vale porque o domínio é finito e está listado — em
-- FOL vimos que nenhuma lista consegue fazer o mesmo pelos naturais.

-- ### Exercise (2 stars): help-defeat ⭐⭐

-- Considere os verbos **help** e **defeat** e os sintagmas nominais
-- **Alice**, **Snow White**, **every wizard** e **a dwarf**. Determine, para
-- cada sentença da forma `S ::= NP TV NP` construída com esses verbos e
-- sintagmas, se ela é verdadeira ou falsa nesta estrutura.

-- A lista `sentences` abaixo tem as trinta e duas sentenças, na ordem em que
-- os laços as geram. Complete `values` com os trinta e dois valores de
-- verdade.

def someNPs : List NP :=
  [.alice, .snowWhite,
   .npDet .every .wizard, .npDet .a .dwarf]

def sentences : List Sent :=
  someNPs.flatMap fun subj =>
    [TV.helped, TV.defeated].flatMap fun v =>
      someNPs.map fun obj =>
        Sent.sent subj (.vpTrans v obj)

def values : List Bool :=
  sorry

theorem values_correct :
    sentences.map checkSentence = values :=
  sorry

end English

