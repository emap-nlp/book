-- # Um fragmento de inglês

namespace English

-- ## Um fragmento linguístico

-- Vamos construir uma sentença a partir de um sujeito e um predicado. Não se
-- trata da concatenação de strings, é um construtor de sentenças que
-- respeitam uma estrutura esperada. O verificador de tipos passa a recusar as
-- combinações que não são sentenças. Um embrião do que vamos ver pela frente.

-- A keyword `deriving` pede que uma instância para a classe `Repr` seja
-- automaticamente gerada para cada tipo.

inductive Subject where
  | Chomsky
  | Montague
deriving Repr

inductive Predicate where
  | Wrote (title : String)
deriving Repr

inductive Sentence where
  | S (subj : Subject) (pred : Predicate)
deriving Repr

-- A abreviações são como `def` mas são `unfold` automaticamente.

abbrev Sentences := List Sentence

#eval Subject.Chomsky

-- English.Subject.Chomsky

#eval Sentence.S Subject.Chomsky
  (Predicate.Wrote "Syntactic Structures")

-- English.Sentence.S (English.Subject.Chomsky) (English.Predicate.Wrote "Syntactic Structures")

-- A última saida acima lembra uma árvore, o que iremos chamar de *árvore
-- sintática*.

-- Sentence
--           /    \
--     Subject   Predicate

-- O passo inverso é a *geração*, serializar uma estrutura que representa uma
-- sentença. Para isso temos que transformar a representação interna em uma
-- String. Já existe a classe `ToString` e `IO.println` pede como entrada um
-- tipo que seja instância desta classe. Então só precisamos definir as
-- instâncias para `ToString` de nossos tipos. Criar uma instância de uma
-- classe é implementar os campos que a classe demanda e classes são
-- `structure`. Algumas variações de sintaxe na declaração das instâncias.

#print ToString

-- class ToString.{u} (α : Type u) : Type u
-- number of parameters: 1
-- fields:
--   ToString.toString : α → String
-- constructor:
--   ToString.mk.{u} {α : Type u} (toString : α → String) : ToString α

instance : ToString Subject where
  toString
  | .Chomsky  => "Chomsky"
  | .Montague => "Montague"

instance : ToString Predicate :=
  ⟨ fun p => match p with
    | .Wrote t => s!"wrote \"{t}\"" ⟩

instance : ToString Sentence :=
  ⟨ fun | .S s p => s!"{s} {p}" ⟩

-- Algumas funções auxiliares para conveniência.

def makeP (title : String) : Predicate := .Wrote title
def makeS (s : Subject) (p : Predicate) : Sentence := .S s p

#eval IO.println $
  makeS .Chomsky (makeP "Syntactic Structures")

-- Chomsky wrote "Syntactic Structures"

-- ## Um fragmento do inglês

-- Em seguida, vamos implementar um fragmento um pouco mais realistico do
-- inglês. Ela é deliberadamente básica e grosseira, queremos capturar a
-- sintaxe de sentenças como:

-- 1. The girl laughed.
-- 2. No dwarf admired some princess that shuddered.
-- 3. Every girl that some boy loved cheered.
-- 4. The wizard that helped Snow White defeated the giant.

-- Então o que precisamos é uma regra para uma sentença sujeito-predicado. Uma
-- regra para a estrutura interna de um sintagma nominal. Uma regra para
-- substantivos com ou sem clausulas relativas. Nossa gramática poderia ser:

-- S    ::= NP VP ;
-- NP   ::= "Snow White" | "Alice" | "Dorothy" | "Goldilocks" | "Little Mook" | "Atreyu"
--       | DET CN | DET RCN ;
-- DET  ::= "the" | "a" | "every" | "some" | "no" | "most" ;
-- CN   ::= "girl" | "boy" | "princess" | "dwarf" | "giant" | "wizard" | "sword" | "dagger" ;
-- RCN  ::= CN "that" VP | CN "that" NP TV ;
-- VP   ::= "laughed" | "cheered" | "shuddered" | TV NP | DV NP NP ;
-- TV   ::= "loved" | "admired" | "helped" | "defeated" | "caught" ;
-- DV   ::= "gave" ;

-- A implementação abaixo acrescenta tipos auxiliares aos oito não-terminais
-- da BNF, introduzidos para ilustrar intensionalidade mais adiante.

-- A tradução para Lean é direta: cada categoria sintática é um construtor de
-- um `inductive` mutuamente recursivo — a árvore de análise de uma sentença é
-- um termo desse tipo, sem passo de tradução string→árvore a definir.

inductive DET where
  | a | the | every | some | no | most
  deriving Repr

instance : ToString DET :=
  ⟨fun | .a => "a" | .the => "the"
       | .every => "every" | .some => "some"
       | .no => "no" | .most => "most"⟩

inductive CN where
  | girl | boy | princess | dwarf | giant | wizard | sword
  | dagger
  deriving Repr

instance : ToString CN :=
  ⟨fun | .girl => "girl" | .boy => "boy"
       | .princess => "princess" | .dwarf => "dwarf"
       | .giant => "giant" | .wizard => "wizard"
       | .sword => "sword" | .dagger => "dagger"⟩

inductive ADJ where
  | fake
  deriving Repr

instance : ToString ADJ := ⟨fun | .fake => "fake"⟩

inductive That where
  | that
  deriving Repr

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

inductive AV where
  | hoped | wanted
  deriving Repr

instance : ToString AV :=
  ⟨fun | .hoped => "hoped" | .wanted => "wanted"⟩

inductive TINF where
  | love | admire | help | defeat | catch
  deriving Repr

instance : ToString TINF :=
  ⟨fun | .love => "love" | .admire => "admire"
       | .help => "help" | .defeat => "defeat"
       | .catch => "catch"⟩

inductive To where
  | to
  deriving Repr

-- Estes nove tipos não se referem uns aos outros nem a
-- `NP`/`VP`/`RCN`/`INF`/`Sent` — cada um é um enum simples ou tem campos só
-- desses enums, então não precisam entrar no bloco `mutual` abaixo. Isolá-los
-- deixa visível qual é a recursão real do fragmento: só `NP`, `RCN`, `VP` e
-- `INF` se referenciam (e a `Sent` que os fecha).

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook
    | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)
  deriving Repr

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)
  deriving Repr

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
  deriving Repr
end
mutual

def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White" | .alice => "Alice"
  | .dorothy => "Dorothy" | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook" | .atreyu => "Atreyu"
  | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 =>
    s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer"
  | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"
end

instance : ToString Sent := ⟨Sent.toStringImpl⟩

-- `That` e `To` são tipos com um único construtor. `catch` colide com a
-- palavra reservada do Lean para captura de exceções; o construtor de `TINF`
-- fica `catch` mesmo assim, dentro do namespace `TINF`, sem conflito (o Lean
-- resolve pelo namespace, `TINF.catch` não é `catch` do núcleo).

-- A árvore de análise de "The dwarf that Snow White helped admired every
-- princess" é como segue, construir esta árvore a partir da string é o que
-- chamamos de *parsing*.

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

-- O termo Lean correspondente segue. Note que a sentença em inglês é uma
-- sequencia de caracteres em um alfabeto, uma string no computador. A árvore
-- é a representação abstrata da estrutura da sentença, o termo Lean é a
-- formalização desta representação. `Repr` imprime o termo; `ToString` faz o
-- caminho inverso do *parsing*, devolve, a partir do termo, a sentença de
-- superfície.

def snowWhile : Sent :=
  .sent (.np2 .the (.rcn2 .dwarf .that .snowWhite .helped))
        (.vp1 .admired (.np1 .every .princess))

#eval snowWhile
#eval toString snowWhile

-- ### Exercise (1 star): preposition-phrase ⭐

-- Estenda o fragmento com sintagmas preposicionais, de modo que a sentença "A
-- dwarf defeated a giant with a sword" seja gerada de duas formas
-- estruturalmente diferentes, enquanto "A dwarf defeated Little Mook with a
-- sword" só tenha uma forma de ser gerada.

-- Primeiro acrescentamos duas regras para construir PPs a partir de uma
-- preposição e um NP. Em seguida estendemos a regra de NPs, para gerar NPs
-- como a giant with a sword. Note que não simplesmente acrescentamos uma
-- produção recursiva `NP → NP PP`. Se fizéssemos isso, não só permitiríamos
-- um número arbitrário de PPs como modificadores de NP, mas também geraríamos
-- NPs como "Little Mook with a sword" (o que queremos excluir). Por fim,
-- também estendemos a regra de VP para construir VPs com sintagmas
-- preposicionais.

-- P   ::= "with" ;
-- PP  ::= P NP ;
-- NP  ::= _NP | DET CN PP ;
-- VP  ::= _VP | TV NP PP ;

-- Como `inductive` em Lean é fechado — não dá para acrescentar construtores a
-- um tipo já definido —, a extensão exige redefinir todo o agrupamento
-- mutuamente recursivo (`Sent`, `NP`, `RCN`, `VP`, `INF`), acrescentando `PP`
-- a ele, em vez de simplesmente estender `NP`/`VP` originais. Isolamos o
-- restante num namespace próprio, para não afetar o fragmento original de
-- `NP`/`VP` sem PPs.

namespace WithPP

inductive P where
  | «with»
  deriving Repr

instance : ToString P := ⟨fun | .with => "with"⟩

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook
    | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)
    | np3 (det : DET) (cn : CN) (pp : PP)
  deriving Repr

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)
    | vp4 (tv : TV) (np : NP) (pp : PP)
  deriving Repr

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
  deriving Repr

  inductive PP where
    | pp1 (p : P) (np : NP)
  deriving Repr
end

mutual

def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White"
  | .alice => "Alice"
  | .dorothy => "Dorothy"
  | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook"
  | .atreyu => "Atreyu"
  | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"
  | .np3 det cn pp => s!"{det} {cn} {pp.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 =>
    s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"
  | .vp4 tv np pp =>
    s!"{tv} {np.toStringImpl} {pp.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer"
  | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"

def PP.toStringImpl : PP → String
  | .pp1 p np => s!"{p} {np.toStringImpl}"

end

instance : ToString Sent := ⟨Sent.toStringImpl⟩

-- A ambiguidade pedida está em `giantWithSword1`/`giantWithSword2`: o PP
-- `with a sword` pode se ligar dentro do NP (modificando `a giant`) ou direto
-- na VP (modificando o evento de derrotar); as duas árvores são diferentes,
-- mas produzem a mesma sentença de superfície. Já `mookWithSword` só admite a
-- segunda leitura, porque `NP ::= DET CN PP` exige um determinante e `CN`, e
-- "Little Mook" é um nome próprio sem determinante — não há como formar
-- `Little Mook with a sword` como um único NP.

-- PP dentro do NP objeto ("a giant with a sword" é um NP).
def giantWithSword1 : Sent :=
  .sent (.np1 .a .dwarf)
    (.vp1 .defeated
      (.np3 .a .giant (.pp1 .with (.np1 .a .sword))))

-- mesma sentença, PP ligado à VP em vez do NP.
def giantWithSword2 : Sent :=
  .sent (.np1 .a .dwarf)
    (.vp4 .defeated (.np1 .a .giant)
      (.pp1 .with (.np1 .a .sword)))

-- única leitura possível
def mookWithSword : Sent :=
  .sent (.np1 .a .dwarf)
    (.vp4 .defeated .littleMook
      (.pp1 .with (.np1 .a .sword)))

end WithPP

#eval toString WithPP.giantWithSword1
#eval toString WithPP.giantWithSword2
#eval toString WithPP.mookWithSword

-- As duas árvores diferentes imprimem a mesma sentença de superfície, a
-- ambiguidade pedida.

-- ### Exercise (1 star): complex-relative-clauses ⭐

-- Estenda o fragmento com orações relativas complexas, em que a oração
-- relativa coordena duas VPs paralelas ou dois pares NP-TV paralelos (não
-- sentenças completas). O fragmento deve gerar, entre outras, a sentença "The
-- dwarf that Snow White helped and Goldilocks admired cheered". Que problemas
-- você encontra?

-- Acrescentamos `COORD` e duas regras para `RCN`, cada uma coordenando duas
-- ocorrências da mesma forma — ou duas VPs, ou dois pares NP-TV:

-- COORD ::= "and" ;
-- RCN   ::= _RCN | CN "that" VP COORD VP
--                | CN "that" NP TV COORD NP TV ;

-- Como antes, `inductive` fechado obriga a redefinir todo o agrupamento
-- mutual só para acrescentar construtores a `RCN`.

namespace WithCoord

inductive COORD where
  | and
  deriving Repr

instance : ToString COORD := ⟨fun | .and => "and"⟩

mutual
  inductive Sent where
    | sent (np : NP) (vp : VP)
  deriving Repr

  inductive NP where
    | snowWhite | alice | dorothy | goldilocks | littleMook
    | atreyu
    | everyone | someone
    | np1 (det : DET) (cn : CN)
    | np2 (det : DET) (rcn : RCN)
  deriving Repr

  inductive RCN where
    | rcn1 (cn : CN) (compl : That) (vp : VP)
    | rcn2 (cn : CN) (compl : That) (np : NP) (tv : TV)
    | rcn3 (adj : ADJ) (cn : CN)
    | rcn4 (cn : CN) (compl : That)
        (vp1 : VP) (coord : COORD) (vp2 : VP)
    | rcn5 (cn : CN) (compl : That)
        (np1 : NP) (tv1 : TV) (coord : COORD)
        (np2 : NP) (tv2 : TV)
  deriving Repr

  inductive VP where
    | laughed | cheered | shuddered
    | vp1 (tv : TV) (np : NP)
    | vp2 (dv : DV) (np1 np2 : NP)
    | vp3 (av : AV) (marker : To) (inf : INF)
  deriving Repr

  inductive INF where
    | laugh | cheer | shudder
    | inf1 (tinf : TINF) (np : NP)
  deriving Repr
end

mutual

def Sent.toStringImpl : Sent → String
  | .sent np vp => s!"{np.toStringImpl} {vp.toStringImpl}"

def NP.toStringImpl : NP → String
  | .snowWhite => "Snow White" | .alice => "Alice"
  | .dorothy => "Dorothy" | .goldilocks => "Goldilocks"
  | .littleMook => "Little Mook" | .atreyu => "Atreyu"
  | .everyone => "everyone" | .someone => "someone"
  | .np1 det cn => s!"{det} {cn}"
  | .np2 det rcn => s!"{det} {rcn.toStringImpl}"

def RCN.toStringImpl : RCN → String
  | .rcn1 cn _ vp => s!"{cn} that {vp.toStringImpl}"
  | .rcn2 cn _ np tv => s!"{cn} that {np.toStringImpl} {tv}"
  | .rcn3 adj cn => s!"{adj} {cn}"
  | .rcn4 cn _ vp1 coord vp2 =>
    s!"{cn} that {vp1.toStringImpl} {coord} " ++
      s!"{vp2.toStringImpl}"
  | .rcn5 cn _ np1 tv1 coord np2 tv2 =>
    s!"{cn} that {np1.toStringImpl} {tv1} {coord} " ++
      s!"{np2.toStringImpl} {tv2}"

def VP.toStringImpl : VP → String
  | .laughed => "laughed" | .cheered => "cheered"
  | .shuddered => "shuddered"
  | .vp1 tv np => s!"{tv} {np.toStringImpl}"
  | .vp2 dv np1 np2 =>
    s!"{dv} {np1.toStringImpl} {np2.toStringImpl}"
  | .vp3 av _ inf => s!"{av} to {inf.toStringImpl}"

def INF.toStringImpl : INF → String
  | .laugh => "laugh" | .cheer => "cheer"
  | .shudder => "shudder"
  | .inf1 tinf np => s!"{tinf} {np.toStringImpl}"

end

instance : ToString Sent := ⟨Sent.toStringImpl⟩

end WithCoord

-- Dois exemplos: a sentença do enunciado usa `rcn5` (coordenação de pares
-- NP-TV, a RCN é sobre o objeto em ambos os ramos); a outra usa `rcn4`
-- (coordenação de VPs, a RCN é sobre o sujeito em ambos os ramos).

#eval toString (WithCoord.Sent.sent
  (.np2 .the  (.rcn5 .dwarf .that .snowWhite .helped
     .and .goldilocks .admired))
  .cheered)

#eval toString (WithCoord.Sent.sent
  (.np2 .the (.rcn4 .dwarf .that
    (.vp1 .helped .goldilocks) .and
    (.vp1 .admired .snowWhite)))
  .laughed)

-- `rcn4` e `rcn5` só coordenam formas paralelas (VP com VP, ou NP-TV com
-- NP-TV), exatamente porque são regras separadas; misturá-las produziria "the
-- dwarf that Goldilocks helped and admired Snow White", que é agramatical: na
-- primeira RCN o vazio (*gap*) está no objeto ("Goldilocks helped ␣"), na
-- segunda está no sujeito ("␣ admired Snow White"), e não há como coordenar
-- as duas leituras numa só sentença. Coordenar `Sent` inteiras em vez de
-- VPs/pares NP-TV geraria justamente essa mistura, por isso o fragmento não
-- faz isso.

-- O *gap* é a posição, dentro da `RCN`, onde entraria o `CN` que ela modifica
-- — em `rcn1` (`CN "that" VP`) o gap é o sujeito da VP; em `rcn2`
-- (`CN "that" NP TV`) é o objeto do TV. `rcn4` sempre coordena dois
-- gaps-sujeito e `rcn5` dois gaps-objeto; nenhuma das duas mistura um tipo de
-- gap com o outro.

-- O problema é que `rcn4`/`rcn5` não são recursivas: cada uma coordena
-- exatamente duas ocorrências. Não é possível gerar "the dwarf that helped
-- Goldilocks and admired the princess that shuddered and laughed" sem
-- acrescentar mais uma regra para RCNs de três coordenadas, depois quatro, e
-- assim por diante — o fragmento não captura a generalização "coordenação de
-- qualquer número de VPs paralelas".

-- ## Uma língua para falar de classes

-- O livro não dá código Haskell nesta seção — adia a implementação para o
-- motor de inferência do capítulo 5. A gramática é um fragmento minúsculo
-- para perguntar e afirmar coisas sobre classes:

-- Q ::= Are all PN PN?
--     | Are no PN PN?
--     | Are any PN PN?
--     | Are any PN not PN?
--     | What about PN?

-- S ::= All PN are PN.
--     | No PN are PN.
--     | Some PN are PN.
--     | Some PN are not PN.

-- onde `PN` (plural noun) fica deliberadamente sem gramática própria. A
-- tradução para Lean é barata e o capítulo 5 a reaproveita — uma base de
-- conhecimento consultável por essas perguntas e afirmações.

abbrev PN := String

inductive Statement where
  | allAre (a b : PN)
  | noneAre (a b : PN)
  | someAre (a b : PN)
  | someAreNot (a b : PN)
  deriving DecidableEq, Repr

inductive Query where
  | areAllPNPN (a b : PN)
  | areNoPNPN (a b : PN)
  | areAnyPNPN (a b : PN)
  | areAnyPNNotPN (a b : PN)
  | whatAbout (a : PN)
  deriving DecidableEq, Repr

end English

