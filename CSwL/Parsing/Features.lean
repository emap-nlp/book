-- # Traços e Categorias

namespace Parsing

-- A análise de uma sentença depende de informações que os rótulos sintáticos,
-- por si sós, deixam em aberto. Em inglês, `she laughs` é uma sentença,
-- enquanto `they laughs` viola a concordância de número entre sujeito e
-- verbo. Para representar essa informação, vamos associar às categorias
-- sintáticas traços como número, pessoa, gênero e caso.

-- Podemos tratar a concordância de duas maneiras. Na visão de **controle**,
-- os traços de um constituinte determinam os de outro. Uma regra pode, por
-- exemplo, atribuir caso nominativo ao sujeito. Na visão de **restrição**,
-- cada constituinte fornece informações parciais, e a concordância resulta de
-- verificar se elas são compatíveis. Nesse teste, os dois constituintes
-- contribuem para a informação resultante. Nosso sistema combina os dois
-- mecanismos.

-- Se os traços têm um número finito de valores, acrescentá-los a uma
-- gramática livre de contexto permite abreviar um conjunto maior de regras
-- livres de contexto. Considere `S → NP VP` com concordância de número. Se o
-- sujeito especifica singular ou plural e o predicado pode deixar o número em
-- aberto, temos quatro possibilidades: `S → NP{Sg} VP{}`,
-- `S → NP{Sg} VP{Sg}`, `S → NP{Pl} VP{}` e `S → NP{Pl} VP{Pl}`. Aqui, `{}`
-- indica ausência de informação de número. Cada combinação pode ser tratada
-- como um novo símbolo da gramática. Como há apenas um número finito dessas
-- combinações, o conjunto de regras resultante também é finito.

-- Representaremos todos os valores de traços pelo tipo `Feat` e uma coleção
-- desses valores por uma lista, `Agreement`. Isso permite usar o mesmo tipo
-- de lista para os traços de qualquer categoria. A verificação de tipos,
-- porém, aceita listas com valores incompatíveis, como singular e plural
-- juntos. A compatibilidade será verificada pelas funções que combinam os
-- traços.

inductive Feat where
  | masc | fem | neutr | mascOrFem
  | sg | pl
  | fst | snd | thrd
  | nom | accOrDat
  | pers | refl | wh
  | tense | infl
  | on | with | by | to | from
  deriving Repr, DecidableEq
def Feat.toString : Feat → String
  | .masc => "Masc" | .fem => "Fem" | .neutr => "Neutr"
  | .mascOrFem => "MascOrFem"
  | .sg => "Sg" | .pl => "Pl"
  | .fst => "Fst" | .snd => "Snd" | .thrd => "Thrd"
  | .nom => "Nom" | .accOrDat => "AccOrDat"
  | .pers => "Pers" | .refl => "Refl" | .wh => "Wh"
  | .tense => "Tense" | .infl => "Infl"
  | .on => "On" | .with => "With" | .by => "By" | .to => "To"
  | .from => "From"

instance : ToString Feat := ⟨Feat.toString⟩

abbrev Agreement := List Feat

-- Os valores de `Feat` são agrupados conforme a informação que expressam. As
-- listas `genderFeats`, `numberFeats` e `personFeats` contêm,
-- respectivamente, os valores de gênero, número e pessoa. As demais listas
-- agrupam os valores de caso, tipo de pronome, forma verbal e preposição. A
-- lista `allFeats` reúne todos esses valores.

-- O caso gramatical indica a função de um `NP` na oração. Nos pronomes do
-- inglês, o nominativo, `Feat.nom`, aparece nas formas usadas como sujeito,
-- como `she`, `he` e `I`. O acusativo corresponde ao objeto direto, e o
-- dativo, ao objeto indireto. Como as formas inglesas `her`, `him` e `me`
-- servem para ambos, usamos o valor `Feat.accOrDat`. Esse valor também
-- representa o caso do `NP` que segue uma preposição.

-- Para obter os valores de um determinado grupo em uma lista de traços, basta
-- filtrar os que pertencem à lista correspondente. É o que fazem `gender`,
-- `number`, `person`, `gcase`, `pronType`, `tense` e `prepType`.

-- Dois valores distintos do mesmo grupo normalmente entram em conflito. Um
-- constituinte, por exemplo, não pode ter simultaneamente os valores
-- `Feat.sg` e `Feat.pl`. O valor `Feat.mascOrFem` expressa uma disjunção e
-- exige um tratamento próprio. Ele é compatível com `Feat.masc` e com
-- `Feat.fem`, mas conflita com `Feat.neutr`. Quando uma lista contém a
-- disjunção junto com um dos valores mais específicos, a função `prune`
-- remove a disjunção. Se só houver a disjunção e o valor neutro, ambos
-- permanecem para que o conflito possa ser detectado.

def genderFeats   : Agreement := [.masc, .fem, .neutr, .mascOrFem]
def numberFeats   : Agreement := [.sg, .pl]
def personFeats   : Agreement := [.fst, .snd, .thrd]
def caseFeats     : Agreement := [.nom, .accOrDat]
def pronTypeFeats : Agreement := [.pers, .refl, .wh]
def tenseFeats    : Agreement := [.tense, .infl]
def prepTypeFeats : Agreement := [.on, .with, .by, .to, .from]

def allFeats : Agreement :=
  genderFeats ++ numberFeats ++ personFeats ++ caseFeats ++
    pronTypeFeats ++ tenseFeats ++ prepTypeFeats

def gender (fs : Agreement) : Agreement :=
  fs.filter (· ∈ genderFeats)
def number (fs : Agreement) : Agreement :=
  fs.filter (· ∈ numberFeats)
def person (fs : Agreement) : Agreement :=
  fs.filter (· ∈ personFeats)
def gcase (fs : Agreement) : Agreement :=
  fs.filter (· ∈ caseFeats)
def pronType (fs : Agreement) : Agreement :=
  fs.filter (· ∈ pronTypeFeats)
def tense (fs : Agreement) : Agreement :=
  fs.filter (· ∈ tenseFeats)
def prepType (fs : Agreement) : Agreement :=
  fs.filter (· ∈ prepTypeFeats)

def prune (fs : Agreement) : Agreement :=
  if .masc ∈ fs || .fem ∈ fs then fs.erase .mascOrFem else fs

#eval prune [.mascOrFem, .fem, .sg]
#eval prune [.mascOrFem, .neutr, .sg]

-- Uma categoria sintática reúne quatro componentes. A forma fonológica
-- identifica a expressão lexical, o rótulo indica a categoria, e os traços
-- registram as informações de concordância. O quarto componente é a **lista
-- de subcategorização**, que descreve as categorias com que a expressão deve
-- se combinar. Um verbo transitivo, por exemplo, espera um `NP` como objeto.

-- A estrutura `Cat` guarda esses componentes nos campos `phon`, `label`, `fs`
-- e `subcatList`. Como cada item da lista de subcategorização é também uma
-- categoria, o tipo é recursivo. Usamos textos tanto para a forma fonológica
-- quanto para o rótulo. Uma categoria lexical tem a sua forma no campo
-- `phon`; uma categoria sem conteúdo lexical usa `"_"` nesse campo.

-- Para exibir categorias, usaremos uma **matriz de atributos e valores**, ou
-- AVM, como nas gramáticas de unificação, entre elas a HPSG (Sag and Wasow,
-- 1999). Cada componente aparece associado a um nome de atributo. O rótulo
-- aparece em `CAT`, a forma lexical em `PHON` e a lista de subcategorização
-- em `SUBCAT`. Os grupos de traços aparecem em `GEN`, `NUM`, `PER`, `CASE`,
-- `PRON`, `VFORM` e `PFORM`.

-- Por exemplo, a categoria de `she` é exibida como
-- `[CAT NP, PHON she, GEN fem, NUM sg, PER thrd, CASE nom, PRON pers]`. Os
-- atributos cujas listas de valores são vazias são omitidos. Assim, o pronome
-- não exibe `SUBCAT`, porque sua lista de subcategorização é vazia. Uma
-- categoria com forma `"_"` também omite `PHON`.

-- Os colchetes `[…]` delimitam um AVM, e `⟨…⟩` delimita uma lista de AVMs. A
-- representação
-- `[CAT VP, PHON loved, VFORM tense, SUBCAT ⟨[CAT NP, CASE accOrDat]⟩]`
-- descreve um verbo com um objeto ainda por combinar. O valor de `SUBCAT`
-- especifica que esse objeto deve ser um `NP` de caso `Feat.accOrDat`. O
-- bloco de detalhes implementa essa apresentação, e os exemplos mostram
-- categorias lexicais e uma categoria sem conteúdo lexical.

abbrev CatLabel := String
abbrev Phon := String

structure Cat where
  phon : Phon
  label : CatLabel
  fs : Agreement
  subcatList : List Cat
  deriving Repr, BEq

-- THE FOLLOWING DETAILS CAN BE SKIPPED (Exibindo categorias como AVMs)
open Std (Format)

def featPairs (fs : Agreement) : List String :=
  let attrs := [("GEN", gender fs), ("NUM", number fs),
    ("PER", person fs), ("CASE", gcase fs), ("PRON", pronType fs),
    ("VFORM", tense fs), ("PFORM", prepType fs)]
  (attrs.filter (!·.2.isEmpty)).map fun (a, vs) =>
    a ++ " " ++ "/".intercalate (vs.map fun v => (toString v).decapitalize)

def avmFmt (attrs : List Format) : Format :=
  Format.bracket "[" (Format.joinSep attrs ("," ++ Format.line)) "]"

def listFmt (xs : List Format) : Format :=
  Format.bracket "⟨" (Format.joinSep xs ("," ++ Format.line)) "⟩"

def featAVM (fs : Agreement) : String :=
  (avmFmt ((featPairs fs).map Format.text)).pretty

def Cat.attrs : Cat → List Format
  | ⟨phon, label, fs, subcatList⟩ =>
    let phonAttr := if phon == "_" then [] else [f!"PHON {phon}"]
    let sub := if subcatList.isEmpty then []
      else [f!"SUBCAT " ++ listFmt (subcatList.map fun c => avmFmt c.attrs)]
    [f!"CAT {label}"] ++ phonAttr ++ (featPairs fs).map Format.text ++ sub

instance : Repr Cat := ⟨fun c _ => avmFmt c.attrs⟩
-- END DETAILS

namespace Examples

def she : Cat := ⟨"she", "NP", [.pers, .thrd, .sg, .fem, .nom], []⟩
def her : Cat := ⟨"her", "NP", [.pers, .thrd, .sg, .fem, .accOrDat], []⟩
def they : Cat := ⟨"they", "NP", [.pers, .thrd, .pl, .nom], []⟩
def alice : Cat := ⟨"Alice", "NP", [.thrd, .sg, .fem], []⟩
def laughs : Cat := ⟨"laughs", "VP", [.tense, .sg, .thrd], []⟩
def child : Cat := ⟨"child", "CN", [.sg, .thrd, .mascOrFem], []⟩
def thing : Cat := ⟨"thing", "CN", [.sg, .thrd, .neutr], []⟩
def the : Cat := ⟨"the", "DET", [], []⟩

end Examples

open Examples in

#eval she

#eval ({
   phon := "_", label := "NP", fs := [.sg],
   subcatList := [] } : Cat)

-- A visão de restrição da concordância requer uma operação que reúna
-- informações compatíveis. A função `combine` recebe duas categorias e tenta
-- combinar suas listas de traços. Se houver conflito, devolve `Option.none`.
-- Se a combinação for possível, devolve a lista resultante com `Option.some`.

-- Em termos de AVMs, essa operação é uma **unificação** das informações de
-- concordância. Os AVMs `[PER thrd]` e `[NUM sg]` fornecem informações que
-- podem ser reunidas em `[NUM sg, PER thrd]`. Já `[NUM sg]` e `[NUM pl]`
-- impõem valores incompatíveis ao mesmo atributo e não podem ser combinadas.

-- Para construir a lista combinada, `combine` filtra `allFeats`, conservando
-- os valores presentes em qualquer uma das categorias. Cada valor aparece
-- assim uma única vez, na ordem de `allFeats`. Depois, `prune` remove a
-- disjunção de gênero quando há um valor mais específico. A combinação é
-- aceita se cada grupo contém no máximo um valor. A função `agree` verifica
-- se essa tentativa teve sucesso.

-- A visão de controle aparece em `assign f c`, que atribui um traço `f` a uma
-- categoria `c`. Para isso, a função combina os traços de `c` com uma
-- categoria que contém apenas `f`. A atribuição também pode falhar. Atribuir
-- `Feat.nom` ao nome `Alice` é possível, pois seus traços deixam o caso em
-- aberto. A mesma atribuição ao pronome `Examples.her` falha, pois ele já tem
-- `Feat.accOrDat`.

-- Para produzir a categoria com os novos traços, `assign` usa `Option.map`.
-- Para um resultado `some a`, a operação `o.map f` produz `some (f a)`; para
-- `Option.none`, o resultado continua sendo `Option.none`. Assim, a
-- atualização `{ c with fs := fs' }` é aplicada somente quando a combinação
-- tem sucesso. Os demais campos da categoria conservam seus valores.

def combine (cat1 cat2 : Cat) : Option Agreement :=
  let feats := prune (allFeats.filter (· ∈ cat1.fs ++ cat2.fs))
  if (gender feats).length ≤ 1 && (number feats).length ≤ 1 &&
      (person feats).length ≤ 1 && (gcase feats).length ≤ 1 &&
      (pronType feats).length ≤ 1 && (tense feats).length ≤ 1 &&
      (prepType feats).length ≤ 1
  then some feats
  else none

def agree (cat1 cat2 : Cat) : Bool :=
  (combine cat1 cat2).isSome

def assign (f : Feat) (c : Cat) : Option Cat :=
  (combine c ⟨"", "", [f], []⟩).map fun fs' => { c with fs := fs' }

open Examples

#eval (combine she laughs).map featAVM
#eval agree they laughs
#eval (combine the child).map featAVM
#eval agree child thing
#eval assign .nom alice
#eval assign .nom her

-- ### Exercise (2 stars): combine-comm ⭐⭐

-- Prove que o resultado de `combine` não depende da ordem das duas
-- categorias.

theorem combine_comm (cat1 cat2 : Cat) :
    combine cat1 cat2 = combine cat2 cat1 := by
  sorry

end Parsing

