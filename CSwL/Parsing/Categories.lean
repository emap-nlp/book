import CSwL.Parsing.Combinators
import CSwL.Parsing.Lexicon

-- # Análise Sintática com Categorias

namespace Parsing

-- Vamos analisar uma entrada em que cada palavra já foi substituída por uma
-- categoria do léxico. Os parsers terão tipo
-- `Parser Cat (ParseTree Cat Cat)`. Assim, tanto as folhas quanto os nós
-- internos das árvores guardam categorias com rótulos, traços e listas de
-- subcategorização.

-- Para consultar a categoria de uma árvore, usamos `t2c`. Se a árvore é uma
-- folha, a função devolve sua categoria. Se é um nó, devolve a categoria da
-- raiz. A função `agreeC` usa `agree` para testar a concordância entre duas
-- árvores.

-- A atribuição de um traço também pode ser feita sobre uma árvore. A função
-- `assignT` aplica `assign` à categoria da raiz e usa `Option.map` para
-- reconstruir a folha ou o nó com a categoria resultante. As filhas são
-- conservadas. Se a atribuição falhar, o resultado será `Option.none`.

-- O parser elementar `leafP l` reconhece uma categoria cujo rótulo é `l` e a
-- transforma em uma folha. Ao construir parsers mais complexos, precisaremos
-- também converter resultados de `combine` e `assign` em passos da análise. A
-- função `fromOption` faz essa conversão. Para `some b`, produz `pure b`, que
-- entrega `b` sem consumir entrada. Para `Option.none`, produz `failure`, de
-- modo que essa tentativa de análise não devolva resultado.

-- Exibiremos cada árvore como uma AVM que contém as AVMs de suas filhas no
-- atributo `ARGS`, como uma estrutura de traços aninhada (Sag and Wasow,
-- 1999). Uma folha mostra apenas a categoria lexical. Um nó com filhas mostra
-- os atributos da categoria da raiz e a lista de árvores filhas em `ARGS`.
-- Seu atributo `PHON` reúne as formas das folhas, na ordem em que aparecem.
-- Por exemplo, o `VP` de `loved her` tem `PHON ⟨loved, her⟩`. Essa lista é
-- calculada para a exibição; o campo `Cat.phon` da categoria do sintagma
-- continua contendo `"_"`. O bloco de detalhes implementa essa apresentação.

abbrev CatParser := Parser Cat (ParseTree Cat Cat)

def t2c : ParseTree Cat Cat → Cat
  | .leaf c => c
  | .branch c _ => c

def agreeC (t1 t2 : ParseTree Cat Cat) : Bool :=
  agree (t2c t1) (t2c t2)

def leafP (label : CatLabel) : CatParser :=
  .leaf <$> satisfy (·.label == label)

def assignT (f : Feat) : ParseTree Cat Cat → Option (ParseTree Cat Cat)
  | .leaf c => (assign f c).map .leaf
  | .branch c ts => (assign f c).map (.branch · ts)

def fromOption {α β : Type} : Option β → Parser α β
  | some b => pure b
  | none => failure

-- THE FOLLOWING DETAILS CAN BE SKIPPED (Exibindo árvores como AVMs)
partial def ParseTree.yield : ParseTree Cat Cat → List String
  | .leaf c => [c.phon]
  | .branch _ ts => ts.flatMap ParseTree.yield

partial def ParseTree.fmt : ParseTree Cat Cat → Std.Format
  | .leaf c => avmFmt c.attrs
  | .branch c [] => avmFmt c.attrs
  | t@(.branch c ts) =>
    -- a phrase has no form of its own: show the forms of its leaves
    let phonAttr := "PHON " ++ listFmt (t.yield.map Std.Format.text)
    let cattrs := c.attrs.take 1 ++ [phonAttr] ++ c.attrs.drop 1
    let attrs := Std.Format.group
      (Std.Format.joinSep cattrs ("," ++ Std.Format.line))
    let args := "ARGS " ++ Std.Format.nest 5 (listFmt (ts.map ParseTree.fmt))
    Std.Format.bracket "[" (attrs ++ "," ++ Std.Format.line ++ args) "]"

instance : Repr (ParseTree Cat Cat) := ⟨fun t _ => t.fmt⟩
-- END DETAILS

open Examples in
#eval (.branch ⟨"_", "S", [], []⟩ [.leaf she, .leaf laughs] : ParseTree Cat Cat)

-- Começamos pelas categorias que reconhecemos diretamente na entrada. Os
-- determinantes têm rótulo `DET`, os substantivos comuns têm rótulo `CN`, as
-- preposições têm rótulo `PREP` e os auxiliares têm rótulo `AUX`. Para cada
-- uma, basta aplicar `leafP` com o rótulo correspondente.

-- Esses parsers reconhecem uma única categoria lexical por vez. Em
-- particular, o parser de `CN` aceita apenas substantivos comuns encontrados
-- no léxico.

def parseDET : CatParser := leafP "DET"
def parseCN : CatParser := leafP "CN"
def parsePrep : CatParser := leafP "PREP"
def parseAux : CatParser := leafP "AUX"

-- Um sintagma nominal pode ser uma categoria lexical com rótulo `NP`, como a
-- de um pronome ou nome próprio. Também pode ser construído pela regra
-- `NP → DET CN`. A função `npRule` analisa o determinante e o substantivo
-- comum e combina seus traços. Se houver incompatibilidade, a tentativa
-- falha. Se a combinação der certo, o nó `NP` recebe os traços resultantes e
-- tem as duas árvores como filhas. O parser `parseNP` reúne a alternativa
-- lexical e essa regra.

-- O sintagma preposicional segue a regra `PP → PREP NP`. Depois de analisar a
-- preposição e o sintagma nominal, `ppRule` atribui `Feat.accOrDat` à raiz da
-- árvore do `NP`. Esse passo expressa controle de traços. O pronome `her`
-- aceita esse caso, mas `she` já tem `Feat.nom`, e a atribuição falha. Assim,
-- a regra aceita `with her` e recusa `with she`.

-- Os traços da preposição são combinados com os do sintagma nominal
-- atualizado, e o resultado vai para o nó `PP`. Sua segunda filha é a árvore
-- que recebeu o caso. Para ler os complementos de um verbo, `parseNPorPP`
-- permite escolher entre os dois tipos de sintagma. A função `parseNPsorPPs`
-- usa `many` para analisar sequências deles, incluindo a sequência vazia.

def npRule : CatParser := do
  let det ← parseDET
  let cn ← parseCN
  let fs ← fromOption (combine (t2c det) (t2c cn))
  if !agreeC det cn then failure
  return .branch ⟨"_", "NP", fs, []⟩ [det, cn]

def parseNP : CatParser := leafP "NP" <|> npRule

def ppRule : CatParser := do
  let prep ← parsePrep
  let np ← parseNP
  let np' ← fromOption (assignT .accOrDat np)
  let fs ← fromOption (combine (t2c prep) (t2c np'))
  return .branch ⟨"_", "PP", fs, []⟩ [prep, np']

def parsePP : CatParser := ppRule

def parseNPorPP : CatParser := parseNP <|> parsePP

def parseNPsorPPs : Parser Cat (List (ParseTree Cat Cat)) :=
  many parseNPorPP

open Examples in
#eval ((just parseNP).run [the, child]).map (·.1)
#eval ((just parsePP).run (lexicon "with" ++ lexicon "her")).map (·.1)
#eval ((just parsePP).run (lexicon "with" ++ lexicon "she")).length

-- Para construir um sintagma verbal, `vpRule` lê uma categoria lexical com
-- rótulo `VP` e uma sequência de sintagmas nominais ou preposicionais. A
-- sequência precisa satisfazer a lista de subcategorização do verbo. A função
-- `matchSubcat` compara as listas na mesma ordem. Elas devem ter o mesmo
-- comprimento, e cada complemento deve ter o rótulo esperado e traços
-- compatíveis com os exigidos.

-- Por exemplo, `loved` espera um `NP` com `Feat.accOrDat`. Em
-- `Alice loved the dwarf`, o objeto é `the dwarf`; em `Alice loved him`, é
-- `him`. Para uma entrada de `gave` que espera um `PP` com `Feat.to`, um
-- complemento com `Feat.with` falha no teste de concordância.

-- A lista de subcategorização registra os complementos que ainda precisam ser
-- encontrados. Quando a regra os encontra, constrói um nó `VP` com lista
-- vazia e com o verbo e os complementos como filhas. A folha lexical do verbo
-- conserva a lista original, registrando as exigências que foram satisfeitas
-- nesse nó.

-- Há duas maneiras de obter um `VP` aceito por `parseVP`. A função
-- `finVpRule` exige que o sintagma construído por `vpRule` aceite
-- `Feat.tense`. Já `auxVpRule` lê um auxiliar e um sintagma verbal que aceite
-- `Feat.infl`. Nesse caso, o novo nó `VP` recebe os traços do auxiliar e tem
-- como filhas o auxiliar e o sintagma no infinitivo. Isso permite analisar
-- `didn't smile`, enquanto `didn't smiled` falha pela incompatibilidade de
-- forma verbal.

def matchSubcat : List Cat → List Cat → Bool
  | [], [] => true
  | x :: xs, y :: ys =>
    x.label == y.label && agree x y && matchSubcat xs ys
  | _, _ => false

def vpRule : CatParser := do
  let vp ← leafP "VP"
  let xps ← parseNPsorPPs
  if !matchSubcat (t2c vp).subcatList (xps.map t2c) then failure
  return .branch ⟨"_", "VP", (t2c vp).fs, []⟩ (vp :: xps)

def finVpRule : CatParser := do
  let vp ← vpRule
  fromOption (assignT .tense vp)

def auxVpRule : CatParser := do
  let aux ← parseAux
  let inf ← vpRule
  let inf' ← fromOption (assignT .infl inf)
  return .branch ⟨"_", "VP", (t2c aux).fs, []⟩ [aux, inf']

def parseVP : CatParser := finVpRule <|> auxVpRule

open Examples in
#eval ((just parseVP).run [laughs]).map (·.1)
#eval ((just parseVP).run (lexicon "didn't" ++ lexicon "smile")).map (·.1)
#eval ((just parseVP).run (lexicon "didn't" ++ lexicon "smiled")).length

-- A regra sujeito–predicado, `S → NP VP`, combina um sintagma nominal com um
-- sintagma verbal. Para que a combinação seja aceita, o sujeito deve permitir
-- a atribuição de `Feat.nom`, e os traços do sujeito e do predicado devem
-- concordar. O predicado também deve ter completado sua lista de
-- subcategorização. A árvore resultante tem um nó `S` com o sujeito
-- atualizado e o predicado como filhas. O parser `parseSent` usa essa regra.

-- Nesta gramática, essa é a única regra para `S`, e por isso uma sentença tem
-- uma só oração. Embora o léxico tenha `and`, a sentença
-- `Alice smiled and Dorothy laughed.` não tem análise, como mostra o último
-- exemplo.

-- A função `parseWith` reúne as etapas da análise de uma entrada, com um
-- léxico `db` e um parser `p` dados como argumentos. Primeiro, `lexer` produz
-- a lista de palavras. Depois, `collectCats` consulta `db` e enumera as
-- escolhas de categorias para a entrada. Para cada escolha, aplicamos `p` com
-- `just`, conservando somente as análises que consomem todas as categorias.
-- Por fim, reunimos as árvores dessas análises em uma lista. Os parsers das
-- regras trabalham sobre categorias e não consultam o léxico. Por isso, só
-- `parseWith` depende dele, e `prs` é `parseWith` com o léxico `lexicon` e o
-- parser `parseSent`.

-- O resultado usa `Except`. Se uma palavra é desconhecida, `collectCats`
-- devolve um erro com a mensagem correspondente. Em um bloco `do` de
-- `Except`, um resultado `Except.error` interrompe a sequência de passos e
-- propaga o erro. Se todas as palavras são conhecidas, mas nenhuma análise é
-- encontrada, `throw "no parse"` produz outro erro. Quando há sucesso,
-- `return trees` entrega a lista de árvores com `Except.ok`. Essa lista
-- contém pelo menos uma árvore.

-- Os exemplos permitem distinguir essas situações. A entrada `Her loved I.`
-- viola as exigências de caso, enquanto `She despised me.` contém uma palavra
-- ausente do léxico. Os exemplos com `gave` testam a preposição do
-- complemento, e o penúltimo combina auxiliar, infinitivo e um complemento
-- instrumental.

def sRule : CatParser := do
  let np ← parseNP
  let vp ← parseVP
  let np' ← fromOption (assignT .nom np)
  if !agreeC np vp then failure
  if !(t2c vp).subcatList.isEmpty then failure
  return .branch ⟨"_", "S", [], []⟩ [np', vp]

def parseSent : CatParser := sRule

def parseWith (db : String → List Cat) (p : CatParser) (s : String) :
    Except String (List (ParseTree Cat Cat)) := do
  let catLists ← collectCats db (lexer s)
  let trees := catLists.flatMap fun cs => ((just p).run cs).map (·.1)
  if trees.isEmpty then throw "no parse"
  return trees

def prs (s : String) : Except String (List (ParseTree Cat Cat)) :=
  parseWith lexicon parseSent s

#eval prs "I loved her."
#eval prs "Her loved I."
#eval prs "She despised me."
#eval prs "Goldilocks gave the sword to Alice."
#eval prs "Goldilocks gave the sword with Alice."
#eval prs "Atreyu didn't kick the giant with a dagger."
#eval prs "Alice smiled and Dorothy laughed."

-- ### Exercise (3 stars): complex-det ⭐⭐⭐

-- Acrescente uma regra para determinantes complexos, formados por uma função
-- de determinante e um numeral. Ela deve cobrir *less than n*, *more than n*,
-- *at least n*, *at most n* e *exactly n*. O pré-processamento já torna cada
-- função de determinante uma única palavra. Você também vai precisar, é
-- claro, de um modo de reconhecer os numerais. Aqui, um numeral é uma palavra
-- formada só por algarismos, como `3` ou `23`, e quem o reconhece é o léxico,
-- que lhe dá a categoria `NUM`: não é preciso um parser para numerais.

-- Faça isso em três passos:

-- - `lexicon'` estende `lexicon` com as entradas `DF` que faltam, `at_least`,
--   `at_most` e `exactly`, e dá a categoria `NUM` a toda palavra formada só por
--   algarismos;

-- - `complexDetRule` analisa um `DET` formado por um `DF` seguido de um `NUM`,
--   com os traços do `DF`;

-- - `complexNpRule` analisa um `NP` formado por esse `DET` e um `CN`, com os
--   traços combinados por `combine`, e `parseNP'` junta `parseNP` e a nova
--   regra.

-- Os testes usam `parseWith` com `lexicon'` e `parseNP'`, e `Except.toBool`
-- dá `true` para um resultado `.ok`. Para analisar uma sentença inteira, como
-- *Less than 3 dwarfs smiled*, `sRule` teria de usar `parseNP'`; aqui
-- testamos só o sintagma nominal.

def lexicon' (w : String) : List Cat :=
  sorry

def complexDetRule : CatParser :=
  sorry

def complexNpRule : CatParser :=
  sorry

def parseNP' : CatParser := parseNP <|> complexNpRule

theorem complexDet_less_than :
    (parseWith lexicon' parseNP' "Less than 3 dwarfs").toBool = true := by
  sorry

theorem complexDet_at_least :
    (parseWith lexicon' parseNP' "At least 2 wizards").toBool = true := by
  sorry

theorem complexDet_exactly :
    (parseWith lexicon' parseNP' "Exactly 1 princess").toBool = true := by
  sorry

theorem complexDet_agreement :
    (parseWith lexicon' parseNP' "Less than 3 dwarf").toBool = false := by
  sorry

theorem complexDet_simple :
    (parseWith lexicon' parseNP' "The dwarfs").toBool = true := by
  sorry

end Parsing

