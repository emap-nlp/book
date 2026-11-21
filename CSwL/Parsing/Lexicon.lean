import CSwL.Parsing.Features

-- # Consulta ao Léxico e Análise Léxica

namespace Parsing

-- O léxico associa cada palavra às categorias sintáticas que ela pode ter.
-- Uma palavra pode admitir mais de uma categoria. Por exemplo, `that` pode
-- ser um determinante ou um pronome relativo. Por isso, a consulta ao léxico
-- devolve uma lista de categorias.

-- Guardaremos as entradas em listas de `Cat`, agrupadas por classe de
-- palavras. Cada entrada contém a forma da palavra, seu rótulo, seus traços e
-- sua lista de subcategorização. Como são categorias lexicais, todas têm uma
-- forma no campo `Cat.phon`, exibida no atributo `PHON` da AVM. Para
-- consultar uma palavra, selecionaremos as entradas cujo campo contém essa
-- forma.

-- Começamos pelos pronomes pessoais, reflexivos, interrogativos e relativos.
-- Suas entradas especificam os traços que a forma permite determinar. Por
-- exemplo, `she` tem terceira pessoa, número singular, gênero feminino e caso
-- nominativo. Já `you` deixa o número e o caso em aberto. As formas que podem
-- funcionar como interrogativos ou relativos recebem entradas distintas, com
-- rótulos `NP` ou `REL`. A lista também inclui os usos de `that` e `which`
-- como determinantes, com rótulo `DET`.

def pronouns : List Cat := [
  -- personal pronouns
  ⟨"i",    "NP", [.pers, .fst, .sg, .nom], []⟩,
  ⟨"me",   "NP", [.pers, .fst, .sg, .accOrDat], []⟩,
  ⟨"we",   "NP", [.pers, .fst, .pl, .nom], []⟩,
  ⟨"us",   "NP", [.pers, .fst, .pl, .accOrDat], []⟩,
  ⟨"you",  "NP", [.pers, .snd], []⟩,
  ⟨"he",   "NP", [.pers, .thrd, .sg, .nom, .masc], []⟩,
  ⟨"him",  "NP", [.pers, .thrd, .sg, .accOrDat, .masc], []⟩,
  ⟨"she",  "NP", [.pers, .thrd, .sg, .nom, .fem], []⟩,
  ⟨"her",  "NP", [.pers, .thrd, .sg, .accOrDat, .fem], []⟩,
  ⟨"it",   "NP", [.pers, .thrd, .sg, .neutr], []⟩,
  ⟨"they", "NP", [.pers, .thrd, .pl, .nom], []⟩,
  ⟨"them", "NP", [.pers, .thrd, .pl, .accOrDat], []⟩,
  -- reflexive pronouns
  ⟨"myself",     "NP", [.refl, .sg, .fst, .accOrDat], []⟩,
  ⟨"ourselves",  "NP", [.refl, .pl, .fst, .accOrDat], []⟩,
  ⟨"yourself",   "NP", [.refl, .sg, .snd, .accOrDat], []⟩,
  ⟨"yourselves", "NP", [.refl, .pl, .snd, .accOrDat], []⟩,
  ⟨"himself",    "NP", [.refl, .sg, .thrd, .accOrDat, .masc], []⟩,
  ⟨"herself",    "NP", [.refl, .sg, .thrd, .accOrDat, .fem], []⟩,
  ⟨"itself",     "NP", [.refl, .sg, .thrd, .accOrDat, .neutr], []⟩,
  ⟨"themselves", "NP", [.refl, .pl, .thrd, .accOrDat], []⟩,
  -- wh-pronouns and relatives
  ⟨"who",   "NP",  [.wh, .thrd, .mascOrFem], []⟩,
  ⟨"who",   "REL", [.mascOrFem], []⟩,
  ⟨"whom",  "NP",  [.sg, .wh, .thrd, .accOrDat, .mascOrFem], []⟩,
  ⟨"whom",  "REL", [.sg, .mascOrFem, .accOrDat], []⟩,
  ⟨"what",  "NP",  [.wh, .thrd, .accOrDat, .neutr], []⟩,
  ⟨"that",  "REL", [], []⟩,
  ⟨"that",  "DET", [.sg], []⟩,
  ⟨"which", "REL", [.neutr], []⟩,
  ⟨"which", "DET", [.wh], []⟩ ]

-- Os nomes próprios recebem o rótulo `NP` e traços de pessoa, gênero e
-- número. O caso fica em aberto, para que a mesma entrada possa ser usada
-- como sujeito ou como objeto. As formas são guardadas em minúsculas, como
-- `alice` e `snowwhite`.

-- Os determinantes, com rótulo `DET`, podem especificar o número. Assim,
-- `every` exige singular e `all` exige plural. Outros, como `some` e `the`,
-- deixam esse traço em aberto.

-- Para expressões como `less than` e `more than`, usamos o rótulo `DF`, de
-- função de determinante. A análise léxica representará cada uma dessas
-- expressões por uma única forma, `less_than` ou `more_than`, que pode ser
-- consultada no léxico.

def properNames : List Cat := [
  ⟨"snowwhite",  "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"alice",      "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"dorothy",    "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"goldilocks", "NP", [.thrd, .fem, .sg], []⟩,
  ⟨"littlemook", "NP", [.thrd, .masc, .sg], []⟩,
  ⟨"atreyu",     "NP", [.thrd, .masc, .sg], []⟩ ]

def determiners : List Cat := [
  ⟨"every",   "DET", [.sg], []⟩,
  ⟨"all",     "DET", [.pl], []⟩,
  ⟨"some",    "DET", [], []⟩,
  ⟨"several", "DET", [.pl], []⟩,
  ⟨"a",       "DET", [.sg], []⟩,
  ⟨"no",      "DET", [], []⟩,
  ⟨"the",     "DET", [], []⟩,
  ⟨"most",    "DET", [.pl], []⟩,
  ⟨"many",    "DET", [.pl], []⟩,
  ⟨"few",     "DET", [.pl], []⟩,
  ⟨"this",    "DET", [.sg], []⟩,
  ⟨"these",   "DET", [.pl], []⟩,
  ⟨"those",   "DET", [.pl], []⟩,
  -- determiner functions
  ⟨"less_than", "DF", [.pl], []⟩,
  ⟨"more_than", "DF", [.pl], []⟩ ]

-- Os substantivos comuns recebem o rótulo `CN`. Para cada um, registramos uma
-- forma singular e uma forma plural, com o mesmo gênero e a terceira pessoa.
-- A função `noun` recebe as duas formas e o gênero e produz as duas entradas.

-- As formas são fornecidas explicitamente, de modo que podemos usar a mesma
-- função para pares como `boy` e `boys` ou `man` e `men`. Quando há mais de
-- uma forma para o plural, regular e irregular, acrescentamos uma entrada à
-- lista. É o caso de `dwarves`, que aparece junto com o plural `dwarfs`.

def noun (sg pl : String) (g : Feat) : List Cat :=
  [⟨sg, "CN", [.sg, g, .thrd], []⟩, ⟨pl, "CN", [.pl, g, .thrd], []⟩]

def commonNouns : List Cat :=
  noun "thing" "things" .neutr ++
  noun "person" "persons" .masc ++
  noun "boy" "boys" .masc ++
  noun "man" "men" .masc ++
  noun "girl" "girls" .fem ++
  noun "woman" "women" .fem ++
  noun "princess" "princesses" .fem ++
  noun "dwarf" "dwarfs" .masc ++
  [⟨"dwarves", "CN", [.pl, .masc, .thrd], []⟩] ++
  noun "giant" "giants" .masc ++
  noun "wizard" "wizards" .masc ++
  noun "sword" "swords" .neutr ++
  noun "dagger" "daggers" .neutr

#eval noun "boy" "boys" .masc

-- Os auxiliares do nosso fragmento são `did` e `didn't`, ambos com rótulo
-- `AUX`. Para os demais verbos, registramos a forma do passado, com
-- `Feat.tense`, e a forma infinitiva, com `Feat.infl`. O infinitivo é a forma
-- sem marca de tempo ou pessoa que encontramos em `smile` e `love`. É também
-- a forma usada depois do auxiliar, como em `didn't smile`. A função `verb`
-- produz as duas entradas com a mesma lista de subcategorização.

-- Um verbo intransitivo, como `smiled`, tem essa lista vazia. Um transitivo,
-- como `loved`, pede um objeto `NP` com caso `Feat.accOrDat`. A categoria
-- `objNP` representa essa exigência. Para complementos preposicionais,
-- `objPP f` representa um `PP` com o traço de preposição `f`.

-- Um mesmo verbo pode admitir diferentes listas de complementos. A forma
-- `gave` tem uma entrada que pede um `NP` seguido de um `PP` com `Feat.to` e
-- outra que pede dois `NP`. As entradas de `sold` seguem os mesmos padrões.

-- Também representamos complementos opcionais com entradas distintas. Uma
-- entrada de `kicked` pede um `NP` e um `PP` com `Feat.with`, enquanto a
-- outra pede apenas o `NP`. Para `took`, o complemento opcional é um `PP` com
-- `Feat.from`. Cada um desses padrões vale tanto para a forma do passado
-- quanto para a infinitiva.

def auxiliaries : List Cat := [
  ⟨"did",    "AUX", [], []⟩,
  ⟨"didn't", "AUX", [], []⟩ ]

def verb (past inf : String) (subcat : List Cat) : List Cat :=
  [⟨past, "VP", [.tense], subcat⟩, ⟨inf, "VP", [.infl], subcat⟩]

def objNP : Cat := ⟨"_", "NP", [.accOrDat], []⟩
def objPP (f : Feat) : Cat := ⟨"_", "PP", [f], []⟩

def verbs : List Cat :=
  -- intransitive
  verb "smiled" "smile" [] ++
  verb "laughed" "laugh" [] ++
  verb "cheered" "cheer" [] ++
  verb "shuddered" "shudder" [] ++
  -- transitive
  verb "loved" "love" [objNP] ++
  verb "admired" "admire" [objNP] ++
  verb "helped" "help" [objNP] ++
  verb "defeated" "defeat" [objNP] ++
  -- ditransitive
  verb "gave" "give" [objNP, objPP .to] ++
  verb "gave" "give" [objNP, objNP] ++
  verb "sold" "sell" [objNP, objPP .to] ++
  verb "sold" "sell" [objNP, objNP] ++
  -- an NP and an optional with-PP
  verb "kicked" "kick" [objNP, objPP .with] ++
  verb "kicked" "kick" [objNP] ++
  -- an NP and an optional from-PP
  verb "took" "take" [objNP, objPP .from] ++
  verb "took" "take" [objNP]

#eval verb "loved" "love" [objNP]

-- Cada preposição tem o rótulo `PREP` e um traço que identifica qual
-- preposição ela é. Esse traço será transmitido ao `PP`. Assim, uma exigência
-- de complemento como a de `gave` pode selecionar um `PP` com `Feat.to`. Um
-- complemento com `Feat.with` entra em conflito com essa exigência.

-- Registramos também as palavras que conectam orações. A palavra `and` recebe
-- o rótulo `CONJ`, e as palavras `if` e `then` recebem os rótulos `COND` e
-- `THEN`. Essas palavras ligam orações dentro de uma mesma sentença: *Alice
-- smiled and Dorothy laughed* é uma única sentença, com duas orações. O
-- parser da seção Análise Sintática com Categorias, porém, só tem a regra
-- `S → NP VP` e não aceita orações coordenadas nem condicionais. As entradas
-- com os rótulos `CONJ`, `COND`, `THEN` e `REL` serão usadas por regras que
-- acrescentaremos depois.

-- A função `lexicon` reúne as listas de entradas e filtra aquelas cuja forma
-- coincide com a palavra consultada. A consulta de `that` devolve suas duas
-- categorias, e a de `gave` devolve seus dois padrões de subcategorização. Se
-- a palavra não estiver nas listas, como `unicorn`, o resultado será a lista
-- vazia.

def prepositions : List Cat := [
  ⟨"on",   "PREP", [.on], []⟩,
  ⟨"with", "PREP", [.with], []⟩,
  ⟨"by",   "PREP", [.by], []⟩,
  ⟨"to",   "PREP", [.to], []⟩,
  ⟨"from", "PREP", [.from], []⟩ ]

def connectives : List Cat := [
  ⟨"and",  "CONJ", [], []⟩,
  ⟨"if",   "COND", [], []⟩,
  ⟨"then", "THEN", [], []⟩ ]

def lexicon (w : String) : List Cat :=
  (pronouns ++ properNames ++ determiners ++ commonNouns ++
    auxiliaries ++ verbs ++ prepositions ++ connectives).filter
    (·.phon == w)

#eval lexicon "that"
#eval lexicon "gave"
#eval lexicon "unicorn"

-- Antes de consultar o léxico, precisamos transformar o texto de entrada em
-- uma lista de palavras. A função `scan` percorre os caracteres com
-- `scanChars` e insere um espaço apenas antes de cada ponto, vírgula ou
-- interrogação. Assim, em `smiled,`, a vírgula pode ser separada da palavra
-- que a precede quando o texto é dividido nos espaços.

-- O tipo `Words` abrevia uma lista de textos. A função `lexer` aplica `scan`,
-- converte o resultado para minúsculas e o divide nos espaços. Em seguida,
-- remove os textos vazios que essa divisão pode produzir e aplica `preproc` à
-- lista obtida.

-- Esperamos que a entrada de `lexer` seja uma única sentença, já que a nossa
-- gramática analisa uma sentença de cada vez, e não um texto. A divisão de um
-- texto em sentenças caberia a uma função de segmentação, aplicada antes, que
-- não definimos aqui. Uma entrada com mais de uma sentença, como
-- `Alice smiled. Dorothy laughed.`, está fora do que as funções desta seção
-- esperam.

-- O pré-processamento elimina as vírgulas e remove o ponto ou a interrogação
-- que estiver no fim da lista. Numa só sentença, esse é o único ponto, e por
-- isso o ponto final não tem entrada no léxico.

-- A função `preproc` também ajusta a divisão de certas expressões às entradas
-- do léxico. A sequência `did not` vira `didn't`, e `nobody` vira duas
-- palavras, `no` e `person`. De modo semelhante, `everybody` vira
-- `every person`. No sentido inverso, `less than` e `more than` são reunidas
-- nas formas `less_than` e `more_than`. As expressões `at least` e `at most`
-- também são reunidas, embora as formas `at_least` e `at_most` ainda não
-- tenham entradas em `lexicon`.

-- Por exemplo, o processamento de `Did not everybody smile?` produz a lista
-- `["didn't", "every", "person", "smile"]`.

def scanChars : List Char → List Char
  | [] => []
  | x :: xs =>
    if x ∈ ['.', ',', '?'] then ' ' :: x :: scanChars xs
    else x :: scanChars xs

def scan (s : String) : String :=
  String.ofList (scanChars s.toList)

abbrev Words := List String

def preproc : Words → Words
  | [] => []
  | ["."] => []
  | ["?"] => []
  | "," :: xs => preproc xs
  | "did" :: "not" :: xs => "didn't" :: preproc xs
  | "nothing" :: xs => "no" :: "thing" :: preproc xs
  | "nobody" :: xs => "no" :: "person" :: preproc xs
  | "something" :: xs => "some" :: "thing" :: preproc xs
  | "somebody" :: xs => "some" :: "person" :: preproc xs
  | "everything" :: xs => "every" :: "thing" :: preproc xs
  | "everybody" :: xs => "every" :: "person" :: preproc xs
  | "less" :: "than" :: xs => "less_than" :: preproc xs
  | "more" :: "than" :: xs => "more_than" :: preproc xs
  | "at" :: "least" :: xs => "at_least" :: preproc xs
  | "at" :: "most" :: xs => "at_most" :: preproc xs
  | x :: xs => x :: preproc xs

def lexer (s : String) : Words :=
  preproc (((scan s).toLower.splitOn " ").filter (· ≠ ""))

#eval scan "Alice smiled, and Dorothy laughed."
#eval lexer "Alice smiled, and Dorothy laughed."
#eval lexer "Did not everybody smile?"

-- Uma consulta ao léxico tem tipo `String → List Cat`. A função
-- `lookupWord db w` consulta a palavra `w` no léxico `db`. Para preparar uma
-- entrada inteira para o parser, precisamos consultar todas as palavras e
-- reunir suas possíveis categorias.

-- A função `collectCats` associa cada palavra à lista de categorias devolvida
-- pela consulta. Se alguma dessas listas for vazia, a palavra é desconhecida.
-- Nesse caso, a função devolve um erro que contém as palavras desconhecidas
-- da entrada.

-- Para representar os dois resultados possíveis, usamos o tipo `Except`. Em
-- `Except ε α`, `ε` é o tipo do erro e `α` é o tipo do valor produzido em
-- caso de sucesso. O construtor `Except.ok` guarda esse valor, e
-- `Except.error` guarda o erro. Aqui, usamos `String` para o erro e
-- `List (List Cat)` para o resultado.

-- Quando todas as palavras são conhecidas, `initCats` escolhe uma categoria
-- de cada lista, conservando a ordem das palavras. Ela enumera todas as
-- combinações possíveis. Para a lista vazia de palavras, há uma escolha, que
-- também é vazia. Para uma lista não vazia, a função antepõe cada categoria
-- da primeira palavra a cada escolha feita para as demais.

-- Na entrada `Alice admired that girl.`, a palavra `that` dá origem a duas
-- escolhas de categorias. O parser poderá testar cada uma para determinar se
-- ela permite uma análise da sentença. Já a entrada com `unicorn` produz um
-- erro durante a consulta.

def lookupWord (db : String → List Cat) (w : String) : List Cat :=
  db w

def initCats : List (List Cat) → List (List Cat)
  | [] => [[]]
  | cs :: rests => cs.flatMap fun c => (initCats rests).map (c :: ·)

def collectCats (db : String → List Cat) (words : Words) :
    Except String (List (List Cat)) :=
  let listing := words.map fun x => (x, lookupWord db x)
  let unknown := (listing.filter (·.2.isEmpty)).map (·.1)
  if unknown ≠ [] then .error s!"unknown words: {unknown}"
  else .ok (initCats (listing.map (·.2)))

#eval collectCats lexicon (lexer "Alice admired that girl.")
#eval collectCats lexicon (lexer "Alice admired the unicorn.")

-- ### Exercise (2 stars): init-cats-length ⭐⭐

-- Prove que o número de escolhas devolvidas por `initCats` é o produto do
-- número de categorias de cada palavra.

theorem length_initCats (css : List (List Cat)) :
    (initCats css).length = (css.map List.length).prod := by
  sorry

end Parsing

