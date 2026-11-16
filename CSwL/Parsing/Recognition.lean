import CSwL.Parsing.ParseTrees
import Mathlib.Data.List.Palindrome
import CSwLCompat

-- # Reconhecendo e Analisando Linguagens Livres de Contexto

namespace Parsing

-- Uma gramática pode gerar palavras sobre um alfabeto de caracteres ou frases
-- sobre um alfabeto de palavras ou tokens. Dada uma sequência, podemos usar a
-- gramática para responder a duas perguntas.

-- Chamamos de **reconhecimento** o procedimento que responde se a sequência
-- pertence à linguagem gerada pela gramática. Na **análise**, ou **parsing**,
-- a resposta consiste nas árvores sintáticas que representam as derivações da
-- sequência.

-- Vamos usar como exemplo a gramática abaixo, que gera os palíndromos sobre
-- `{a, b, c}`. Um palíndromo é uma palavra igual à que obtemos ao invertê-la.

-- Uma regra de uma gramática livre de contexto tem um único não terminal à
-- esquerda. Para testar uma regra com `n` símbolos à direita, dividimos a
-- entrada em `n` pedaços consecutivos, de todos os modos possíveis. Para cada
-- divisão, testamos se cada símbolo gera o pedaço que lhe corresponde.

-- A função `split2` enumera as divisões em dois pedaços. Para a lista vazia,
-- ela produz uma só divisão, com dois pedaços vazios. Para uma lista não
-- vazia, a primeira divisão é o pedaço vazio seguido da lista inteira. As
-- demais divisões são obtidas dividindo a cauda e recolocando o primeiro
-- elemento no primeiro pedaço. O exemplo usa `"Jan".toList` para obter os
-- caracteres e `String.ofList` para exibir os pedaços como textos.

-- A função `splitN n` generaliza esse procedimento. Em zero pedaços, só a
-- lista vazia pode ser dividida, e há uma única divisão. Para dois ou mais
-- pedaços, a função usa `split2` para separar o primeiro e divide
-- recursivamente o restante.

-- A ::= ε | "a" | "b" | "c" | "a" A "a" | "b" A "b" | "c" A "c" ;

def split2 {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
    ([], x :: xs) ::
      (split2 xs).map fun (ys, zs) => (x :: ys, zs)

#eval split2 "Jan".toList |>.map
  λ (a, b) ↦ (String.ofList a, String.ofList b)

def splitN {α : Type} : Nat → List α → List (List (List α))
  | 0, [] => [[]]
  | 0, a :: as => []
  | 1, xs => [[xs]]
  | n + 2, xs =>
    (split2 xs).flatMap fun (ys, zs) =>
      (splitN (n + 1) zs).map fun rs => ys :: rs

#eval splitN 3 "Jan".toList |>.map
   λ xs => xs.map String.ofList

-- O reconhecedor aceita diretamente as palavras geradas pelas regras `A → ε`,
-- `A → a`, `A → b` e `A → c`. Para testar `A → a A a`, ele procura, entre as
-- divisões de `splitN 3 xs`, uma que tenha `['a']` nas duas pontas. Se
-- encontrar uma divisão assim, testa recursivamente se o pedaço do meio é um
-- palíndromo. As regras `A → b A b` e `A → c A c` seguem o mesmo
-- procedimento.

-- Na primeira tentativa, `recognize₀`, o padrão `[['a'], ys, ['a']]`
-- identifica o pedaço central, mas não carrega a informação de que a divisão
-- veio de `splitN 3 xs`. O Lean precisa dessa informação para verificar que a
-- chamada sobre `ys` termina. A definição de `recognize` usa `List.attach`
-- para associar cada divisão a uma prova de que ela pertence à lista de
-- divisões.

-- A cláusula `termination_by xs.length` indica que a medida usada para
-- justificar a recursão é o comprimento da entrada. A cláusula
-- `decreasing_by` fornece a prova de que a medida diminui em cada chamada. O
-- lema `flatten_of_mem_splitN`, no bloco de detalhes, mostra que concatenar
-- os pedaços recupera a entrada. Aplicamos `List.length` à igualdade com
-- `congrArg`. Como os dois pedaços externos têm um elemento cada, o pedaço
-- central tem dois elementos a menos do que a entrada.

-- O mesmo raciocínio explica quando o método funciona para uma regra
-- recursiva à esquerda, como `V → V T`. Se o pedaço de `T` tiver ao menos um
-- símbolo, o pedaço de `V` é menor que a entrada. Se o pedaço de `T` for
-- vazio, uma chamada para `V` sobre o primeiro pedaço receberá a entrada
-- inteira. Podemos descartar essa divisão quando `T` não gera a palavra
-- vazia. Em uma gramática que permite essa derivação, descartá-la sem outro
-- tratamento pode perder análises.

-- THE FOLLOWING DETAILS CAN BE SKIPPED (As divisões juntam-se de volta na entrada)
theorem append_of_mem_split2 {α : Type} :
    ∀ {xs : List α} {p : List α × List α},
      p ∈ split2 xs → p.1 ++ p.2 = xs
  | [], p, h => by
    simp [split2] at h
    simp [h]
  | x :: xs, p, h => by
    simp only [split2, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨ys, zs⟩, h, rfl⟩
    · rfl
    · simp [← append_of_mem_split2 h]

theorem flatten_of_mem_splitN {α : Type} :
    ∀ {n : Nat} {xs : List α} {l : List (List α)},
      l ∈ splitN n xs → l.flatten = xs
  | 0, [], l, h | 1, _, l, h => by
    simp [splitN] at h
    simp [h]
  | 0, _ :: _, _, h => by simp [splitN] at h
  | n + 2, xs, l, h => by
    simp only [splitN, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨ys, zs⟩, h1, rs, h2, rfl⟩ := h
    simp [flatten_of_mem_splitN h2, append_of_mem_split2 h1]
-- END DETAILS

sf_expect_failure
  def recognize₀ (xs : List Char) : Bool :=
    xs == [] || xs == ['a'] || xs == ['b'] || xs == ['c'] ||
    (splitN 3 xs).any fun
      | [['a'], ys, ['a']] => recognize₀ ys
      | [['b'], ys, ['b']] => recognize₀ ys
      | [['c'], ys, ['c']] => recognize₀ ys
      | _ => false

def recognize (xs : List Char) : Bool :=
  xs == [] || xs == ['a'] || xs == ['b'] || xs == ['c'] ||
  (splitN 3 xs).attach.any fun
    | ⟨[['a'], ys, ['a']], h⟩ => recognize ys
    | ⟨[['b'], ys, ['b']], h⟩ => recognize ys
    | ⟨[['c'], ys, ['c']], h⟩ => recognize ys
    | _ => false
termination_by xs.length
decreasing_by
  all_goals
    have := congrArg List.length (flatten_of_mem_splitN h)
    simp at this
    omega

#eval recognize "aabcbbcbaa".toList
#eval recognize "aabcbbcba".toList

-- Podemos usar `recognize` para gerar palavras da linguagem. Primeiro
-- enumeramos as palavras sobre um alfabeto dado e depois conservamos apenas
-- as que o reconhecedor aceita.

-- A função `generate n alphabet` enumera as palavras de comprimento `n`. A
-- única palavra de comprimento zero é a lista vazia. Para obter palavras de
-- comprimento `n + 1`, a função antepõe cada símbolo do alfabeto a cada
-- palavra de comprimento `n`. Como há palíndromos de comprimento arbitrário,
-- fixamos um limite para que a enumeração caiba em uma lista finita. A função
-- `generateUpTo n alphabet` reúne as palavras dos comprimentos de zero a `n`.
-- A função `language` filtra essa lista com `recognize`.

def generate {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | n + 1, alphabet =>
    alphabet.flatMap fun x =>
      (generate n alphabet).map (x :: ·)

def generateUpTo {α : Type} (n : Nat) (alphabet : List α) :
    List (List α) :=
  (List.range (n + 1)).flatMap fun k => generate k alphabet

def language (n : Nat) (alphabet : List Char)
  : List (List Char) :=
  (generateUpTo n alphabet).filter recognize

#eval language 3 "abc".toList |>.map
  String.ofList

-- O Mathlib representa a propriedade de ser palíndromo pelo predicado
-- indutivo `List.Palindrome`. A lista vazia e as listas de um elemento são
-- palíndromos. Se `l` é um palíndromo, acrescentar o mesmo elemento `x` às
-- duas pontas produz outro, `x :: (l ++ [x])`. Esses casos correspondem às
-- regras da nossa gramática, com a diferença de que o predicado permite
-- qualquer elemento nas pontas.

-- O teorema `recognize_iff_palindrome` diz que `recognize` concorda com esse
-- predicado para toda palavra `w` sobre `{a, b, c}`. Para listas,
-- `w ⊆ "abc".toList` significa que cada elemento de `w` pertence a
-- `"abc".toList`. Essa hipótese é necessária para garantir que todo
-- palíndromo seja aceito. Por exemplo, `xx` é um palíndromo, mas contém um
-- símbolo fora do alfabeto do reconhecedor.

-- A prova trata uma direção de cada vez, por indução em um limite para o
-- comprimento da palavra. Na primeira direção, cada sucesso do reconhecedor
-- corresponde a um dos casos de `List.Palindrome`. Na segunda, a forma do
-- palíndromo determina uma divisão que o reconhecedor precisa testar. As
-- equações de `recognize` podem ser usadas nas duas provas porque sua
-- terminação foi demonstrada.

-- THE FOLLOWING DETAILS CAN BE SKIPPED (O reconhecedor e a definição de palíndromo)
theorem mem_split2_append {α : Type} :
    ∀ ys zs : List α, (ys, zs) ∈ split2 (ys ++ zs)
  | [], [] => by simp [split2]
  | [], z :: zs => by simp [split2]
  | y :: ys, zs => by
    simp only [List.cons_append, split2, List.mem_cons,
      List.mem_map]
    exact Or.inr ⟨(ys, zs), mem_split2_append ys zs, rfl⟩

theorem mem_splitN_flatten {α : Type} :
    ∀ l : List (List α), l ∈ splitN l.length l.flatten
  | [] => by simp [splitN]
  | [ys] => by simp [splitN]
  | ys :: zs :: rs => by
    simp only [List.length_cons, List.flatten_cons]
    simp only [splitN, List.mem_flatMap, List.mem_map]
    refine ⟨(ys, (zs :: rs).flatten),
      by simpa using mem_split2_append ys _,
      zs :: rs, ?_, rfl⟩
    simpa using mem_splitN_flatten (zs :: rs)

theorem recognize_sound (n : Nat) :
    ∀ w : List Char, w.length ≤ n →
      recognize w → w.Palindrome := by
  induction n with
  | zero =>
    intro w hw hr
    simp at hw
    rw [hw]
    exact .nil
  | succ n ih =>
    intro w hw h
    rw [recognize] at h
    simp only [Bool.or_eq_true, beq_iff_eq,
      List.any_eq_true] at h
    rcases h with (((rfl | rfl) | rfl) | rfl)
      | ⟨⟨l, hl⟩, _, hm⟩
    · exact .nil
    · exact .singleton _
    · exact .singleton _
    · exact .singleton _
    · split at hm <;> (try contradiction) <;>
      · rename_i ys hys _
        have he := flatten_of_mem_splitN hys
        simp at he
        subst he
        apply List.Palindrome.cons_concat
        exact ih ys (by simp at hw; omega) hm

theorem recognize_complete (n : Nat) :
    ∀ w : List Char, w.length ≤ n → w ⊆ "abc".toList →
      w.Palindrome → recognize w = true := by
  induction n with
  | zero =>
    intro w hw _ _
    simp at hw
    subst hw
    rw [recognize]
    simp
  | succ n ih =>
    intro w hw ha hp
    cases hp with
    | nil =>
      rw [recognize]
      simp
    | singleton x =>
      have hx : x ∈ "abc".toList := ha (by simp)
      simp at hx
      rcases hx with rfl | rfl | rfl <;>
        (rw [recognize]; simp)
    | cons_concat x hl =>
      rename_i l
      have hx : x ∈ "abc".toList := ha (by simp)
      have hl' : l ⊆ "abc".toList :=
        fun c hc => ha (by simp [hc])
      have ih' := ih l (by simp at hw; omega) hl' hl
      rw [recognize]
      simp only [Bool.or_eq_true, beq_iff_eq,
        List.any_eq_true]
      right
      have hmem :
          [[x], l, [x]] ∈ splitN 3 (x :: (l ++ [x])) := by
        simpa using mem_splitN_flatten [[x], l, [x]]
      refine ⟨⟨_, hmem⟩, List.mem_attach _ _, ?_⟩
      simp at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ih'

theorem recognize_iff_palindrome (w : List Char)
    (hw : w ⊆ "abc".toList) :
    recognize w ↔ w.Palindrome :=
  ⟨recognize_sound _ w (Nat.le_refl _),
   recognize_complete _ w (Nat.le_refl _) hw⟩
-- END DETAILS

-- Para construir as árvores que a gramática atribui a uma palavra, seguimos
-- as mesmas regras usadas no reconhecimento. A entrada continua sendo uma
-- lista de caracteres. A análise devolve uma lista de árvores de tipo
-- `ParseTree Char Char`, com caracteres nas folhas e o rótulo `'A'` nos nós
-- internos.

-- Cada uso de uma regra produz um nó. A regra `A → ε` produz um nó sem
-- filhas, e uma regra como `A → a` produz um nó com uma folha. Para
-- `A → a A a`, percorremos as divisões com `['a']` nas duas pontas. Para cada
-- árvore obtida ao analisar o pedaço central, construímos uma árvore com essa
-- subárvore entre duas folhas com o caractere `a`. A justificativa de que a
-- chamada recursiva recebe uma palavra menor é a mesma usada para
-- `recognize`.

-- O reconhecedor pode parar assim que uma regra der certo. Para analisar a
-- palavra, reunimos com `++` os resultados das regras e usamos `List.flatMap`
-- para reunir os resultados das divisões. Se a palavra não pertence à
-- linguagem, a lista de árvores é vazia. Se a gramática atribui mais de uma
-- árvore à palavra, a lista contém todas elas.

def parse (xs : List Char) : List (ParseTree Char Char) :=
  (if xs == [] then [.branch 'A' []] else []) ++
  (if xs == ['a'] then [.branch 'A' [.leaf 'a']] else []) ++
  (if xs == ['b'] then [.branch 'A' [.leaf 'b']] else []) ++
  (if xs == ['c'] then [.branch 'A' [.leaf 'c']] else []) ++
  (splitN 3 xs).attach.flatMap fun
    | ⟨[['a'], ys, ['a']], h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'a', t, .leaf 'a']
    | ⟨[['b'], ys, ['b']], h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'b', t, .leaf 'b']
    | ⟨[['c'], ys, ['c']], h⟩ =>
      (parse ys).map fun t =>
        .branch 'A' [.leaf 'c', t, .leaf 'c']
    | _ => []
termination_by xs.length
decreasing_by
  all_goals
    have := congrArg List.length (flatten_of_mem_splitN h)
    simp at this
    omega

#eval IO.println (parse "".toList)
#eval IO.println (parse "aab".toList)
#eval IO.println (parse "aabaa".toList)

-- THE FOLLOWING DETAILS CAN BE SKIPPED (Árvores mais enxutas)
-- Como a gramática tem um só não terminal, poderíamos omitir o nó `A` na
-- regra `A → a` e devolver só a folha `a`. Nenhuma informação se perderia,
-- porque o único rótulo possível é `A`. Mas a árvore deixaria de ter um nó
-- para cada regra usada, e a correspondência entre a gramática e o parser
-- ficaria menos direta. Na regra `A → ε` nem há essa opção pois uma árvore é
-- uma folha ou um nó, sem o nó `A`, não sobra nada para devolver. Por isso
-- mantemos um nó para cada regra.
-- END DETAILS

-- ### Exercise (2 stars): split-nonempty ⭐⭐

-- Numa gramática sem regras com `ε`, nenhum pedaço da divisão pode ser vazio.
-- Defina `split2'` e `splitN'`, que dão só as divisões sem pedaços vazios.
-- Confira o resultado em `"Jan"`.

def split2' {α : Type} : List α → List (List α × List α)
  | [] | [_] => []
  | x :: y :: ys =>
    sorry

def splitN' {α : Type} : Nat → List α → List (List (List α))
  | 0, [] => [[]]
  | 0, _ :: _ => []
  | 1, [] => []
  | 1, xs => [[xs]]
  | n + 2, xs =>
    sorry

theorem split2'_jan :
    split2' "Jan".toList =
      [(['J'], ['a', 'n']), (['J', 'a'], ['n'])] := by
  sorry

theorem splitN'_jan :
    splitN' 3 "Jan".toList = [[['J'], ['a'], ['n']]] := by
  sorry

end Parsing

