import CSwLCompat
import Mathlib.Data.List.Chain

-- # Gramáticas para jogos

-- O capítulo trata de como definir uma língua — no sentido amplo: um conjunto
-- de strings bem formadas — por meio de uma gramática. Os dois exemplos são
-- de linguagens sobre jogos.

-- ## Batalha Naval

-- ### Sintaxe

-- Batalha naval é um jogo de tabuleiro de dois jogadores, no qual os
-- jogadores têm de adivinhar em que quadrados estão os navios do oponente. O
-- jogo pode ser jogado com uma comunicação bastante limitada entre os
-- jogadores.

-- Cada jogador tem dois tabuleiros, `10 × 10`. Usualmente, as colunas são
-- identificadas por `A..J` e as linhas `0..9`. Um tabuleiro representa a
-- disposição dos navios do jogador e onde ele irá registrar os 'tiros' do seu
-- oponente, o outro representa a tabuleiro do seu oponente, onde ele marca os
-- 'tiros' que realizou, que podem acertar ou erras parte dos navios do
-- oponente. O objetivo de cada jogador é revelar o tabuleiro do oponente,
-- afundando todos os navios a frota adversária.

-- Modelar o jogo como uma linguagem `L` significa determinarmos quais são as
-- sentenças válidas de nossa linguagem. Como o jogo é jogado em turnos, cada
-- participante faz um ataque, marca a reação do oponente e depois recebe um
-- ataque, indicando a consequência. Desta forma, a sentença `A 10` representa
-- um ataque na posição `A × 10` do tabuleiro adversário. A sentença
-- `hit frigate` representa uma reação a um tiro indicando ele ter atingido
-- parte de uma fragata. A gramática a seguir captura esta idéia.

-- column   ::= "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" ;
-- row      ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
-- attack   ::= column row ;
-- ship     ::= "battleship" | "frigate" | "submarine" | "destroyer" ;
-- reaction ::= "missed" | "hit" ship | "sunk" ship | "defeated" ;
-- turn     ::= attack reaction ;

-- A notação `::=` acima é BNF (*Backus-Naur Form*). Cada regra associa um
-- não-terminal (à esquerda) a uma ou mais alternativas (à direita, separadas
-- por `|`), cada alternativa uma sequência de símbolos. A gramática é o
-- conjunto de regras que, quando aplicadas sucessivamente, geram todas as
-- sentenças da linguagem. Se repetirmos a aplicação das regras acima para
-- reescrever não terminais a partir de `turn` até só restarem terminais,
-- obtém-se uma jogada válida, como `B 2 missed`. Se começarmos a partir do
-- símbolo `turn` (chamado *símbolo inicial*), teremos uma jogada completa
-- `B 2 missed` ou `A 0 hit frigate`.

-- Chamamos cada passo de reescrita de `⇒` e nele temos os vários estados
-- intermediários para geração de uma sentença válida:

-- turn ⇒ attack reaction ⇒ attack missed ⇒ ... ⇒ B 2 missed

-- A repetição de passos é o feixo transitivo e reflexivo que representamos
-- por `⇒*`:

-- turn ⇒* B 2 missed

-- A imlementação desta gramática em Lean é mostrada a seguir. Para cada não
-- terminal, temos um tipo. Não terminais com mais de um regra de derivação,
-- correspondem a tipos indutivos. Os terminais são os construtores. Para os
-- não terminais com apenas uma derivação, como o `attack`, usamos uma
-- `structure`.

namespace Battleship

inductive Column where
  | A | B | C | D | E | F | G | H | I | J
  deriving DecidableEq, Repr

inductive Ship where
  | battleship | frigate | submarine | destroyer
  deriving DecidableEq, Repr

structure Attack where
  column : Column
  row : Fin 10
  deriving DecidableEq, Repr

inductive Reaction where
  | missed
  | hit (s : Ship)
  | sunk (s : Ship)
  | defeated
  deriving DecidableEq, Repr

structure Turn where
  attack : Attack
  reaction : Reaction
  deriving DecidableEq, Repr

-- Um `Attack` basicamente corresponde a uma coordenada, as colunas poderiam
-- ter sido modeladas como as linhas, o que tornaria o design mais simples.
-- Mas preferimos seguir o estilo de coordenadas usual, que facilita a leitura
-- e associação de letras a colunas e números para linhas.

-- O tipo `Fin 10` corresponde os números naturais menores que 10. O termo
-- `(10 : Fin 10)` corresponde ao `0` (`10 % 10`, via `OfNat`), mas isso só
-- vale para o literal `10` interpretado nesse tipo. A instância
-- `OfNat (Fin 10) 10` (usada ao escrever `10 : Fin 10`) normaliza o literal
-- por `% 10` antes de guardá-lo. O construtor `⟨n, prova⟩` (`Fin.mk`) exige
-- uma prova de `n < 10` como dado — para `n = 10` essa prova não existe
-- (`10 < 10` é falso), então `⟨10, by omega⟩` sequer elabora. Ou seja,
-- `(10 : Fin 10)` sempre existe via módulo, e `(⟨10, _⟩ : Fin 10)` só existe
-- para `n` de fato menor que `10`.

#eval (10 : Fin 10)
#eval (11 : Fin 10)

example : (11 : Fin 10) = 1 := rfl
example : ⟨0, by omega⟩ = (0 : Fin 10) := rfl

-- Se `Column` também fosse um `Fin 10` então poderíamos modelar com um par
-- `Attack : Fin 10 × Fin 10`.

-- Uma possível extensão de nossa gramática seria representar como sentença um
-- jogo completo entre dois jogadores.

-- game ::= turn | turn game ;

-- Se agora tomarmos `game` como símbolo inicial, as sentenças que geramos são
-- sequências de jogadas como no exemplo abaixo. Vejam que os parênteses só
-- foram introduzidos para explicitar a estrutura sintática.

-- game ⇒* (A 0 missed) (B 3 (hit battleship)) (B 4 (sunk battleship))

-- Considerando esta nova gramática. Como a regra de `game` é recursiva, a
-- gramática permite gerar sequências de turnos indefinitivamente. O
-- não-terminal `turn` é sempre expandido de forma independente. Portanto,
-- sintaticamente, nada impede que a gramática gere uma sequência de turnos
-- onde um jogador é derrotado e o jogo continua depois disso.

-- game ⇒* turn turn ⇒* (A 1 defeated) (B 2 missed)

-- Uma forma conveniente de formalizar em Lean esta extensão é usar o tipo
-- `List` para obter naturalmente uma sequencia de `Turn` de qualquer
-- comprimento.

abbrev Game := List Turn

def game1 : Game :=
  [⟨⟨.B, 2⟩, .missed⟩,
   ⟨⟨.B, 3⟩, .hit .battleship⟩,
   ⟨⟨.B, 4⟩, .sunk .battleship⟩
  ]

-- Note que `game1` não representa um jogo completo e a expressão `B 2 missed`
-- pode ou não ser verdade para um determinado tabuleiro. Ou seja, só temos a
-- *sintaxe*, não temos a *semântica* do jogo. Exigir que o jogo termine
-- quando um dos jogadores é derrotado é também uma questão semântica. Uma
-- regra para "não atacar duas vezes a mesma posição" vai para além da sintaxe
-- ou semântica, refere-se a pragmática, ou como ele deve ser jogado.

-- ### Exercise (2 stars): game-over-grammar ⭐⭐

-- Revise a gramática de modo que fique explícito, nas regras da gramática,
-- que o jogo termina assim que um dos jogadores é derrotado.

-- A gramática revisada do exercício anterior separa um `turn` comum (que
-- nunca termina o jogo) de um `surrender` (que só ocorre no fim), usando para
-- isso duas categorias sintáticas distintas — `reaction`, que perde a
-- alternativa `"defeated"`, e um `surrender` novo. Nosso `Game` em Lean não
-- faz essa separação: `Turn` continua com o `Reaction` original, de quatro
-- construtores, e `Game` continua sendo `List Turn` sem distinguir o último
-- turno dos demais. Uma tradução fiel da gramática revisada exigiria dois
-- tipos — um para `turn` e outro para `surrender` — e tornaria a propriedade
-- abaixo verdadeira por construção, sem conteúdo de prova.

-- Preferimos manter `Game` como está e formalizar a propriedade que a
-- gramática revisada garante sintaticamente como um predicado sobre essa
-- representação existente: uma sequência de turnos é bem-formada quando
-- `defeated` — se aparecer — só aparece no último turno.

inductive WellFormed : Game → Prop where
  | last (t : Turn) : t.reaction = .defeated → WellFormed [t]
  | step (t : Turn) (g : Game) :
      t.reaction ≠ .defeated → WellFormed g → WellFormed (t :: g)

-- O construtor `step` só permite estender uma sequência bem-formada com um
-- turno cuja reação não seja `defeated` — é essa condição que faz o
-- predicado, e não o tipo `Game`, carregar a restrição que a gramática
-- revisada impõe estruturalmente.

-- ### Exercise (3 stars): defeated-last ⭐⭐⭐

-- Prove que toda `Game` bem-formada não é vazia, e que ela sempre termina com
-- uma reação `.defeated`, não importa o comprimento da sequência.

theorem WellFormed.ne_nil {g : Game} (h : WellFormed g) : g ≠ [] :=
  sorry

theorem WellFormed.defeated_last {g : Game} (h : WellFormed g) :
    ∃ init t, g = init ++ [t] ∧ t.reaction = .defeated :=
  sorry

-- Os dois exemplos de derivação já vistos são testemunhas de que a condição
-- extra de `WellFormed` é mesmo necessária: `game1` (linha 113) não é
-- bem-formado, ele termina em `.sunk`. O jogo `(A 1 defeated) (B 2 missed)`
-- também não é bem-formado, pois a derrota aparece antes do fim.

example : ¬ WellFormed game1 := by
  intro h
  cases h with
  | step t g hne hwf =>
    cases hwf with
    | step t' g' hne' hwf' =>
      cases hwf' with
      | last t'' ht'' => simp at ht''
      | step t'' g'' hne'' hwf'' => cases hwf''

def badDerivation : Game :=
  [⟨⟨.A, 1⟩, .defeated⟩, ⟨⟨.B, 2⟩, .missed⟩]

example : ¬ WellFormed badDerivation := by
  intro h
  cases h with
  | step t g hne hwf => apply hne; simp

-- ### Semântica

-- Dar semântica a Batalha Naval exige um modelo do que existe fora da
-- linguagem — o estado do tabuleiro — e uma regra que ligue cada expressão da
-- sintaxe a esse estado. Um estado do jogo é um tabuleiro com a posição dos
-- navios marcada, mais o registro das células já atacadas até aquele ponto.

-- Os não-terminais da gramática não carregam todos o mesmo tipo de
-- significado. `column` e `row` são **referenciais**: apontam para uma célula
-- do tabuleiro, sem dizer nada sobre o que há nela. `ship` é
-- **denotacional**: denota um subconjunto de células do tabuleiro — as que
-- aquele navio ocupa num estado dado. `attack` é **operacional**: seu
-- significado é a transição de um estado do jogo para outro, registrando a
-- posição atacada — é o que `updateBattle`, mais adiante, implementa. Já
-- `reaction` tem valor verdade, seu significado é um predicado sobre um
-- estado e uma posição, que vale ou não vale, sem alterar nada — é o papel de
-- `hit`, `missed`, `sunk` e `defeated`. `turn`, por combinar um ataque com
-- uma reação, tem significado composto: primeiro a transição de estado,
-- depois a verificação sobre o estado resultante.

-- Um tabuleiro então é apenas uma lista de pares ordenados. E como um navio
-- ocupa células adjacentes de uma mesma linha ou coluna, também podemos
-- entender que cada navio é uma lista de células: um encouraçado 5 células,
-- uma fragata 4 célula, um submarino 3 células, um contratorpedeiro 2
-- células.

abbrev Grid := List (Column × Fin 10)

def battleshipCells : Grid := [(.D, 3), (.E, 3), (.F, 3), (.G, 3), (.H, 3)]
def frigateCells : Grid := [(.B, 3), (.B, 4), (.B, 5), (.B, 6)]
def sub1Cells : Grid := [(.A, 8), (.B, 8), (.C, 8)]
def sub2Cells : Grid := [(.G, 6), (.G, 7), (.G, 8)]
def destroyerCells : Grid := [(.H, 0), (.I, 0)]

-- Um estado guarda a lista de grades dos navios — uma por navio, para saber
-- depois qual navio ocupa qual célula — e a grade dos ataques sofridos. Mas
-- nem toda lista de grades é uma distribuição de frota aceitável: duas
-- condições precisam valer sempre, para qualquer estado que o jogo produza.

-- Nenhuma célula pode ser compartilhada por dois navios — a lista de todas as
-- células dos navios não pode ter repetição.

abbrev NoClashes (ships : List Grid) : Prop :=
  ships.flatten.Nodup

-- E cada navio, sozinho, precisa ocupar células adjacentes numa única linha
-- ou coluna.

def toIdx : Column → Nat := fun c => match c with
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4
  | .F => 5 | .G => 6 | .H => 7 | .I => 8 | .J => 9

abbrev ShipOK (ship : Grid) : Prop :=
  let cols := (ship.map fun c => toIdx c.1).mergeSort (· ≤ ·)
  let rows := (ship.map fun c => c.2.val).mergeSort (· ≤ ·)
  (cols.Nodup = false ∧ List.IsChain (· + 1 = ·) rows) ∨
  (rows.Nodup = false ∧ List.IsChain (· + 1 = ·) cols)

-- Note que `NoClashes` e `ShipOK` são `Prop`, não `Bool` — são afirmações
-- sobre um estado, não computações que o jogo executa a cada turno (isso é o
-- papel de `hit`/`missed`/`sunk`/`defeated`, na próxima seção, que calculam a
-- reação verdadeira a cada ataque). `abbrev`, em vez de `def`, mantém as duas
-- transparentes: o Lean já sabe decidir `List.Nodup` e `List.IsChain` quando
-- a relação de base é decidível, e a transparência é o que deixa essas
-- instâncias alcançarem `NoClashes`/`ShipOK` sem esforço extra — uma `def`
-- opaca escondia essa busca.

-- Em vez de deixar as duas condições como testes externos que um estado pode
-- ou não satisfazer — o que fazia o exercício `lineupOK` das versões
-- anteriores deste capítulo —, podemos exigi-las já na definição do tipo: um
-- `State` só existe se vier acompanhado da prova de que sua distribuição de
-- navios as satisfaz. É o estilo idiomático de Lean — **proof-carrying data**
-- —, em que a invariante não é algo a verificar depois, é parte do que
-- significa ser um `State`.

structure State where
  ships : List Grid
  attacks : Grid
  noClashes : NoClashes ships
  shipsOK : ∀ ship ∈ ships, ShipOK ship

def attacksGrid : Grid :=
  [(.F, 8), (.E, 7), (.D, 6), (.C, 5)]

def shipsDistrib : List Grid :=
  [battleshipCells, frigateCells, sub1Cells,
   sub2Cells, destroyerCells]

def exampleState : State :=
  { ships := shipsDistrib
    attacks := attacksGrid
    noClashes := by native_decide
    shipsOK := by native_decide }

-- Um estado que viole alguma das duas invariantes simplesmente não tipa como
-- `State` — não é um valor que o programa possa produzir e testar depois, é
-- um erro do compilador. `gapShip` tem uma lacuna na coluna B, então nenhum
-- `State` pode conter só esse navio: a prova de `shipsOK` que a `structure`
-- exige não existe.

sf_expect_failure
  /-- Contraexemplo: mesma linha, com lacuna na coluna B. -/
  def gapShip : Grid := [(.A, 0), (.C, 0)]
  
  def badState : State :=
    { ships := [gapShip]
      attacks := []
      noClashes := by native_decide
      shipsOK := by native_decide }

-- ### Exercise (3 stars): add-ship ⭐⭐⭐

-- Um estado válido só pode ser estendido por outro estado válido. Complete
-- `addShip`, que tenta adicionar um navio a um estado, preservando as duas
-- invariantes — devolvendo `none` quando a adição as violaria.

def addShip (ship : Grid) (s : State) : Option State :=
  sorry

example : (addShip [(.A, 0), (.A, 1)] exampleState).isSome :=
  sorry

/-- `gapShip` não é um navio válido: a adição falha. -/
example : addShip gapShip exampleState = none :=
  sorry

/-- `destroyerCells` já ocupa células de `exampleState`: colide. -/
example : addShip destroyerCells exampleState = none :=
  sorry

-- A semântica de uma reação depende do estado do jogo e da posição do último
-- ataque. Dado um estado `s`, uma posição `p` e uma reação `r`, queremos
-- dizer quando `r` é a reação verdadeira:

-- - `missed` é verdadeira sse não há navio nenhum na posição `p`;

-- - `hit s'` é verdadeira sse há algum navio na posição `p`;

-- - `sunk s'` é verdadeira sse há um navio do tipo `s'` na posição `p` cujas
--   células estão todas marcadas como atacadas, exceto `p`;

-- - `defeated` é verdadeira sse todo navio do estado está com todas as suas
--   células marcadas.

def hit (a : Attack) (s : State) : Bool :=
  s.ships.flatten.contains (a.column, a.row)

def missed (a : Attack) (s : State) : Bool :=
  !hit a s

def defeated (s : State) : Bool :=
  s.ships.all fun ship => ship.all fun cell => s.attacks.contains cell

#eval defeated exampleState
#eval hit ⟨.B, 4⟩ exampleState
#eval hit ⟨.A, 3⟩ exampleState

-- ### Exercise (2 stars): sunk ⭐⭐

-- Implemente uma função booleana que diz se um ataque afunda um navio de um
-- tipo específico, num estado dado.

def sunk (a : Attack) (ship : Ship) (s : State) : Bool :=
  sorry

/-- Estado com só o destroyer, quase afundado: falta atacar `(.H, 0)`. -/
def almostSunkState : State :=
  { ships := [destroyerCells]
    attacks := [(.I, 0)]
    noClashes := by native_decide
    shipsOK := by native_decide }

example : sunk ⟨.H, 0⟩ .destroyer almostSunkState = true :=
  sorry

example : sunk ⟨.B, 3⟩ .frigate exampleState = false :=
  sorry

-- Registrar um novo ataque só acrescenta a posição atacada à grade de ataques
-- — o estado dos navios não muda.

def updateBattle (a : Attack) (s : State) : State :=
  { s with attacks := s.attacks ++ [(a.column, a.row)] }

end Battleship

-- ### Pragmática

-- As definições da seção anterior para `hit`, `missed`, `defeated` e `sunk`
-- seguem uma hierarquia entre as reações: todo ataque que termina uma partida
-- (`defeated`) também é um ataque de afundamento (`sunk`), e todo ataque de
-- afundamento também é um acerto (`hit`). Segue daí que a regra de jogo
-- "reaja corretamente a um ataque" não determina, por si só, a reação
-- apropriada em todos os casos. Pode haver mais de uma reação verdadeira ao
-- mesmo tempo. Escolher entre elas não é questão de semântica — a semântica
-- só diz quais reações são verdadeiras, não qual delas devemos usar. Regras
-- de jogo desse tipo são assunto de pragmática.

-- H. P. Grice (Grice, 1975), filósofo da linguagem, tratou desse tema de
-- forma sistemática. O princípio de *cooperação* entre interlocutores. Grice
-- organiza esse ajuste em máximas:

-- - Quantidade: Diga apenas o necessário. Não forneça menos informação do que o
--   pedido, nem exagere com detalhes inúteis.

-- - Qualidade: Diga a verdade. Não afirme nada que você saiba ser falso ou que
--   não tenha provas.

-- - Relação (ou Relevância): Seja pertinente. Fale apenas sobre o que importa
--   para o momento da conversa.

-- - Modo (ou Maneira): Seja claro. Evite ambiguidades, termos obscuros e
--   desordem, procurando ser breve e direto.

-- Como todo estímulo ao bom comportamento, as máximas são vagas, se
-- sobrepõem, e falam em termos de verdade e informação, noções semânticas.
-- Pragmática, nesse sentido, pressupõe semântica.

-- Por mais vagas que sejam, as máximas de Grice se aplicam com precisão a
-- Batalha Naval, porque a semântica do jogo dá uma medida exata de
-- informação. Por que `sunk` (quando verdadeira) é mais informativa que `hit`
-- (também verdadeira na mesma situação)? Porque `sunk` vale para um conjunto
-- estritamente menor de estados do jogo. O mesmo vale entre `defeated` e
-- `sunk`. Do princípio de cooperação, dado o objetivo de deixar o oponente
-- saber onde ele está, segue que, numa situação em que `sunk` vale, reagir
-- com `hit` é inapropriado; a máxima de quantidade sustenta a mesma conclusão
-- por outro caminho, exigindo a reação mais informativa em cada estágio do
-- jogo.

-- ### Exercise (1 star): grice-maxims ⭐

-- O que mais se pode dizer sobre a pragmática de Batalha Naval em termos das
-- máximas de Grice?

-- ## Mastermind (Jogo Senha)

-- Outra linguagem bem simples é a do Mastermind (Jogo Senha). O Mastermind é
-- um jogo de dois jogadores em que um deles tenta descobrir o código
-- escolhido pelo outro. Um dos jogadores decide uma sequência de quatro pinos
-- coloridos, com as cores escolhidas dentro de um conjunto fixo. O outro
-- jogador (quem tenta decifrar) tenta adivinhar o padrão de cores. Depois de
-- cada palpite, quem propôs o código dá uma resposta indicando sua correção.
-- Essa resposta consiste numa sequência de pinos pretos e brancos: um pino
-- preto para cada pino da cor certa na posição certa, e um pino branco para
-- cada pino adicional da cor certa, mas na posição errada. Se o código
-- secreto é vermelho, azul, verde, amarelo, e o palpite é verde, azul,
-- vermelho, laranja, a resposta é um preto (o azul está na posição certa) e
-- dois brancos (verde e vermelho aparecem no palpite, mas nas posições
-- erradas). Os palpites e as respostas se alternam até que o padrão seja
-- descoberto. O desafio é adivinhar o padrão no menor número de tentativas.

-- colour ::= "red" | "yellow" | "blue" | "green" | "orange" ;
-- answer ::= "black" | "white" ;
-- guess ::= colour colour colour colour ;
-- reaction ::= answer
--   | answer answer
--   | answer answer answer
--   | answer answer answer answer ;
-- turn ::= guess reaction ;
-- game ::= turn | turn game ;

-- Note que os pinos pretos e brancos são colocados em qualquer ordem, não
-- correspondem a uma sinalização por posição. Uma desvantagem da
-- implementação a seguir é que dois diferentes termos do tipo `Reaction`
-- poderiam representar a mesma *resposta* para uma tentativa.

-- Dois tipos do Lean entram aqui, ambos porque a gramática fixa quantidades.
-- Um palpite tem exatamente quatro pinos, e `Vector Colour 4` é a lista de
-- `Colour` cujo comprimento é quatro — o tamanho faz parte do tipo, então uma
-- lista de três cores sequer elabora como `Guess`. Seus valores se escrevem
-- `#v[...]`, como em `turn1` abaixo.

-- Uma resposta tem **no máximo** quatro pinos, que é uma condição e não um
-- tamanho fixo. Para isso serve um **subtipo**:
-- `{ r : List Answer // r.length ≤ 4 }` é o tipo das listas de `Answer`
-- acompanhadas de uma prova de que seu comprimento não passa de quatro. Um
-- valor seu é o par `⟨lista, prova⟩` — daí o `⟨[.black, .white], by simp⟩`
-- mais abaixo, onde `by simp` é a prova de que essa lista tem comprimento
-- menor ou igual a quatro. Sobre ambos, ver (FRO, 2026); sobre subtipos em
-- particular, (Baanen et al., 2026).

namespace Mastermind

inductive Colour where
  | red | yellow | blue | green | orange
  deriving DecidableEq, Repr

inductive Answer where
  | black | white
  deriving DecidableEq, Repr

abbrev Guess := Vector Colour 4

/-- uma alternativa `Vector (Option Answer) 4` -/
abbrev Reaction := { r : List Answer // r.length ≤ 4 }

structure Turn where
  guess : Guess
  reaction : Reaction
  deriving DecidableEq, Repr

abbrev Game := List Turn

def turn1 : Turn :=
  ⟨#v[.green, .blue, .red, .orange],
   (⟨[.black, .white], by simp⟩ : Reaction) ⟩

end Mastermind

-- ### Exercise (1 star): four-turn-game ⭐

-- Revise a gramática para garantir que um jogo tenha no máximo quatro
-- jogadas.

namespace Mastermind

abbrev Game₄ := sorry

end Mastermind

-- ### Exercise (1 star): chess-grammar ⭐

-- Escreva suas próprias gramáticas para o xadrez e em seguida sua
-- implementação no Lean.

-- figure ::= "King" | "Queen" | "Knight"
--   | "Rook" | "Bishop" | "Pawn" ;
-- row    ::= "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" ;
-- column ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" ;
-- move   ::= figure row column ;
-- turn   ::= move move ;
-- game   ::= turn | turn game ;

namespace Chess

inductive Figure where
  | king | queen | knight | rook | bishop | pawn
  deriving DecidableEq, Repr

inductive Row where
  | a | b | c | d | e | f | g | h
  deriving DecidableEq, Repr

structure Move where
  figure : Figure
  row : Row
  column : Fin 8
  deriving DecidableEq, Repr

structure Turn where
  white : Move
  black : Move
  deriving DecidableEq, Repr

abbrev Game := List Turn

end Chess

-- _Quiz:_

-- Todas as gramáticas que discutimos geram linguagens infinitas?

-- A partir das discussões acima, poderíamos sugerir uma primeira gramática
-- para um fragmennto do inglês talvez um tanto quanto permissiva. Qualquer
-- sequencia de caracteres ASCII.

-- character ::= _ascii ;
--  string ::= character | character string ;

