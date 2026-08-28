-- # O estudo formal da língua natural

-- Ref. CSwFP/1. Formal Study of Natural Language.

-- Este capítulo introduz semântica computacional.

-- O capítulo começa com uma visão geral do estudo formal da linguagem. As
-- áreas abrangentes da sintaxe, semântica e pragmática são distinguidas, e o
-- conceito de significado é discutido.

-- Como iremos nos concentrar na linguagem como uma ferramenta para descrever
-- estados de coisas e transmitir informações, e como os lógicos desenvolveram
-- ferramentas específicas para essas tarefas, a lógica será importante para
-- nós. O capítulo enfatiza as semelhanças entre as línguas naturais e as
-- linguagens formais que foram desenvolvidas por lógicos e cientistas da
-- computação. O capítulo termina com uma discussão sobre a utilidade da
-- programação funcional para a semântica computacional e com uma visão geral
-- do restante do livro.

namespace IntroCS

-- ## O estudo da língua natural

-- Uma língua encadeia estruturas dentro de estruturas, e a descrição se
-- organiza em níveis, cada um tomando como átomo o que o nível anterior
-- produziu:

-- - **fonologia** - quais são as menores unidades de som que distinguem
--   significado, e como elas se combinam nas menores unidades que carregam
--   significado;

-- - **morfologia** — como essas unidades se combinam em palavras;

-- - **sintaxe** — como palavras se combinam em constituintes e sentenças;

-- - **semântica** — que significado têm as expressões básicas, e como o
--   significado das compostas resulta dele e da estrutura sintática.

-- Deste ponto em diante, os dois primeiros níveis ficam de fora. A palavra é
-- o átomo, e não se pergunta do que ela é feita. É uma escolha de escopo, não
-- uma tese: harmonia vocálica e declinação são fenômenos reais, e vão
-- aparecer no capítulo 2 como exemplos resolvidos de programação — mas como
-- dados, não como teoria.

-- O que se exige de uma gramática, nos dois níveis que restam, são três
-- coisas: que ela construa exatamente as expressões bem formadas da língua em
-- questão, que ela determine os constituintes de uma expressão e sua
-- estrutura interna, e que essa estrutura seja suficiente para atribuir
-- significado.

-- Falantes aplicam as regras da própria língua corretamente e, perguntados,
-- quase nunca conseguem enunciá-las. O conhecimento é implícito. Uma
-- gramática é uma descrição explícita dele, e vale como modelo desse
-- conhecimento — não como descrição do que acontece na cabeça de alguém, que
-- ninguém sabe. A idealização que torna o estudo possível separa duas coisas.

-- - **Competência** é a capacidade de reconhecer as sentenças da própria
--   língua.

-- - **Desempenho** é o que de fato se produz, sujeito a limites de memória,
--   distração e erro. Um falante que troca uma concordância no meio de uma
--   frase longa não revogou a gramática do português.

-- A distinção é de Chomsky, e é ela que autoriza tratar uma língua como um
-- **conjunto de sentenças** — objeto matemático, sobre o qual se pode provar
-- coisas.

-- ## Sintaxe, semântica e pragmática

-- Sobre a mesma expressão cabem três perguntas, e elas se encaixam: a segunda
-- pressupõe a primeira, e a terceira pressupõe as duas anteriores.

-- - **sintaxe** estuda a forma;
-- - **semântica** estuda a forma mais o conteúdo;
-- - **pragmática** estuda a forma, o conteúdo e o uso.

-- A semântica é o objeto central daqui em diante, e a sintaxe entra na medida
-- em que ela é necessária — não se calcula o significado de uma sentença sem
-- antes saber como ela se divide em partes. A pragmática reaparece no
-- capítulo 13, quando o assunto for o que dois interlocutores sabem um sobre
-- o conhecimento do outro.

-- Tratar uma língua como conjunto de estruturas aproxima língua natural de
-- linguagem formal, e é uma aproximação deliberada. Mas há uma assimetria
-- entre as duas, e ela não é pequena.

-- Uma linguagem formal é dada por estipulação: uma cadeia pertence a ela se a
-- gramática a produz. Não há como a definição estar errada — ela é a
-- definição. Uma gramática de língua natural, ao contrário, pode estar
-- errada: se ela gera uma sentença que os falantes rejeitam, ou rejeita uma
-- que eles aceitam, é a gramática que cede. O juiz é a intuição de quem fala
-- a língua, e isso faz da linguística uma ciência empírica onde o estudo de
-- linguagens formais é matemática.

-- A escolha do que conta como "forma" também não é única. Aqui serão cadeias
-- de palavras, e depois árvores de constituintes. Quem trabalha com
-- reconhecimento de fala parte de cadeias de fonemas, ou de reticulados que
-- registram alternativas com suas probabilidades.

-- ### Saber "que" e "como"

-- Há duas maneiras de explicar o que uma expressão significa, e a diferença
-- entre elas organiza todo o resto.

-- Explicar *turn right at the next traffic light* é, em parte, dizer o que a
-- pessoa tem de saber fazer: identificar qual semáforo é o próximo, qual lado
-- é o direito. Significado operacional que se formaliza como algoritmo.

-- Mas é também dizer quando a instrução é verdadeira e quando é falsa — a
-- instrução classifica situações, e em algumas ela acerta. Significado
-- denotacional, que se formaliza como condição de verdade.

-- A distinção é familiar em computação, e mostrar que as duas versões
-- coincidem costuma dar trabalho.

-- E o significado operacional é frequentemente mais fino que o denotacional.
-- *Seven plus five* e *two times six* denotam o mesmo número: a denotação não
-- os distingue. As receitas para chegar lá são duas, e é isso que o
-- operacional vê.

-- Essa é a razão de haver dois modos de perguntar se algo é verdadeiro.
-- Verificar uma sentença contra uma situação dada é calcular: a resposta é
-- `true` ou `false`, e sai em tempo finito. Concluir uma sentença a partir de
-- outras é demonstrar: a resposta é uma prova. Os dois modos aparecem
-- adiante, e Lean é incomum entre as linguagens de programação por hospedar
-- ambos.

example : 7 + 5 = 2 * 6 := by rfl

-- ## Os propósitos da comunicação

-- Comunicar serve a muitas coisas — encontrar a verdade em conjunto,
-- convencer, confundir, ironizar. Uma delas interessa particularmente aqui:
-- descrever estados de coisas e raciocinar sobre eles, que é o uso que língua
-- natural e linguagem formal têm em comum.

-- Considere dois fatos básicos sobre os quais nada se sabe. Há quatro
-- possibilidades: ambos verdadeiros, ambos falsos, o primeiro só, o segundo
-- só. Agora alguém diz *a ou b*. Quem acredita elimina uma das quatro —
-- aquela em que os dois são falsos; lendo o *ou* como exclusivo, elimina
-- duas.

-- Conhecimento cresceu, e cresceu por **eliminação de possibilidades**. Essa
-- é a imagem que sustenta tanto a verificação de sentenças contra modelos, no
-- capítulo 6, quanto a teoria de comunicação do capítulo 13, onde uma
-- afirmação pública elimina possibilidades para todos os presentes ao mesmo
-- tempo.

-- ### A escada dos instrumentos

-- O fragmento mínimo capaz de sustentar essa conversa tem fatos básicos,
-- negação, conjunção, disjunção e implicação. É a **lógica proposicional**, e
-- Boole já tinha percebido o quanto ela rende.

-- Para dizer mais é preciso mais. Relações entre sujeitos e objetos, nomes
-- próprios, pronomes e quantificação exigem **lógica de predicados** — que é
-- o que separa *there is love* de *I love no-one but you*. Falar de
-- significados como objetos que se combinam exige **lógica tipada de ordem
-- superior**. E falar do que os interlocutores sabem, inclusive do que sabem
-- sobre o que o outro sabe, exige **lógica epistêmica**.

-- Essa escada é o índice do curso. Cada degrau é um capítulo, e cada um entra
-- quando o anterior deixa de dar conta de um fenômeno.

-- ### O método dos fragmentos

-- Nenhuma dessas lógicas cobre uma língua inteira, e o programa não é esse. O
-- método é recortar: escolher o conjunto de sentenças que se traduz numa
-- lógica dada, tratá-lo por completo, e só então ampliar.

-- A ideia é de Montague, nos anos 1970, e vem acompanhada de uma afirmação
-- forte — que não há diferença teórica importante entre as línguas naturais e
-- as linguagens artificiais dos lógicos, e que a sintaxe e a semântica de
-- ambas cabem numa única teoria matematicamente precisa. É dela que nasce a
-- tradição chamada de semântica formal.

-- O objetivo, então, é um modelo adequado de *partes* da competência
-- linguística. Adequado significa realista quanto a complexidade e a
-- aprendibilidade. Não se afirma que o modelo espelhe processos cognitivos; o
-- que se afirma é que ele restringe o que esses processos podem ser.

-- ### Exercise (1 star): possibilities ⭐

-- Ref. CSwFP/1, exercício 1.1 (p. 6).

-- A ignorância completa sobre a verdade ou falsidade de dois fatos se modela
-- como incerteza entre quatro possibilidades. Com dez fatos básicos, quantas
-- possibilidades? E no caso geral de `n` fatos?

def possibilities : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * possibilities n

#eval possibilities 10

-- Em Lean, podemos provar proriedades sobre funções, embora óbvio para este
-- caso, sabemos que a função `possibilities` computa basicamente a expressão
-- $2^n$. No passo indutivo é preciso desdobrar a potência, e há dois lemas
-- para isso: `Nat.pow_succ'` e `Nat.pow_succ`.

example (n : Nat) : possibilities n = 2 ^ n := by
 induction n with
  | zero => rfl
  | succ k ih => rw [possibilities, ih, Nat.pow_succ']

-- ## Línguas naturais e línguas formais

-- Comparada a sistemas de comunicação animal, a língua humana tem três traços
-- de projeto que valem nomear:

-- - **dupla articulação** — o conteúdo se organiza em dois níveis. Palavras e
--   morfemas carregam significado, mas são feitos de um punhado pequeno de sons
--   que não significam nada por si; é a diferença entre /k/ e /m/ que separa
--   *cat* de *mat*.

-- - **recursão** — um padrão estrutural pode se aplicar ao próprio resultado.
--   *bird*, *green bird*, *small green bird*, *beautiful small green bird*.

-- - **contextualidade** — parte do que uma expressão significa vem de onde ela
--   foi dita.

-- Os dois primeiros explicam a economia criativa da língua: infinitas
-- sentenças a partir de finitos sons e finitas regras. Sem isso, nenhuma
-- criança aprenderia a falar no tempo em que aprende — não haveria o que
-- decorar.

-- O terceiro é o que vai dar trabalho, e o trabalho começa no capítulo 12.

-- ### Exercise (1 star): sentence-go-on ⭐

-- Ref. CSwFP/1, exercício 1.2 (p. 8).

-- Pollard e Sag dão este exemplo de recursão que estende sentenças:

-- Sentences can go on.
-- Sentences can go on and on.
-- Sentences can go on and on and on.
-- Sentences can go on and on and on and on.
-- ...

-- Dê uma descrição descrição concisa do padrão de recursão — isto é, escreva
-- o gerador. `sentence n` deve produzir a sentença com `n` repetições de "and
-- on".

-- Uma observação que economiza tempo: a recursão **não** cabe direto em
-- `sentence`, porque o ponto final tem de ficar sempre no fim. O que se
-- repete é o pedaço `" and on"`, e é ele que merece a função recursiva. Por
-- isso o esqueleto vem em duas partes.

-- `andOn n` são as `n` repetições de `" and on"`, sem mais nada.

def andOn : Nat → String
  | 0 => ""
  | n + 1 => " and on" ++ andOn n

-- E a sentença é o começo, mais as repetições, mais o ponto.

def sentence (n : Nat) : String :=
  "Sentences can go on" ++ andOn n ++ "."

#eval sentence 2

-- _Quiz:_

-- Há infinitas sentenças em inglês? Ou segue que sentenças em inglês podem
-- ter comprimento infinito? Ou as duas coisas?

-- ### Composicionalidade

-- Se as sentenças são infinitas, uma lista de significados não serve. O
-- princípio de Frege dá a saída: o significado de uma expressão composta é
-- determinado pelos significados de suas partes e pelo modo como estão
-- combinadas.

-- Enunciado assim, o princípio é vago — não diz o que são significados, nem o
-- que conta como parte, nem que tipo de dependência está em jogo. Ele só
-- ganha conteúdo dentro de uma teoria que responda a isso. E vem acompanhado
-- de uma exigência de sistematicidade: quem sabe o que significam *white
-- unicorn* e *brown elk* tem de saber, sem nada mais, o que significam *brown
-- unicorn* e *white elk*.

-- Vale insistir num ponto que se perde com facilidade. Composicionalidade não
-- é uma afirmação empírica sobre línguas humanas, a ser verificada. É uma
-- decisão de método: a pergunta não é se a língua satisfaz o princípio, mas
-- se se consegue — e se se quer — montar a atribuição de significado de modo
-- que ele seja respeitado. Onde o fenômeno resiste, como em pronomes e
-- pressuposições, há duas reações possíveis: abandonar a composicionalidade,
-- ou enriquecer a teoria até que o fenômeno caiba nela. O caminho escolhido
-- aqui é o segundo, e os capítulos 12 e 13 são o resultado.

-- Em termos de programação, o princípio diz: a interpretação é uma função
-- recursiva sobre a estrutura sintática. Cada construção da gramática tem um
-- caso na definição, e o caso combina os resultados obtidos para os filhos. É
-- a forma exata dos programas que percorrem tipos indutivos.

-- Daí em diante as duas metades do assunto passam a ter a mesma forma. Um
-- fragmento da língua é um tipo; sua semântica é uma função definida por
-- casos sobre esse tipo; uma construção mal formada é um termo que não tipa.

-- Abaixo está a sintaxe de um fragmento de uma linguagem sobre expressões
-- aritméticas e a função de interpretação de 'frases' desta linguagem em
-- termos do Lean. A
-- [BNF](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form)
-- correspondente seria:

-- Expr := | num Nat | plus Expr Expr | times Expr Expr

inductive Expr where
  | num (n : Nat)
  | plus (a b : Expr)
  | times (a b : Expr)
deriving Repr

def sevenPlusFive : Expr :=
  .times (.plus (.num 7) (.num 5)) (.num 1)

def twoTimesSix : Expr := .times (.num 2) (.num 6)

-- A interpretação: um caso por construção da sintaxe, cada caso combinando os
-- resultados obtidos para as partes.

def eval : Expr → Nat
 | .num n => n
 | .plus a b => eval a + eval b
 | .times a b => eval a * eval b

#eval eval sevenPlusFive

-- Estruturas sintáticas diferentes, mesma denotação.

example : eval sevenPlusFive = eval twoTimesSix := by
  unfold sevenPlusFive twoTimesSix
  repeat rewrite [eval]
  rfl -- ou simplesmente `rfl`

-- ## O que a semântica formal não é

-- Há uma objeção antiga contra tudo isso, e ela merece resposta. Explicar que
-- o significado de *Toto barked and Dorothy smiled* é `A ∧ B` parece não
-- explicar nada: trocou-se a palavra *and* pelo símbolo `∧`.

-- A resposta é que o símbolo não está isolado. Ele nomeia uma operação
-- determinada — o `meet` da álgebra booleana. Se se sabe o que é uma
-- estrutura booleana, houve explicação; se se está aprendendo o que é uma
-- estrutura booleana pela semântica da conjunção, então de fato nada
-- aconteceu, e a objeção acerta.

-- O problema de fundo é que não há como referir significado sem símbolo
-- nenhum. Explicar *bicycle* desenhando uma bicicleta funciona, mas o desenho
-- também é um símbolo — só um símbolo mais fácil de reconhecer. A conta se
-- fecha do mesmo modo aqui: o ganho não está em ter trocado de notação, está
-- em a notação nova vir com uma teoria matemática atrás.

-- Por que uma linguagem funcional, e não uma linguagem lógica como o Prolog?
-- O que se ganha em separar a *construção* da representação de significado
-- das *operações* sobre ela?

-- A programação funcional preserva pureza lógica sem precisar dos operadores
-- de controle (`assert`, `retract`, `cut`) que o Prolog exige para ser uma
-- linguagem completa, e que comprometem a leitura dos programas. Separar
-- construção de operação importa porque a primeira pode ser vista como
-- tradução sistemática (forma → representação), e a segunda como cálculo
-- sobre o resultado (model checking, inferência); sem essa segunda parte, a
-- representação construída não serve para nada — não há como usá-la para
-- responder a uma pergunta ou verificar algo.

-- ## Semântica computacional e programação funcional

-- Duas tarefas, e vale separá-las porque exigem coisas diferentes.

-- A primeira é **construir** a representação de significado a partir da forma
-- linguística. É o que ocupa a maior parte do caminho: dada uma sentença,
-- produzir o objeto que a interpreta.

-- A segunda é **operar** sobre o que se construiu — verificar se é verdadeiro
-- num modelo dado, tirar conclusões a partir de um conjunto de premissas,
-- responder a uma pergunta. Sem essa segunda parte a primeira não serve para
-- nada: uma representação de significado que não se pode usar não representa.

-- A programação funcional se encaixa nessas duas tarefas por uma razão que
-- não é acidental: ela é construída sobre o cálculo lambda tipado, que é
-- também o instrumento da semântica na tradição de Montague. Escrever a
-- teoria como programa força a precisão — uma regra vaga simplesmente não
-- compila — e o retorno é imediato: o computador discorda na hora.

-- ## Fragmentos

-- O preço dessa abordagem é o tamanho. Os fragmentos cobrem uma fração da
-- língua, e o vocabulário é estipulado palavra por palavra; nada aqui extrai
-- significado de texto arbitrário.

-- O que se ganha em troca é que tudo fica explícito — a gramática, o
-- significado de cada palavra, a regra de composição. Onde houver
-- ambiguidade, ela aparece como mais de um resultado. Onde houver lacuna, o
-- verificador de tipos a aponta.

end IntroCS

