-- # O estudo formal da língua natural

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

-- A língua é uma das capacidades mais notáveis do ser humano e um dos traços
-- distintivos que nos separam dos demais habitantes deste planeta. As línguas
-- humanas são sistemas sofisticados para manipular símbolos que codificam
-- informação, e para compor sons em expressões estruturadas como palavras,
-- sintagmas e sentenças. Essas expressões podem então servir, de inúmeras
-- maneiras, a ações comunicativas como troca de informação, persuasão e
-- engano, expressão de pensamentos, raciocínio, e muito mais.

-- A linguística é o estudo científico da língua humana. Para fazer da
-- linguística uma ciência é necessário especificar o objeto de estudo. Em seu
-- livro *Syntactic Structures* (1957), o linguista Noam Chomsky fez a
-- proposta influente de identificar uma língua humana com o conjunto de todas
-- as sentenças corretas (ou: gramaticais) dessa língua. Essa idealização
-- abstrai das limitações cognitivas de quem usa a língua. Chomsky chamou de
-- competência a capacidade que os usuários da língua têm de reconhecer, ao
-- menos em princípio, os membros desse conjunto, e a distinguiu do
-- desempenho, as capacidades efetivas dos usuários da língua, afetadas por
-- condições como limitações de memória, distração e erros. Neste livro
-- faremos a mesma distinção. Vamos nos concentrar no estudo da competência e,
-- portanto, supor que uma língua particular nos é dada como um conjunto de
-- sentenças.

-- O que exatamente nos torna falantes competentes de nossa língua? O que é o
-- conhecimento linguístico? É certamente algo a que temos acesso apenas
-- limitado. Para a maioria dos falantes de uma língua, as regras e
-- regularidades da língua materna são implícitas. Eles sabem aplicá-las
-- corretamente, mas, quando lhes pedem que as enunciem, em geral ficam sem
-- saber o que dizer. Descrições explícitas das regras e regularidades de uma
-- língua são chamadas de gramáticas. Gramáticas podem ser vistas como modelos
-- de nossa competência linguística.

-- Como as gramáticas estão representadas como dispositivo cognitivo no
-- cérebro do usuário da língua, não temos como saber. De fato, gramáticas
-- podem ser representadas de maneiras bem diferentes. Na vida cotidiana as
-- encontramos, por exemplo, em dicionários, em referências de língua on-line
-- e em livros didáticos para aprender línguas estrangeiras. Seu desenho
-- difere conforme o propósito. Gramáticas para quem aprende uma língua
-- costumam seguir diretrizes pedagógicas e podem simplificar demais as
-- regras. Gramáticas usadas em linguística costumam visar a ser tão
-- explícitas e completas quanto possível. Elas podem começar especificando
-- elementos básicos como sons, palavras e significados. Em seguida enunciam
-- regras sobre como combiná-los em expressões estruturadas mais complexas. Em
-- geral há vários níveis de representação, de acordo com as subdisciplinas da
-- teoria gramatical:

-- - A fonologia explora quais são as menores unidades que distinguem
--   significado (os sons) e como elas se combinam nas menores unidades que
--   carregam significado (os morfemas).

-- - A morfologia se ocupa de como os morfemas se combinam em palavras.

-- - A sintaxe estuda como as palavras se combinam em sintagmas e sentenças.

-- - A semântica investiga os significados das expressões básicas e como o
--   significado é atribuído às expressões complexas com base no significado de
--   expressões mais simples e na estrutura sintática.

-- Neste livro não nos ocuparemos de modo algum da fonologia, e também
-- ignoraremos a maior parte dos aspectos da morfologia. Vamos nos concentrar
-- na forma linguística no nível dos sintagmas e das sentenças. Isso significa
-- que começaremos pelas palavras como blocos de construção básicos. A tarefa
-- principal será então desenvolver uma gramática que nos forneça noções de
-- boa-formação sintática e de estrutura sintática, e que nos permita
-- desenvolver a noção de significado para as estruturas bem formadas. Assim,
-- nossas gramáticas

-- - devem ser capazes de construir exatamente aquelas expressões que são bem
--   formadas na língua de nossa escolha,

-- - devem determinar os constituintes das expressões linguísticas complexas,
--   bem como sua estrutura interna,

-- - e devem nos permitir atribuir significados apropriados às expressões
--   sintaticamente bem formadas, com base em sua estrutura.

-- Em outras palavras, a noção de boa-formação sintática nos permite
-- determinar se uma expressão particular é de fato uma expressão bem formada
-- de uma dada categoria, e determinar sua estrutura interna. A estrutura, por
-- sua vez, ajudará a relacionar as formas linguísticas com o mundo
-- extralinguístico (aquilo de que elas tratam).

-- ## Sintaxe, semântica e pragmática

-- Uma tricotomia básica no estudo da língua é a que se faz entre sintaxe,
-- semântica e pragmática. Grosso modo, a sintaxe diz respeito ao aspecto de
-- forma da língua, a semântica ao seu aspecto de significado, e a pragmática
-- ao seu uso. Desenvolver compreensão sobre a semântica de uma língua
-- pressupõe conhecimento da sintaxe dessa língua; o estudo do uso da língua
-- pressupõe conhecimento tanto da sintaxe quanto da semântica. Não
-- surpreende, então, que para muitas línguas saibamos mais sobre sua sintaxe
-- e sua semântica do que sobre os aspectos pragmáticos de seu uso. Eis
-- definições aproximadas das três noções:

-- **Sintaxe** é o estudo das cadeias e da estrutura que lhes é imposta pelas
-- gramáticas que as geram.

-- **Semântica** é o estudo da relação entre cadeias e seus significados, isto
-- é, de sua relação com a estrutura extralinguística de que elas tratam.

-- **Pragmática** é o estudo do uso de cadeias significativas para comunicar
-- sobre estrutura extralinguística, num processo de interação entre usuários
-- da língua.

-- Num slogan: a sintaxe estuda a Forma, a semântica estuda a Forma + o
-- Conteúdo, e a pragmática estuda a Forma + o Conteúdo + o Uso. Neste
-- capítulo examinaremos o que se pode dizer sobre essa tricotomia em casos
-- concretos.

-- É matéria de estipulação o que se toma como "forma" na língua natural. A
-- seguir vamos nos concentrar na língua escrita, mais especificamente em
-- sentenças bem formadas. Assim, olharemos para as línguas como conjuntos de
-- cadeias de símbolos tomados de algum alfabeto.

-- Essa escolha torna particularmente fácil transpor a distância entre
-- linguagens formais e línguas naturais, pois as linguagens formais também
-- podem ser vistas como conjuntos de cadeias. A diferença entre línguas
-- naturais e linguagens formais está na maneira como os conjuntos de cadeias
-- são dados. No caso das linguagens formais, a linguagem é dada por definição
-- estipulativa: uma cadeia pertence à linguagem se é produzida por uma
-- gramática dessa linguagem, ou reconhecida por um algoritmo de análise
-- sintática dessa linguagem. Um algoritmo de análise para C, digamos, pode
-- estar errado no sentido de não estar em conformidade com o padrão
-- internacional da linguagem de programação C, mas em última instância não há
-- certo ou errado aqui: a maneira como as linguagens formais são dadas é
-- matéria de definição.

-- No caso das línguas naturais, a situação é bem diferente. Um formalismo
-- gramatical proposto para uma língua natural (ou para um fragmento de uma
-- língua natural) pode estar errado no sentido de não concordar com as
-- intuições dos falantes nativos da língua. Se uma dada cadeia é ou não uma
-- sentença bem formada de alguma língua é questão a ser decidida com base nas
-- intuições linguísticas dos falantes nativos dessa língua.

-- Uma vez dada uma gramática para uma língua, podemos associar estruturas às
-- sentenças. No caso das línguas naturais, os falantes nativos têm intuições
-- sobre quais constituintes de uma sentença pertencem uns aos outros, e uma
-- gramática de língua natural terá de estar em conformidade com esses juízos.
-- Isso poderia constituir um argumento para considerar árvores de
-- constituintes, em vez de cadeias, como as formas que são dadas.

-- Ainda outras escolhas são possíveis, dependendo do objetivo. Quem considera
-- o problema do reconhecimento de língua natural pode tomar cadeias de
-- fonemas (as menores unidades distintivas de som de uma língua) como as
-- formas básicas. Quem quer admitir incerteza no reconhecimento da língua
-- passa a ter como formas básicas listas de palavras com possibilidade de
-- escolha, os chamados reticulados de palavras (com *full proof* e *fool
-- proof* listados em pé de igualdade como alternativas), ou reticulados de
-- fonemas (cadeias de fonemas envolvendo a possibilidade de escolha). Talvez
-- possamos atribuir probabilidades às escolhas. E assim por diante. E assim
-- por diante.

-- Um caminho alternativo até o significado é apontar, ou demonstrar
-- diretamente, que é possivelmente o ponto de partida da aprendizagem de
-- conceitos básicos. As opiniões de cada um sobre os princípios da
-- aprendizagem de conceitos tendem a ser tingidas por preconceitos
-- filosóficos, então não nos deixemos levar pela especulação. Em vez disso,
-- eis um relato em primeira mão. Foi assim que Helen Keller, nascida
-- surda-muda e cega, aprendeu o significado da palavra *water* com sua
-- professora, a senhorita Sullivan:

-- Descemos o caminho até a casa do poço, atraídas pela fragrância da

-- madressilva que a cobria. Alguém estava tirando água, e minha professora

-- colocou minha mão sob a bica. Enquanto o jato fresco corria sobre uma das

-- mãos, ela soletrou na outra a palavra *water*, primeiro devagar, depois

-- depressa. Fiquei imóvel, toda a minha atenção fixa nos movimentos dos dedos

-- dela. De repente senti uma consciência nebulosa como de algo esquecido — um

-- frêmito de pensamento que retornava; e de algum modo o mistério da
-- linguagem

-- me foi revelado. Soube então que "w-a-t-e-r" significava aquela coisa

-- maravilhosa e fresca que corria sobre a minha mão. Aquela palavra viva

-- despertou minha alma, deu-lhe luz, esperança, alegria, libertou-a!

-- (Keller, 1902)

-- ### Saber "que" e "como"

-- As explicações de significado caem em duas classes amplas: significado como
-- *saber como* e significado como *saber que*. Se dizemos que Joãozinho não
-- sabe o significado de uma boa surra, referimo-nos ao significado
-- operacional. Se Helen Keller escreve que *water* significa a coisa
-- maravilhosa e fresca que corria sobre a sua mão, então ela se refere ao
-- significado como referência, ou significado denotacional.

-- Em geral os dois estão entrelaçados. Suponha que lhe perguntemos como
-- chegar ao Teatro Municipal. Você poderia dizer algo como: "Vire à direita
-- no próximo semáforo e você o verá bem à sua frente." Entender o significado
-- disso envolve ser capaz de seguir as instruções (ser capaz de descobrir
-- qual semáforo conta como o "próximo", qual direção é "à direita", e ser
-- capaz de reconhecer o edifício à frente). Formulado em termos de "ser capaz
-- de descobrir...", "ser capaz de reconhecer...", isso é significado como
-- saber como. Ser capaz de entender o significado das instruções envolve
-- também ser capaz de distinguir instruções corretas de instruções erradas.
-- Em outras palavras, as instruções classificam situações, estando eu
-- posicionado em algum lugar de alguma cidade, voltado para uma direção
-- particular: em algumas situações as instruções fornecem uma descrição que é
-- verdadeira, em outras uma descrição que é falsa. Isso é significado
-- denotacional.

-- O significado denotacional pode ser formalizado como conhecimento das
-- condições de verdade em situações. O significado operacional pode ser
-- formalizado como algoritmos para executar ações (cognitivas). A semântica
-- operacional de *mais* na expressão *sete mais cinco* é a operação de somar
-- dois números naturais; essa operação pode ser dada como um conjunto de
-- instruções de cálculo, ou como a descrição do funcionamento de uma máquina
-- de calcular. A distinção entre semântica denotacional e semântica
-- operacional é básica em ciência da computação, e muitas vezes há bastante
-- trabalho envolvido em mostrar que as duas coincidem.

-- Frequentemente o significado operacional é mais fino que o denotacional.
-- Por exemplo, as expressões *sete mais cinco* e *duas vezes seis* ambas se
-- referem ao número natural doze, de modo que seu significado denotacional é
-- o mesmo. Mas elas têm significado operacional diferente, pois a receita
-- para somar sete e cinco é diferente da receita para multiplicar dois e
-- seis.

-- Que as duas denotam o mesmo número é algo que se pode não apenas calcular,
-- mas demonstrar:

example : 7 + 5 = 2 * 6 := by rfl

-- Sobre o código deste capítulo, um aviso. Ele está aqui para dar uma ideia
-- de onde vamos chegar, e não para ser acompanhado linha a linha agora — nada
-- nele é apresentado, e tudo o que ele usa é explicado nos capítulos
-- seguintes. Leia-o como se lê uma fotografia do destino no começo da viagem:
-- se despertar curiosidade, cumpriu seu papel; se não disser nada por
-- enquanto, siga em frente sem preocupação.

-- ## Os propósitos da comunicação

-- O objetivo mais elevado da comunicação é usar a língua como instrumento
-- para a busca coletiva da verdade. Mas a língua é também um instrumento para
-- fazer seus concidadãos acreditarem em coisas, ou para confundir seus
-- inimigos. Mesmo que dois usuários da língua concordem em não se enganar,
-- isso não exclui o uso da ironia.

-- Um uso muito importante da língua, e do qual nos ocuparemos bastante nas
-- páginas seguintes, é como instrumento para descrever estados de coisas e
-- como instrumento de raciocínio. É um uso que as linguagens formais e a
-- língua natural têm em comum. As linguagens formais são frequentemente
-- projetadas como instrumentos de consulta ou de raciocínio, ou ao menos como
-- instrumentos para reconstruções formais de processos de raciocínio. Por
-- isso elas são um ponto focal natural para o estudo formal da língua.

-- Pode-se ver a coisa assim. Suponha que queiramos usar a língua para
-- comunicar fatos básicos, como "o sol está brilhando", "está frio", "está
-- chovendo", e assim por diante. Se você quiser negar um fato desses, precisa
-- poder dizer algo como "não está frio". Você pode também querer exprimir sua
-- incerteza sobre qual de dois fatos é o caso, e então gostaria de dizer "ou
-- está frio ou está chovendo". Do mesmo modo, você pode querer dizer "está
-- frio e está chovendo", ou: "se chover, então está frio". Assim, os
-- ingredientes do tipo mais simples de comunicação são: fatos básicos,
-- negações, conjunções, disjunções e implicações. Um fragmento de língua
-- natural que só tenha isso já é bastante útil. De fato, a utilidade desse
-- fragmento simples é evidente para os lógicos há muito tempo. O estudo do
-- que pode ser expresso nesse fragmento chama-se lógica proposicional ou
-- lógica booleana, em homenagem ao matemático britânico George Boole
-- (1815–1864).

-- Para ver como a lógica proposicional pode ser usada para exprimir o que se
-- passa em discursos comunicativos simples, suponha que queiramos falar sobre
-- fatos básicos a, b. Suponha que você não saiba nada sobre se esses fatos
-- são verdadeiros ou não. Então, para você, há quatro possibilidades: ambos
-- os fatos são verdadeiros, ambos são falsos, o primeiro é verdadeiro e o
-- segundo falso, ou o primeiro é falso e o segundo verdadeiro. Agora nós lhe
-- dizemos "a ou b". Se você acreditar em nós, isso lhe permitirá descartar
-- uma das quatro possibilidades, aquela em que tanto a quanto b são falsos.
-- Ou, se você tomar nossa afirmação no sentido exclusivo, ela lhe permitirá
-- até descartar duas das quatro possibilidades. Seu conhecimento cresceu pela
-- eliminação de possibilidades.

-- ### Exercise (1 star): possibilities ⭐

-- A ignorância completa sobre a verdade ou falsidade de dois fatos se modela
-- como incerteza entre quatro possibilidades. Com dez fatos básicos, quantas
-- possibilidades? E no caso geral de `n` fatos?

def possibilities : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * possibilities n

#eval possibilities 10

-- Em Lean, podemos provar propriedades sobre funções, embora óbvio para este
-- caso, sabemos que a função `possibilities` computa basicamente a expressão
-- $2^n$. No passo indutivo é preciso desdobrar a potência, e há dois lemas
-- para isso: `Nat.pow_succ'` e `Nat.pow_succ`.

example (n : Nat) : possibilities n = 2 ^ n := by
 induction n with
  | zero => rfl
  | succ k ih => rw [possibilities, ih, Nat.pow_succ']

-- Se você quiser apenas estudar a troca simples de informação factual, faz
-- sentido concentrar-se no fragmento de língua natural que pode ser traduzido
-- para a lógica proposicional. Mas suponha que você queira ser mais explícito
-- ao exprimir relações entre coisas. Se você deseja declarar seu amor a
-- alguém, digamos, então enunciar uma proposição básica como "há amor" talvez
-- não seja articulado o bastante. Você pode querer dizer algo mais ousado,
-- como "eu amo você". Uma fala dessas exprime relações entre sujeitos e
-- objetos. Você pode usar pronomes como "eu" e "você", mas também nomes
-- próprios. Você ainda pode fazer o que é proposicional, como disjunções e
-- negações, mas pode também exprimir fatos quantificacionais. Você pode usar
-- o poder da quantificação para acrescentar algo à sua declaração romântica,
-- reforçando-a para "não amo ninguém além de você". Você está agora no
-- domínio que se chama lógica de predicados.

-- Pode-se dizer coisas interessantes com a lógica de predicados, ao menos se
-- você souber usá-la, pois a lógica de predicados é muito expressiva. Veremos
-- adiante que a lógica de predicados nos leva bem longe na expressão dos
-- significados de enunciados de língua natural. Ainda mais expressiva é a
-- lógica tipada de ordem superior, que também será usada extensivamente neste
-- livro. Na lógica tipada você pode dizer coisas mais abstratas (mas ainda
-- românticas) como "amar alguém como você me faz muito feliz". Por fim, ao
-- final do livro, daremos uma olhada na lógica do conhecimento, ou lógica
-- epistêmica. Isso lançará luz sobre o significado de enunciados como "não
-- tenho certeza absoluta se ainda amo você". Ela também nos permitirá dar um
-- quadro abstrato de como a comunicação por meio de enunciados declarativos
-- leva ao crescimento do conhecimento, de maneiras sutis. Estudaremos o
-- crescimento do conhecimento da audiência sobre o que o falante sabe, mas
-- também o crescimento do conhecimento do falante sobre o conhecimento da
-- audiência sobre o conhecimento do falante, e assim por diante.

-- A lógica é um campo que fez um progresso tremendo ao concentrar-se em
-- linguagens formais bem definidas, como as linguagens de exemplo acima, e
-- estudar suas propriedades em profundidade. É possível ver linguagens
-- lógicas como a da lógica proposicional ou a da lógica de predicados como
-- fragmentos de língua natural, concentrando-se no conjunto específico de
-- sentenças da língua natural que podem ser traduzidas para a linguagem
-- lógica. Este será um método importante neste livro. Esse método dos
-- fragmentos, de tomar as coisas passo a passo, foi proposto pela primeira
-- vez para a análise da língua natural pelo lógico e filósofo Richard
-- Montague (1930–1971), nos anos 1970, quando ele fez a seguinte afirmação
-- famosa:

-- Não há, em minha opinião, diferença teórica importante entre as línguas

-- naturais e as linguagens artificiais dos lógicos; de fato, considero
-- possível

-- compreender a sintaxe e a semântica de ambos os tipos de linguagem dentro
-- de

-- uma única teoria natural e matematicamente precisa.

-- (Montague, 1974)

-- O trabalho pioneiro de Montague mostrou como as línguas naturais podem ser
-- descritas formalmente usando técnicas tomadas de empréstimo à lógica. Ele
-- introduziu instrumentos para computar significados de maneira sistemática e
-- deu origem a toda uma tradição de semântica formal, um termo bastante geral
-- que recobre as abordagens lógicas da semântica de língua natural.

-- Nosso objetivo último é formar um modelo adequado de partes de nossa
-- competência linguística. Adequado significa que o modelo tem de ser
-- realista em termos de complexidade e de aprendibilidade. Não seremos tão
-- ambiciosos a ponto de afirmar que nosso relato espelha processos cognitivos
-- reais, mas o que afirmamos é que nosso relato impõe restrições sobre a
-- aparência que os processos cognitivos reais podem ter. No resto deste
-- capítulo, vamos explorar os meios que nos ajudarão a cumprir esse objetivo.

-- ## Línguas naturais e línguas formais

-- O inglês, o sueco, o russo e o híndi são línguas naturais. A linguagem da
-- aritmética do ensino fundamental, a linguagem da lógica proposicional e a
-- linguagem de programação Lean são linguagens formais. Mas a distinção não é
-- absoluta, pois encontramos casos intermediários, como o esperanto. Para ver
-- se podemos traçar uma linha divisória, vejamos alguns traços de projeto
-- cruciais das línguas humanas.

-- - **Dupla articulação** (ou dupla estruturação): a construção do conteúdo
--   linguístico pode ser analisada em dois níveis estruturais. Um é o nível que
--   contém as menores unidades significativas da língua: morfemas ou palavras,
--   como *cat*. Elas, porém, não são mínimas: em outro nível são feitas de um
--   pequeno conjunto de sons da fala, os chamados fonemas. Estes não carregam
--   significado em si, apenas diferenciam unidades significativas — por exemplo
--   /k/ e /m/, que distinguem *cat* de *mat*.

-- - **Recursão**: padrões estruturais em sentenças ou sintagmas podem
--   repetir-se a si mesmos. Um nome comum *bird* pode ser modificado para
--   formar o nome comum complexo *green bird*, que pode ser modificado de novo
--   para formar *small green bird*, e de novo, para formar *beautiful small
--   green bird*.

-- - **Contextualidade**: o que um sintagma ou uma sentença significa é
--   determinado em parte pelo contexto em que o sintagma é usado.

-- ### Exercise (1 star): sentence-go-on ⭐

-- Pollard e Sag dão este exemplo de recursão que estende sentenças:

-- Sentences can go on.
-- Sentences can go on and on.
-- Sentences can go on and on and on.
-- Sentences can go on and on and on and on.
-- ...

-- Dê uma descrição concisa do padrão de recursão — isto é, escreva o gerador.
-- `sentence n` deve produzir a sentença com `n` repetições de "and on".

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

-- As propriedades de dupla articulação, recursão e contextualidade separam as
-- línguas humanas dos sistemas comunicativos dos animais, como a dança das
-- abelhas. São elas as responsáveis pela economia criativa da língua, pois
-- nos permitem construir e compreender infinitas sentenças usando apenas
-- finitos sons e finitas regras — uma precondição para que as crianças
-- aprendam a língua tão rápida e facilmente quanto aprendem.

-- Outra noção-chave, quando se fala das propriedades das línguas humanas, é a
-- composicionalidade. O chamado princípio da composicionalidade vai nos
-- ocupar bastante no que se segue. Esse princípio costuma ser atribuído ao
-- matemático alemão Gottlob Frege (1848–1925). O que ele diz é que o
-- significado de uma expressão complexa depende dos significados de suas
-- partes e do modo como elas são combinadas sintaticamente. Essa formulação é
-- bastante vaga, no entanto, porque nada se diz ainda sobre o que são
-- significados, o que conta como parte de uma expressão, e de que tipo de
-- dependência estamos falando. Para fazer sentido, o princípio tem de ser
-- especificado quanto a essas questões. Além disso, ele só é significativo
-- quando entendido contra o pano de fundo de exigências adicionais sobre uma
-- teoria semântica, por exemplo a exigência de que a atribuição de
-- significado seja sistemática. Um relato sistemático assim capturará o fato
-- de que, uma vez que sabemos o significado de *white unicorn* e de *brown
-- elk*, também sabemos o que significam *brown unicorn* e *white elk*.

-- A composicionalidade não aparece na lista das propriedades cruciais das
-- línguas humanas dada acima, porque supomos que ela é primariamente uma
-- questão de metodologia. A pergunta não é se as línguas naturais satisfazem
-- o princípio da composicionalidade, mas antes se podemos e queremos projetar
-- a montagem do significado de modo que esse princípio seja respeitado.
-- Montar a representação do significado de maneira composicional tem o mérito
-- da elegância, mas nem sempre é direto. Uma dificuldade recorrente é a
-- dependência de contexto do significado na língua natural. Para enunciar o
-- significado de um pronome é preciso informação sobre o contexto em que o
-- pronome ocorre. Algo semelhante vale para as pressuposições. Nesses casos
-- há, em geral, dois tipos de reação. A saída fácil é abrir mão da
-- composicionalidade. O outro tipo de reação é enriquecer e estender nossa
-- teoria semântica de modo a permitir capturar de maneira composicional
-- fenômenos aparentemente não composicionais. Voltaremos a essas questões a
-- seu tempo, quando olharmos mais de perto a resolução de pronomes e a
-- pressuposição.

-- Além das línguas naturais, há outros sistemas de manipulação de símbolos
-- que também exibem algumas das propriedades listadas acima, por exemplo a
-- linguagem da lógica de predicados e as linguagens de programação de alto
-- nível. Mas estas aparentemente carecem de outras propriedades das línguas
-- humanas. Por exemplo, carecem de toda a dimensão pragmática que as línguas
-- humanas empregam: o engano, a ironia, transmitir informação sem enunciá-la
-- explicitamente, e capacidades como criar e compreender metáforas. As
-- linguagens formais também carecem da flexibilidade das línguas humanas,
-- induzida pela vagueza junto com o uso intenso de contexto e de conhecimento
-- de fundo. Essas diferenças, de fato, são a razão pela qual as línguas
-- naturais são bem adequadas à comunicação eficiente entre humanos, ao passo
-- que as linguagens formais se destacam para fazer matemática e para
-- interagir com computadores.

-- Essas diferenças importantes se tornam visíveis se nos concentramos no modo
-- como as línguas naturais e as linguagens formais são usadas. As diferenças
-- somem de vista se olhamos para as línguas como conjuntos de sentenças.
-- Quando nos concentramos em fragmentos de línguas naturais e descrevemos sua
-- gramática de maneira formal, estamos, de fato, fazendo exatamente o mesmo
-- que ao descrever linguagens formais.

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

-- Um preconceito difundido contra a semântica formal para a língua natural é
-- o de que ela não passa de um exercício de tipografia. Explica-se o
-- significado de *and* na língua natural dizendo que o significado de *Toto
-- barked and Dorothy smiled* é igual a A e B, onde A é o significado de *Toto
-- barked* e B é o significado de *Dorothy smiled*. Parece que nada se ganha
-- ao explicar *and* por "e".

-- A resposta a isso é que *and* se refere a uma operação que se supõe já
-- apreendida, a saber, a operação de tomar o encontro booleano de dois
-- objetos numa estrutura booleana. Supondo que saibamos o que é uma estrutura
-- booleana, isso é uma explicação de verdade, e não apenas um truque
-- tipográfico. Por outro lado, se alguém está justamente aprendendo o que são
-- estruturas booleanas ao ser exposto a um relato da semântica da lógica
-- proposicional, pode bem parecer que nada acontece na explicação semântica
-- da conjunção proposicional.

-- Uma história conhecida sobre a linguista Barbara Partee conta que ela certa
-- vez encerrou um curso sobre semântica de Montague convidando os alunos a
-- fazer perguntas. Como era o fim do curso, podiam perguntar qualquer coisa,
-- por mais vagamente relacionada ao assunto que fosse. Um aluno então
-- perguntou: "Qual é o significado da vida?" E Partee disse: "Para responder
-- a essa pergunta basta ver como Montague trataria a palavra *life*. Ele a
-- traduziria em sua lógica intensional como a constante `life'`, e usaria um
-- operador de cap para indicar que se referia ao significado, isto é, à
-- extensão em todos os mundos possíveis. Portanto a resposta à sua pergunta
-- é: o significado da vida é `^life'`. Mais alguma pergunta?"

-- O cerne do problema é que é difícil, de todo modo, evitar a referência ao
-- significado por meio de símbolos. Compare com o processo de explicar o
-- significado da palavra *bicycle* a alguém que não fala inglês. Uma maneira
-- de explicar o significado da palavra é desenhar uma bicicleta. Se seu aluno
-- conhece bicicletas, o significado será transmitido assim que ele ou ela
-- apreender que o desenho é apenas outra maneira de se referir ao significado
-- efetivo. O desenho em si é apenas outro símbolo, pois um desenho de
-- bicicleta é apenas outra maneira de se referir a bicicletas. Do mesmo modo,
-- *and* é apenas outro símbolo para o encontro booleano.

-- Uma das coisas que tornam tão fascinante o estudo da língua de um ponto de
-- vista formal é que podemos tomar emprestadas ideias das ciências formais —
-- matemática, lógica e ciência da computação teórica — assim como a
-- linguística também toma emprestadas ideias da psicologia, da filosofia, e
-- assim por diante. Ideias e instrumentos formais podem ser usados para
-- modelar a competência linguística num arcabouço claro e preciso, que por
-- fim nos permite implementar a língua natural numa máquina. Se isso é útil
-- depende dos objetivos de cada um. Quando decidimos nos ocupar do
-- processamento da língua por meio de computadores, os métodos formais são
-- indispensáveis, porque não podemos nos apoiar nas intuições informais do
-- usuário da língua — computadores não aprendem línguas do modo como os
-- humanos aprendem. Para pôr significados num computador, temos de
-- representar significados de maneira exata e compacta. Para esse fim vamos
-- usar representações de significado numa linguagem formal, o que tem a
-- vantagem de ser não ambíguo e preciso, e que também nos dá a possibilidade
-- de provar nossas afirmações e nos fornece um instrumento de raciocínio.

-- Em contraste com a situação dos estudos informais, forjaremos nós mesmos os
-- instrumentos conceituais de nosso estudo, por meio de definições formais.
-- Essas definições devem ser tomadas muito ao pé da letra. Vez após vez será
-- necessário relembrar as definições para entender a análise. Nesse aspecto o
-- estudo formal é bem diferente de ler romances. A abordagem formal da língua
-- convida a mastigar, e mastigar, e mastigar de novo, até chegar à digestão
-- adequada. Se você ainda não está acostumado a ler coisas escritas em estilo
-- formal, pode ter a sensação de que as explicações vão rápido demais. A
-- culpa não é sua e, além disso, o remédio é fácil: basta lembrar-se de ir
-- mais devagar.

-- ## Semântica computacional e programação funcional

-- A abordagem da semântica de língua natural propagada por Richard Montague —
-- às vezes chamada de programa montagoviano — mostrou-se muito fecunda nas
-- últimas décadas. Mais recentemente desenvolveu-se uma disciplina de
-- programação dita funcional, que se ajusta naturalmente à abordagem de
-- Montague. Como a gramática de Montague, a programação funcional se baseia
-- no chamado cálculo lambda tipado.

-- Ora, por que afinal os linguistas teriam de adquirir habilidades de
-- programação? A programação funcional é uma habilidade útil para linguistas
-- não só pelo encaixe com a gramática de Montague, mas também porque permite
-- experimentos esclarecedores com formatos de regras linguísticas.
-- Implementar um sistema de regras força o linguista a ser inteiramente
-- preciso quanto às regras que propõe. Você descobrirá que, uma vez versado
-- em programação funcional, seus esforços de programação lhe darão retorno
-- imediato sobre suas teorias linguísticas.

-- Há basicamente duas coisas para as quais as máquinas são usadas em
-- semântica computacional. Uma é automatizar a construção de representações
-- de significado. A outra é operar sobre os resultados. Operações possíveis
-- são a verificação de modelos (ou a construção de modelos) e a execução de
-- tarefas de inferência. Operações desse tipo são essenciais para aplicações
-- de Processamento de Língua Natural, por exemplo para buscar informação
-- dentro de documentos ou bases de dados (recuperação de informação), como
-- implementado em mecanismos de busca na web, para desenvolver e implementar
-- sistemas de diálogo ou sistemas de resposta a perguntas, e a longo prazo
-- também para que máquinas executem tarefas de inteligência artificial.

-- Mas, além dessas aplicações práticas, há também benefícios que surgem do
-- processo de automatizar a construção de representações de significado.
-- Nesse contexto, a escolha da programação funcional não é acidental. Com
-- Lean, o passo da definição formal ao programa é particularmente fácil. Isso
-- pressupõe, evidentemente, que você esteja à vontade com definições formais.
-- Nossa razão para combinar o treino em raciocínio e em linguística
-- computacional com uma introdução à programação funcional é que um e outro
-- podem ser fecundos entre si. Por um lado, os programas em Lean servirão
-- como ilustrações concretas das coisas que a semântica computacional permite
-- computar. Por outro, ser forçado a ser inteiramente explícito sobre a
-- teoria semântica que se quer implementar pode dar ideias de como refinar e
-- melhorar essa teoria. Além disso, como linguagens de programação como Lean
-- repousam sobre uma base formal sólida, implementar uma teoria semântica
-- oferece um modo fácil de verificar que ela está correta e que faz o que
-- deveria fazer (ou o que se espera que faça). Esperamos mostrar ao longo do
-- livro como Lean pode ajudar na reflexão sobre a semântica formal que se
-- quer usar. Afinal, a semântica computacional é, em larga medida, não apenas
-- a ciência mas também a arte de processar significado por computador.

-- A maior parte do trabalho atual em semântica computacional usa Prolog, uma
-- linguagem baseada na lógica de predicados e projetada para engenharia de
-- conhecimento. Decidimos nos afastar dessa tradição. Programas em Prolog
-- devem ser implementações de predicados lógicos, mas há um senão. Para fazer
-- do Prolog uma linguagem de programação completa, foi preciso acrescentar
-- operadores de controle, como `assert`, `retract` e `cut`. Sem o poder desse
-- controle a linguagem simplesmente não é expressiva o bastante, mas os
-- efeitos de controle tornam os programas em Prolog muitas vezes difíceis de
-- entender e de depurar, e estragam a pureza lógica. Diferentemente do
-- paradigma da programação em lógica, o paradigma da programação funcional
-- admite pureza lógica. A programação funcional pode produzir implementações
-- notavelmente fiéis às definições formais. Neste estágio isso é apenas o
-- enunciado de uma afirmação, evidentemente, mas o resto do livro pode ser
-- visto como uma ilustração dessa afirmação.

end IntroCS

