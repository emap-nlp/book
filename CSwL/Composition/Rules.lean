-- # As Regras do Jogo

-- Um exercício de tradução de uma sentença em linguagem natural para uma
-- linguagem lógica formal pressupõe que entendemos tanto a sentença quanto as
-- fórmulas dessa linguagem formal. O significado das fórmulas pode ser
-- explicitado pelas definições de verdade da lógica. O exercício pede então
-- que expressemos nessa linguagem uma mensagem que já compreendemos. Isso
-- ajuda a explorar o poder expressivo da lógica, mas pressupõe justamente a
-- compreensão da sentença cujo significado queremos explicar.

-- O procedimento de interpretação apresentado em FOL como Linguagem de
-- Representação permite explicar como o significado de uma sentença é
-- construído. Para aplicá-lo, precisamos conhecer os significados dos
-- componentes básicos e as regras que os combinam. Os significados das
-- palavras são dados pelo modelo, que associa nomes a entidades e predicados
-- a propriedades e relações. Tomamos essas associações como dadas e estudamos
-- como compô-las para interpretar expressões maiores.

-- O Princípio da Composicionalidade, apresentado em O Estudo Formal da Língua
-- Natural, afirma que o significado de uma expressão é uma função dos
-- significados de seus componentes sintáticos imediatos e do modo como eles
-- se combinam. A semântica computacional estuda como realizar
-- sistematicamente essa construção. O princípio está presente no trabalho de
-- Frege e foi explicitado na abordagem de Montague para a semântica da língua
-- natural. O tratamento dos quantificadores é outro ingrediente central dessa
-- abordagem e será o ponto de partida para as nossas regras.

