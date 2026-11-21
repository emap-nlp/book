import CSwL.Parsing.ParseTrees
import CSwL.Parsing.Recognition
import CSwL.Parsing.Combinators
import CSwL.Parsing.Features
import CSwL.Parsing.Lexicon
import CSwL.Parsing.Categories
import CSwL.Parsing.FurtherReading

-- # Análise Sintática

-- Uma gramática descreve como as palavras se combinam para formar
-- constituintes e sentenças. Até aqui, construímos à mão as árvores que
-- representam essa estrutura. Neste capítulo, vamos partir de uma sequência
-- de palavras e construir as árvores que uma gramática lhe atribui. Esse
-- processo é a análise sintática, ou **parsing**.

-- Começamos pela representação das árvores e pelas relações entre suas
-- posições, como dominância, c-comando e precedência. Com a gramática dos
-- palíndromos, estudamos como decidir se uma sequência pertence à linguagem e
-- como construir as árvores das sequências aceitas. Depois, desenvolvemos
-- parsers por composição de funções menores, de modo que as alternativas e as
-- sequências das regras tenham operações correspondentes no programa.

-- Para analisar um fragmento do inglês, acrescentamos às categorias
-- sintáticas traços de concordância e listas dos complementos que cada
-- expressão exige. Um léxico associa as palavras a essas categorias, e a
-- análise léxica prepara a sentença de entrada para a consulta ao léxico. Os
-- parsers passam então a combinar categorias, verificando a compatibilidade
-- dos traços e as exigências de subcategorização ao construir as árvores.

-- As categorias e as árvores resultantes são exibidas como matrizes de
-- atributos e valores, ou AVMs. Nessa apresentação, cada constituinte reúne
-- suas informações sintáticas e as estruturas de suas filhas. Ao final,
-- teremos um programa que recebe uma sentença e devolve as árvores
-- encontradas, ou informa que alguma palavra é desconhecida ou que a
-- gramática não admite uma análise para a entrada.

