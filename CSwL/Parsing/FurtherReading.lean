-- # Leituras adicionais

-- Lógicas para falar de relações em árvores foram propostas em Blackburn,
-- Gardent, and Meyer-Viol (1993) (lógica modal) e em Backofen, Rogers, and
-- Vijay-Shanker (1995) (lógica de primeira ordem). As relações binárias entre
-- posições que usamos na seção Árvores Sintáticas podem ser facilmente
-- descritas em termos lógicos.

-- A análise sintática de língua natural pode ser também entendida como um
-- processo de dedução, muito semelhante à dedução lógica Pereira and Warren
-- (1983). A bíblia da análise sintática no contexto da teoria das linguagens
-- formais é Aho and Ullman (1972). A análise de fragmentos de língua natural
-- com Prolog é o tema de Pereira and Shieber (1987). Combinadores de parsers
-- no contexto da programação funcional são introduzidos em Wadler (1985) e
-- recebem discussão adicional em Hutton (1992). Exemplos de combinadores de
-- parsers também podem ser encontrados em Jeuring and Swierstra (2001).

-- Uma linguagem de programação de propósito específico para desenvolver
-- aplicações multilíngues de língua natural, com a análise sintática no
-- centro, é o Grammatical Framework, ou GF. O GF é semelhante a Haskell, mas
-- especializado na escrita de gramáticas. Ver Ranta (2009) e
-- [grammaticalframework.org](https://www.grammaticalframework.org).

-- Os parsers construídos com combinadores seguem a descida recursiva, que não
-- aceita regras recursivas à esquerda. Algoritmos que analisam qualquer
-- gramática livre de contexto, como CKY e Earley, são apresentados no
-- capítulo 19 de Jurafsky and Martin (2026), em Carroll (2022) e em Allen
-- (1995). Bunt, Carroll, and Satta (2004) reúnem trabalhos sobre técnicas de
-- análise sintática de língua natural. Bender and Emerson (2024) tratam do
-- uso computacional de gramáticas de grande cobertura no formalismo HPSG,
-- incluindo a análise sintática com elas.

