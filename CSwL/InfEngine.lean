import CSwL.Sets

-- # Um motor de inferência

namespace InfEngine

-- Nesta seção construímos um motor de inferência com interface em língua
-- natural, usando um fragmento para falar de classes. Esse fragmento usa os
-- chamados quantificadores aristotélicos, e pode ser visto como uma
-- implementação da teoria da quantificação que se origina com o filósofo
-- grego Aristóteles (384 a.C. – 322 a.C.). Em sua teoria do silogismo,
-- Aristóteles estudou o seguinte padrão inferencial:

-- Quantificador₁ CN₁ VP₁
-- Quantificador₂ CN₂ VP₂
-- ----------------------
-- Quantificador₃ CN₃ VP₃

-- Um exemplo é o silogismo válido BARBARA:

-- Todo A é B
-- Todo B é C
-- ----------
-- Todo A é C

-- A teoria silogística se concentra nos quantificadores do chamado **quadrado
-- das oposições**:

-- Todo A é B    ---    Nenhum A é B
--     |                     |
-- Algum A é B   ---   Nem todo A é B

-- Os quantificadores do quadrado exprimem relações entre um primeiro e um
-- segundo argumento. Ambos os argumentos denotam conjuntos de entidades
-- tomadas de algum domínio de discurso. As expressões quantificadas do
-- quadrado se relacionam pelas diagonais por negação externa (sentencial), e
-- pelas arestas horizontais por negação interna (do sintagma verbal).
-- Segue-se que a relação pelas arestas verticais é a de negação interna mais
-- externa — a chamada **dualidade** de quantificadores.

-- Como Aristóteles supõe que o domínio de discurso é não vazio, as duas
-- expressões quantificadas da aresta superior não podem ser ambas
-- verdadeiras; elas são chamadas de **contrárias**. Do mesmo modo, as duas da
-- aresta inferior não podem ser ambas falsas: são **subcontrárias**.
-- Aristóteles interpreta ainda seus quantificadores com **importe
-- existencial**: "todo A é B" e "nenhum A é B" são tomados como implicando
-- que há A. Sob essa suposição, as expressões da aresta superior implicam as
-- imediatamente abaixo delas.

-- ## Uma língua para falar de classes

-- A gramática é um fragmento minúsculo para perguntar e afirmar coisas sobre
-- classes:

-- Q ::= "Are all" PN PN "?"
--     | "Are no" PN PN "?"
--     | "Are any" PN PN "?"
--     | "Are any" PN "not" PN "?"
--     | "What about" PN "?" ;
-- S ::= "All" PN "are" PN "."
--     | "No" PN "are" PN "."
--     | "Some" PN "are" PN "."
--     | "Some" PN "are not" PN "." ;

-- onde `PN` (plural noun) fica deliberadamente sem gramática própria.

-- Uma classe é nomeada, e para cada classe há sua oposta — o complemento.

inductive Class where
  | cls (name : String)
  | opp (name : String)
  deriving DecidableEq, Repr

def Class.opposite : Class → Class
  | .cls name => .opp name
  | .opp name => .cls name

def Class.toStringImpl : Class → String
  | .cls name => name
  | .opp name => "non-" ++ name

instance : ToString Class := ⟨Class.toStringImpl⟩

-- As afirmações e as perguntas do fragmento:

inductive Statement where
  | allAre (a b : Class)
  | noneAre (a b : Class)
  | someAre (a b : Class)
  | someAreNot (a b : Class)
  deriving DecidableEq, Repr

inductive Query where
  | areAll (a b : Class)
  | areNone (a b : Class)
  | areAny (a b : Class)
  | anyNot (a b : Class)
  | whatAbout (a : Class)
  deriving DecidableEq, Repr

def Statement.toStringImpl : Statement → String
  | .allAre a b => s!"All {a} are {b}."
  | .noneAre a b => s!"No {a} are {b}."
  | .someAre a b => s!"Some {a} are {b}."
  | .someAreNot a b => s!"Some {a} are not {b}."

instance : ToString Statement := ⟨Statement.toStringImpl⟩

-- ## A base de conhecimento e as regras

-- Nossa aplicação é uma extensão ligeira da lógica aristotélica, pois
-- consideramos o caso em que há toda uma base de conhecimento de premissas
-- possíveis, em vez de apenas duas. As duas relações que vamos modelar na
-- base são a de inclusão e a de não inclusão.

-- - "Todo A é B" se exprime por inclusão, `A ⊆ B`.

-- - "Nenhum A é B" se exprime por inclusão no complemento, `A ⊆ não-B`.

-- - "Algum A não é B" se exprime por não inclusão, `A ⊄ B`.

-- - "Algum A é B" se exprime por não inclusão no complemento, `A ⊄ não-B`. Note
--   que isso equivale a `A ∩ B ≠ ∅`.

-- Uma base de conhecimento é uma lista de triplas, onde `(A, B, true)`
-- exprime `A ⊆ B` e `(A, B, false)` exprime `A ⊄ B`.

abbrev KB := List (Class × Class × Bool)

-- As regras do motor são as seguintes. Escrevemos `A ⟹ B` para `A ⊆ B`, e
-- `A ⇏ B` para `A ⊄ B`. Calcular a relação de inclusão a partir de uma base
-- `K` se faz com três regras — a premissa na base, o contrapositivo, e a
-- transitividade:

-- (A, B, ⊤) ∈ K        A ⟹ B              A ⟹ B    B ⟹ C
-- ─────────────        ──────────────      ───────────────
--    A ⟹ B             não-B ⟹ não-A          A ⟹ C

-- Calcular a não inclusão se faz com:

-- (A, B, ⊥) ∈ K        A ⇏ B               A ⟸ B   B ⇏ C   C ⟸ D
-- ─────────────        ──────────────      ───────────────────────
--    A ⇏ B             não-B ⇏ não-A               A ⇏ D

-- Falta um axioma, sem premissa, para a reflexividade da inclusão, e a
-- leitura com importe existencial, que supõe as classes não vazias:

-- ─────────         A não é da forma não-C
-- A ⟹ A            ──────────────────────
--                        A ⇏ não-A

-- ## O motor

-- A implementação usa listas de pares para relações. A **seção à direita** de
-- uma relação num ponto dá tudo que se relaciona com ele.

abbrev Relation (α : Type) := List (α × α)

def rSection {α : Type} [DecidableEq α] (x : α)
    (r : Relation α) : List α :=
  (r.filter (fun p => p.1 = x)).map Prod.snd

def comp {α : Type} [DecidableEq α]
    (r s : Relation α) : Relation α :=
  (r.flatMap (fun p =>
     (s.filter (fun q => q.1 = p.2)).map
       (fun q => (p.1, q.2)))).eraseDups

-- O fecho reflexivo e transitivo é o menor ponto fixo de "acrescente o que a
-- composição produz". Em vez de iterar até estabilizar sem garantia de
-- parada, iteramos com um combustível: cada passo ou estabiliza, ou consome
-- uma unidade.

def lfp {α : Type} [DecidableEq α]
    (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x =>
      let y := f x
      if y = x then x else lfp f n y

def rtc {α : Type} [DecidableEq α] (xs : List α)
    (r : Relation α) : Relation α :=
  let step := fun s => (s ++ comp r s).eraseDups
  lfp step (xs.length * xs.length + 1)
    (xs.map (fun x => (x, x)))

-- O domínio de uma base é o conjunto das classes que nela aparecem, com suas
-- opostas.

def domain (kb : KB) : List Class :=
  (kb.flatMap (fun t =>
    [t.1, t.1.opposite, t.2.1, t.2.1.opposite])).eraseDups

-- A relação de inclusão que a base sustenta: os pares afirmados, mais seus
-- contrapositivos, fechados por reflexividade e transitividade.

def subsetRel (kb : KB) : Relation Class :=
  rtc (domain kb)
    ((kb.filter (fun t => t.2.2)).map
       (fun t => (t.1, t.2.1))
     ++ (kb.filter (fun t => t.2.2)).map
          (fun t => (t.2.1.opposite, t.1.opposite)))

def supersets (c : Class) (kb : KB) : List Class :=
  rSection c (subsetRel kb)

-- A relação de não inclusão. Além dos pares negados e de seus
-- contrapositivos, entram os pares que o importe existencial garante: uma
-- classe nomeada nunca está contida em sua oposta.

def nsubsetRel (kb : KB) : Relation Class :=
  let r :=
    ((kb.filter (fun t => !t.2.2)).map
       (fun t => (t.1, t.2.1))
     ++ (kb.filter (fun t => !t.2.2)).map
          (fun t => (t.2.1.opposite, t.1.opposite))
     ++ (domain kb).filterMap (fun c =>
          match c with
          | .cls n =>
              some (Class.cls n, Class.opp n)
          | .opp _ => none)).eraseDups
  let s := (subsetRel kb).map (fun p => (p.2, p.1))
  comp s (comp r s)

def nsupersets (c : Class) (kb : KB) : List Class :=
  rSection c (nsubsetRel kb)

-- E o motor propriamente dito: responder a uma pergunta é procurar a classe
-- certa numa das duas relações.

def derive (kb : KB) : Query → Bool
  | .areAll a b => (supersets a kb).contains b
  | .areNone a b => (supersets a kb).contains b.opposite
  | .areAny a b => (nsupersets a kb).contains b.opposite
  | .anyNot a b => (nsupersets a kb).contains b
  | .whatAbout _ => false

-- Uma base pequena para experimentar: todo humano é mortal, todo grego é
-- humano, e algum grego é filósofo.

def kb0 : KB :=
  [(.cls "humans", .cls "mortals", true),
   (.cls "greeks", .cls "humans", true),
   (.cls "greeks", .opp "philosophers", false)]

#eval derive kb0 (.areAll (.cls "greeks") (.cls "mortals"))

-- true

-- O motor deriva que todo grego é mortal, que é o silogismo BARBARA,
-- encadeando as duas premissas pela transitividade.

-- Perguntado sobre uma classe, o motor conta tudo que sabe dela.

def tellAbout (kb : KB) (a : Class) : List Statement :=
  let sub := subsetRel kb
  (supersets a kb).filterMap (fun b =>
    if b = a then none
    else match b with
         | .cls _ => some (.allAre a b)
         | .opp n => some (.noneAre a (.cls n)))
  ++ (nsupersets a kb).filterMap (fun b =>
    match b with
    | .opp n =>
        if b = a || sub.contains (a, .cls n) then none
        else some (.someAre a (.cls n))
    | .cls n =>
        if b = a || sub.contains (a, .opp n) then none
        else some (.someAreNot a b))

#eval (tellAbout kb0 (.cls "greeks")).map toString

-- ["All greeks are humans.", "All greeks are mortals.", "Some greeks are philosophers."]

-- ## A interface em língua natural

-- Falta ligar o motor à língua. São três peças: reconhecer uma sentença
-- escrita, incorporá-la à base, e responder a uma pergunta.

-- O reconhecimento é direto porque o fragmento é minúsculo. Primeiro se
-- normaliza a entrada — tudo em minúsculas, descartando o que vier depois da
-- primeira pontuação, e quebrando em palavras.

def preprocess (line : String) : List String :=
  let kept := line.toList.takeWhile
    (fun c => c.isAlpha || c.isWhitespace)
  (String.mk kept).toLower.splitOn " "
    |>.filter (fun w => w ≠ "")

-- Depois se casa a lista de palavras contra as produções da gramática. Uma
-- entrada é ou uma afirmação, que muda a base, ou uma pergunta, que a
-- consulta.

inductive Input where
  | stmt (s : Statement)
  | query (q : Query)
  deriving Repr

def parse (line : String) : Option Input :=
  match preprocess line with
  | ["all", a, "are", b] =>
      some (.stmt (.allAre (.cls a) (.cls b)))
  | ["no", a, "are", b] =>
      some (.stmt (.noneAre (.cls a) (.cls b)))
  | ["some", a, "are", "not", b] =>
      some (.stmt (.someAreNot (.cls a) (.cls b)))
  | ["some", a, "are", b] =>
      some (.stmt (.someAre (.cls a) (.cls b)))
  | ["are", "all", a, b] =>
      some (.query (.areAll (.cls a) (.cls b)))
  | ["are", "no", a, b] =>
      some (.query (.areNone (.cls a) (.cls b)))
  | ["are", "any", a, "not", b] =>
      some (.query (.anyNot (.cls a) (.cls b)))
  | ["are", "any", a, b] =>
      some (.query (.areAny (.cls a) (.cls b)))
  | ["what", "about", a] =>
      some (.query (.whatAbout (.cls a)))
  | ["how", "about", a] =>
      some (.query (.whatAbout (.cls a)))
  | _ => none

-- Note a ordem dos casos: `some A are not B` tem de vir antes de
-- `some A are B`, senão a lista de quatro palavras nunca é alcançada. É a
-- mesma cautela que qualquer gramática com prefixo comum exige.

#eval (parse "All bears are mammals.").isSome

-- true

-- Incorporar uma afirmação à base tem três desfechos, e a distinção entre
-- eles é o que dá ao motor alguma inteligência. A afirmação pode contradizer
-- o que já se sabe, e aí é recusada; pode já ser derivável, e aí não
-- acrescenta nada; ou é nova, e entra.

inductive Outcome where
  | inconsistent
  | known
  | added (kb : KB)
  deriving Repr

def update (st : Statement) (kb : KB) : Outcome :=
  match st with
  | .allAre a b =>
      if (nsupersets a kb).contains b then .inconsistent
      else if (supersets a kb).contains b then .known
      else .added ((a, b, true) :: kb)
  | .noneAre a b =>
      let b' := b.opposite
      if (nsupersets a kb).contains b' then .inconsistent
      else if (supersets a kb).contains b' then .known
      else .added ((a, b', true) :: kb)
  | .someAre a b =>
      let b' := b.opposite
      if (supersets a kb).contains b' then .inconsistent
      else if (nsupersets a kb).contains b' then .known
      else .added ((a, b', false) :: kb)
  | .someAreNot a b =>
      if (supersets a kb).contains b then .inconsistent
      else if (nsupersets a kb).contains b then .known
      else .added ((a, b, false) :: kb)

-- Uma base se constrói a partir de uma lista de afirmações, incorporando uma
-- a uma e recusando o conjunto todo se alguma contradizer as anteriores.

def makeKB : List Statement → Option KB :=
  let rec go (kb : KB) : List Statement → Option KB
    | [] => some kb
    | st :: sts =>
        match update st kb with
        | .inconsistent => none
        | .known => go kb sts
        | .added kb' => go kb' sts
  go []

def process (text : String) : Option KB := do
  let sts ← (text.splitOn "\n").filter (fun l => l ≠ "")
    |>.mapM (fun l =>
        match parse l with
        | some (.stmt st) => some st
        | _ => none)
  makeKB sts

-- Um texto de exemplo, e a base que ele produz:

def mytxt : String :=
  "all bears are mammals\n" ++
  "no owls are mammals\n" ++
  "some bears are stupids\n" ++
  "all men are humans\n" ++
  "no men are women\n" ++
  "all women are humans\n" ++
  "all humans are mammals\n" ++
  "some men are stupids\n" ++
  "some men are not stupids"

def kb1 : KB := (process mytxt).getD []

#eval kb1.length

-- 9

-- Para responder a uma pergunta, o motor tenta derivá-la; se não conseguir,
-- tenta derivar sua negação. Só se as duas falharem é que ele admite não
-- saber. A negação de uma pergunta é sua diagonal no quadrado das oposições.

def Query.neg : Query → Query
  | .areAll a b => .anyNot a b
  | .areNone a b => .areAny a b
  | .areAny a b => .areNone a b
  | .anyNot a b => .areAll a b
  | .whatAbout a => .whatAbout a

def respond (kb : KB) : Input → String
  | .query (.whatAbout a) =>
      match tellAbout kb a, tellAbout kb a.opposite with
      | [], [] => "No info."
      | [], neg =>
          String.intercalate "\n" (neg.map toString)
      | pos, _ => String.intercalate "\n" (pos.map toString)
  | .query q =>
      if derive kb q then "Yes."
      else if derive kb q.neg then "No."
      else "I don't know."
  | .stmt st =>
      match update st kb with
      | .inconsistent => "Inconsistent with my info."
      | .known => "I knew that already."
      | .added _ => "OK."

#eval (parse "Are all bears mammals?").map (respond kb1)

-- some "Yes."

#eval (parse "Are any owls bears?").map (respond kb1)

-- some "No."

#eval (parse "What about men?").map (respond kb1)

-- some
--   "No men are women.\nAll men are humans.\nAll men are mammals.\nNo men are owls.\nSome men are not stupids.\nSome men are stupids."

-- O `respond` é a conversa inteira, menos o laço: dada uma base e uma linha,
-- ele produz a resposta. O que falta para um programa interativo é ler da
-- entrada, guardar a base atualizada e repetir — e isso é `IO`, não
-- semântica.

-- ### Exercise (2 stars): inconsistent-kb ⭐⭐

-- O que acontece se a base receber uma afirmação que contradiz o que já sabe?
-- Construa o caso e confira.

example :
    process "all bears are mammals\nno bears are mammals"
      = none := sorry

-- ## A validade dos silogismos, demonstrada

-- O motor acima **decide** se uma conclusão se segue de uma base: ele
-- responde `true` ou `false`, e a resposta se confere rodando. Mas a validade
-- de um silogismo é uma afirmação sobre todas as interpretações possíveis das
-- classes, e essa é uma afirmação que se demonstra.

-- Lido sobre conjuntos, "todo A é B" é `A ⊆ B`, e o silogismo BARBARA é a
-- transitividade da inclusão.

theorem barbara {α : Type} (A B C : Set α)
    (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C :=
  fun _ hx => h₂ (h₁ hx)

-- O silogismo CELARENT — de "nenhum B é C" e "todo A é B" conclui-se "nenhum
-- A é C" — é a mesma transitividade, com o complemento no lugar da segunda
-- classe.

theorem celarent {α : Type} (A B C : Set α)
    (h₁ : B ⊆ Cᶜ) (h₂ : A ⊆ B) : A ⊆ Cᶜ :=
  fun _ hx => h₁ (h₂ hx)

-- E DARII — de "todo B é C" e "algum A é B" conclui-se "algum A é C" —
-- precisa da testemunha, e é onde o importe existencial aparece como um
-- habitante exibido.

theorem darii {α : Type} (A B C : Set α)
    (h₁ : B ⊆ C) (h₂ : ∃ x, x ∈ A ∧ x ∈ B) :
    ∃ x, x ∈ A ∧ x ∈ C := by
  obtain ⟨x, hA, hB⟩ := h₂
  exact ⟨x, hA, h₁ hB⟩

-- Repare no que muda de estatuto. Para o motor, "BARBARA vale" é uma resposta
-- que se obtém rodando `derive` numa base concreta. Aqui é um teorema sobre
-- quaisquer `A`, `B` e `C`, e a prova é a mesma para todos eles.

-- ### Exercise (2 stars): ferio ⭐⭐

-- FERIO conclui "algum A não é C" de "nenhum B é C" e "algum A é B". Enuncie
-- e demonstre.

theorem ferio {α : Type} (A B C : Set α)
    (h₁ : B ⊆ Cᶜ) (h₂ : ∃ x, x ∈ A ∧ x ∈ B) :
    ∃ x, x ∈ A ∧ x ∉ C := sorry

end InfEngine

