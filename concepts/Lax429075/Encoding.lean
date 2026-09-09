import Lax429075.CNF

/-!
---
title: Binary encoding of CNF formulas
type: definition
---
Lists use a one-bit continuation marker and a zero-bit terminator.
A literal consists of its variable index in unary, a zero terminator, and
its sign. This encoding gives every formula a unique binary word and bounds
each variable index by the word length.
-/

namespace Lax429075.Encoding

open CNF Lax434930.PolynomialTime

def encodeList {α : Type} (encode : α → Word) : List α → Word
  | [] => [false]
  | a :: as => true :: (encode a ++ encodeList encode as)

def encodeNat (n : ℕ) : Word := List.replicate n true ++ [false]

def encodeLiteral (l : Literal) : Word := encodeNat l.variable ++ [l.positive]

def encodeClause : Clause → Word := encodeList encodeLiteral

def encodeCNF : Formula → Word := encodeList encodeClause

def parseNat : Word → Option (ℕ × Word)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => do
    let (n, rest) ← parseNat w
    pure (n + 1, rest)

def parseLiteral (w : Word) : Option (Literal × Word) := do
  let (n, rest) ← parseNat w
  match rest with
  | [] => none
  | sign :: tail => pure (⟨n, sign⟩, tail)

def parseList {α : Type} (parse : Word → Option (α × Word)) :
    ℕ → Word → Option (List α × Word)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: w => some ([], w)
  | fuel + 1, true :: w => do
    let (a, rest) ← parse w
    let (as, tail) ← parseList parse fuel rest
    pure (a :: as, tail)

def parseClause (w : Word) : Option (Clause × Word) := parseList parseLiteral w.length w

def decodeCNF (w : Word) : Option Formula := do
  let (F, rest) ← parseList parseClause w.length w
  if rest = [] then pure F else none

end Lax429075.Encoding
