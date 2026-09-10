import Lax434930.PolynomialTime

/-!
---
title: Conjunctive normal form
type: definition
---
A literal names a natural-number variable and its sign. A CNF formula is a
list of clauses, each a list of literals. Empty clauses are false and the
empty conjunction is true. Satisfiability quantifies over Boolean assignments.
-/

namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal
abbrev Formula := List Clause
abbrev Assignment := ℕ → Bool

def Literal.eval (l : Literal) (ρ : Assignment) : Bool :=
  if l.positive then ρ l.index else !(ρ l.index)

def eval (F : Formula) (ρ : Assignment) : Bool :=
  F.all fun C => C.any fun l => l.eval ρ

def Satisfiable (F : Formula) : Prop := ∃ ρ, eval F ρ = true

end Lax429075.CNF
