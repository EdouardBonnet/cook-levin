import Lax429075.Satisfiability

/-!
---
title: A bounded satisfying assignment
type: lemma
---
A satisfiable formula has a certificate whose length is at most the length
of its binary encoding. Only variables occurring in the formula matter.
-/

namespace Lax429075.FiniteWitness

open CNF Encoding Satisfiability Lax434930.PolynomialTime

axiom bounded (F : Formula) :
  Satisfiable F ↔ ∃ y : Word, y.length ≤ (encodeCNF F).length ∧ eval F (assignment y) = true

end Lax429075.FiniteWitness
