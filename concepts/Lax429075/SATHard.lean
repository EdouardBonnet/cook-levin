import Lax429075.SAT
import Lax429075.Reductions

/-!
---
title: NP-hardness of SAT
type: lemma
---
Every language in NP has a polynomial many-one reduction to the binary
language of satisfiable CNF formulas.
-/

namespace Lax429075.SATHard

open SAT Reductions Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

axiom hardness (A : Language) : A ∈ NP → ManyOne A SAT

end Lax429075.SATHard
