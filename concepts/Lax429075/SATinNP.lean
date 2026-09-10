import Lax429075.Satisfiability
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: SAT belongs to NP
type: lemma
---
A polynomial time verifier checks a satisfying assignment of polynomial length.
-/

namespace Lax429075.SATinNP

open Satisfiability Lax434930.NondeterministicPolynomialTime

axiom membership : SAT ∈ NP

end Lax429075.SATinNP
