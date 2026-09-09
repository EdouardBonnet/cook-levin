import Lax429075.SAT

/-!
---
title: Polynomial time for CNF verification
type: lemma
---
Decoding a formula and checking a supplied assignment can be implemented
in polynomial time in the paired input length, using the machine model of
lax-554803. This machine construction is an open proof obligation.
-/

namespace Lax429075.VerifierTime

open SAT Lax434930.PolynomialTime

axiom polynomial : Verifier ∈ P

end Lax429075.VerifierTime
