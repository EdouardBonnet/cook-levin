import Lax429075.SAT

/-!
---
title: Correctness of the SAT verifier
type: lemma
---
Membership in SAT is equivalent to the existence of an accepted certificate
of length at most the input length.
-/

namespace Lax429075.VerifierCorrect

open SAT Lax434930.PolynomialTime Lax434930.Certificates

axiom correct (w : Word) :
  w ∈ SAT ↔ ∃ y : Word, y.length ≤ w.length ∧ pair w y ∈ Verifier

end Lax429075.VerifierCorrect
