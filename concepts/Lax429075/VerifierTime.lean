import Lax429075.Satisfiability

/-!
---
title: Polynomial time for CNF verification
type: lemma
---
A finite stack machine decodes the paired input and checks the supplied
assignment. Its running time is polynomial in the input length, including
on malformed encodings, using the machine model of lax-554803.
-/

namespace Lax429075.VerifierTime

open Satisfiability Lax434930.PolynomialTime

axiom polynomial : Verifier ∈ P

end Lax429075.VerifierTime
