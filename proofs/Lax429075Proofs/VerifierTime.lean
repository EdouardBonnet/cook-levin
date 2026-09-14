import Lax429075Proofs.VerifierExecution
import Lax429075.VerifierTime

namespace Lax429075Proofs

open Lax434930.PolynomialTime Lax429075.Satisfiability
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram VerifierProgram

/--
---
conclusion: Lax429075.VerifierTime.polynomial
assumptions:
---
Decode the pair, evaluate the formula against the certificate, and clear the
work stacks. The finite stack program takes at most $100(n+1)^4$ steps on
every input, including malformed encodings.
-/
lemma verifier_polynomial : Verifier ∈ P := by
  refine ⟨decideVerifier, decideVerifier_correct, ?_⟩
  apply program_polytime program .input .output initial id Computability.encodeBool decideVerifier
    (100 * (Polynomial.X + 1) ^ 4)
  intro w
  simpa [Computability.encodeBool] using program_executes w

end Lax429075Proofs
