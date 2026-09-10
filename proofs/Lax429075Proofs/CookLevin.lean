import Lax429075.CircuitMachine
import Lax429075.TseitinCorrect
import Lax429075.SATEncoding
import Lax429075.SATinNP
import Lax429075.SATHard
import Lax429075.CookLevin

namespace Lax429075Proofs

open Lax429075 Lax429075.Satisfiability Lax429075.Encoding Lax429075.Reductions
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/--
---
conclusion: Lax429075.SATHard.hardness
assumptions:
  - Lax429075.CircuitMachine.compile
  - Lax429075.SATEncoding.correct
  - Lax429075.TseitinCorrect.correct
---
Compile the verifier, impose the gate clauses, and encode the resulting formula.
-/
lemma sat_hard (A : Language) : A ∈ NP → ManyOne A SAT := by
  rintro ⟨V, hV, p, hA⟩
  obtain ⟨circuits, htime, hcircuits⟩ := CircuitMachine.compile V hV p
  refine ⟨fun x => encodeCNF (Tseitin.encode (circuits x)), htime, ?_⟩
  intro x
  rw [SATEncoding.correct, TseitinCorrect.correct, hcircuits, hA]

/--
---
conclusion: Lax429075.CookLevin.np_complete
assumptions:
  - Lax429075.SATHard.hardness
  - Lax429075.SATinNP.membership
---
Combine membership in NP with polynomial many-one hardness.
-/
theorem cook_levin : NPComplete SAT :=
  ⟨SATinNP.membership, SATHard.hardness⟩

end Lax429075Proofs
