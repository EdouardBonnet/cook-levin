import Lax429075Proofs.VerifierCircuitCorrectness
import Lax429075Proofs.CircuitSizeBounds

namespace Lax429075Proofs.VerifierCircuit

open Lax434930.PolynomialTime Lax434930.Certificates Lax429075
open Lax434930.MachineModels

lemma verifier_circuits (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
    ∃ (M : SingleTape) (R : Polynomial ℕ), ∀ x : Word,
      (Circuits.Satisfiable (circuit M x (p.eval x.length) (R.eval x.length)) ↔
        ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V) ∧
      (circuit M x (p.eval x.length) (R.eval x.length)).gates.length ≤
        (sizePolynomial M p R).eval x.length := by
  obtain ⟨M, R, hM⟩ := WindowMachine.bounded_verifier V hV p
  refine ⟨M, R, ?_⟩
  intro x
  refine ⟨?_, circuit_polynomial_size M p R x⟩
  rw [circuit_correct]
  constructor
  · rintro ⟨y, hy, ha⟩
    exact ⟨y, hy, ((hM x y hy).2).mp ha⟩
  · rintro ⟨y, hy, ha⟩
    exact ⟨y, hy, ((hM x y hy).2).mpr ha⟩

end Lax429075Proofs.VerifierCircuit
