import Lax429075Proofs.MachineCircuitSize

namespace Lax429075Proofs.MachineCircuit

open Turing Lax434930.MachineModels
open WindowMachine CircuitBuilder Lax429075.CNF

lemma evaluate_rounds (M : SingleTape) (radius t : ℕ) (c : Cfg M radius) :
    (evaluateLayer (stepExpressions M radius))^[t] (encode M radius c) =
      encode M radius ((next M radius)^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, stepExpressions_eval, Function.iterate_succ_apply']

lemma simulation_sound (M : SingleTape) (radius start t : ℕ) (v : Fin (bitCount M radius) → ℕ)
    (c : Cfg M radius) (ρ : Assignment)
    (hi : (fun i => ρ (v i)) = encode M radius c)
    (hs : Satisfies start (compileRounds start (stepExpressions M radius) t v).gates ρ) :
    (fun i => ρ ((compileRounds start (stepExpressions M radius) t v).outputs i)) =
      encode M radius ((next M radius)^[t] c) := by
  have h := compileRounds_sound start (stepExpressions M radius) t v
    (fun i => stepExpr_bounded M radius _) ρ hs
  rw [hi, evaluate_rounds] at h
  exact h

lemma simulation_complete (M : SingleTape) (radius start t : ℕ) (v : Fin (bitCount M radius) → ℕ)
    (hv : ∀ i, v i < start) (c : Cfg M radius) (ρ : Assignment)
    (hi : (fun i => ρ (v i)) = encode M radius c) :
    ∃ σ, (∀ j < start, σ j = ρ j) ∧
      Satisfies start (compileRounds start (stepExpressions M radius) t v).gates σ ∧
      (fun i => σ ((compileRounds start (stepExpressions M radius) t v).outputs i)) =
        encode M radius ((next M radius)^[t] c) := by
  obtain ⟨σ, hσ, hs, ho⟩ := compileRounds_complete start (stepExpressions M radius) t v
    (fun i => stepExpr_bounded M radius _) hv ρ
  rw [hi, evaluate_rounds] at ho
  exact ⟨σ, hσ, hs, ho⟩

end Lax429075Proofs.MachineCircuit
