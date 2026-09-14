import Lax429075Proofs.MachineStepExpressions
import Lax429075Proofs.CircuitRounds

namespace Lax429075Proofs.MachineCircuit

open Turing Lax434930.MachineModels
open WindowMachine CircuitBuilder

lemma sum_cost_bound (es : List Expr) (bound : ℕ) (h : ∀ e ∈ es, e.cost ≤ bound) :
    (es.map Expr.cost).sum ≤ es.length * bound := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hh := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

lemma casesList_length (M : SingleTape) (radius : ℕ) :
    (casesList M radius).length = Fintype.card M.Q * (2 * radius + 1) * Fintype.card M.Γ := by
  simp [casesList, List.length_flatMap, Function.comp_def, Nat.mul_assoc]

lemma guard_cost (M : SingleTape) (radius : ℕ) (q : M.Q) (i : Position radius) (a : M.Γ) :
    (guard M radius q i a).cost = 2 := rfl

lemma caseResult_cost (M : SingleTape) (radius : ℕ) (b : Bit M radius)
    (q : M.Q) (i : Position radius) (a : M.Γ) : (caseResult M radius b q i a).cost = 1 := by
  classical
  rcases b with q' | i' | ⟨j, a'⟩
  · rfl
  · rfl
  · unfold caseResult
    cases M.transition q a with
    | none => rfl
    | some p =>
      obtain ⟨r, op⟩ := p
      cases op with
      | move dir => cases dir <;> rfl
      | write c =>
        dsimp only
        split_ifs <;> simp [Expr.cost, wire]

lemma stepExpr_cost (M : SingleTape) (radius : ℕ) (b : Bit M radius) :
    (stepExpr M radius b).cost ≤ 5 * (casesList M radius).length + 1 := by
  unfold stepExpr
  rw [anyExpr_cost]
  have h := sum_cost_bound ((casesList M radius).map fun s =>
    Expr.conj (guard M radius s.1 s.2.1 s.2.2) (caseResult M radius b s.1 s.2.1 s.2.2)) 4 (by
      intro e he
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
      have hs := caseResult_cost M radius b s.1 s.2.1 s.2.2
      simp only [Expr.cost, guard_cost]
      omega)
  simp only [List.length_map] at h ⊢
  omega

lemma machine_layer_cost (M : SingleTape) (radius : ℕ) :
    layerCost (stepExpressions M radius) ≤
      bitCount M radius * (5 * Fintype.card M.Q * (2 * radius + 1) * Fintype.card M.Γ + 1) := by
  have h := sum_cost_bound (List.ofFn (stepExpressions M radius))
    (5 * (casesList M radius).length + 1) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact stepExpr_cost M radius _)
  simpa [layerCost, List.map_ofFn, Function.comp_def, casesList_length, Nat.mul_assoc] using h

lemma machine_rounds_size (M : SingleTape) (radius start t : ℕ) (v : Fin (bitCount M radius) → ℕ) :
    (compileRounds start (stepExpressions M radius) t v).gates.length ≤
      t * bitCount M radius *
        (5 * Fintype.card M.Q * (2 * radius + 1) * Fintype.card M.Γ + 1) := by
  rw [compileRounds_length, Nat.mul_assoc]
  exact Nat.mul_le_mul_left t (machine_layer_cost M radius)

end Lax429075Proofs.MachineCircuit
