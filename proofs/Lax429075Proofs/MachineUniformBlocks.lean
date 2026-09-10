import Lax429075Proofs.MachineCircuitRuns

namespace Lax429075Proofs.MachineCircuit

open Lax554803.MachineModels CircuitBuilder

lemma stepExpr_cost_exact (M : SingleTape) (radius : ℕ) (b : Bit M radius) :
    (stepExpr M radius b).cost = 5 * (casesList M radius).length + 1 := by
  simp [stepExpr, anyExpr_cost, List.map_map, Function.comp_def, Expr.cost,
    guard_cost, caseResult_cost, Nat.mul_comm] <;> omega

def blockSize (M : SingleTape) (radius : ℕ) : ℕ :=
  5 * Fintype.card M.Q * (2 * radius + 1) * Fintype.card M.Γ + 1

lemma blockSize_eq (M : SingleTape) (radius : ℕ) :
    blockSize M radius = 5 * (casesList M radius).length + 1 := by
  simp [blockSize, casesList_length, Nat.mul_assoc]

lemma machine_layer_cost_exact (M : SingleTape) (radius : ℕ) :
    layerCost (stepExpressions M radius) = bitCount M radius * blockSize M radius := by
  simp [layerCost, stepExpressions, stepExpr_cost_exact, blockSize_eq]

lemma machine_rounds_size_exact (M : SingleTape) (radius start t : ℕ)
    (v : Fin (bitCount M radius) → ℕ) :
    (compileRounds start (stepExpressions M radius) t v).gates.length =
      t * bitCount M radius * blockSize M radius := by
  rw [compileRounds_length, machine_layer_cost_exact, Nat.mul_assoc]

end Lax429075Proofs.MachineCircuit
