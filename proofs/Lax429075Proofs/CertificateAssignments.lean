import Lax429075Proofs.CertificatePrefixes

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax429075.CNF Lax429075.Satisfiability CircuitBuilder

def certificateAssignment (bound : ℕ) (y : Word) : Assignment := fun j =>
  if 0 < j ∧ j ≤ bound then assignment y (j - 1)
  else if bound < j ∧ j ≤ 2 * bound then decide (j - (bound + 1) < y.length)
  else false

lemma certificateAssignment_data (bound : ℕ) (y : Word) (i : ℕ) (hi : i < bound) :
    certificateAssignment bound y (dataPort i) = assignment y i := by
  simp [certificateAssignment, dataPort, show i + 1 ≤ bound by omega]

lemma certificateAssignment_live (bound : ℕ) (y : Word) (hy : y.length ≤ bound) (i : ℕ) :
    live bound (certificateAssignment bound y) i = decide (i < y.length) := by
  by_cases hi : i < bound
  · have h₁ : ¬ (0 < bound + i + 1 ∧ bound + i + 1 ≤ bound) := by omega
    have h₂ : bound < bound + i + 1 ∧ bound + i + 1 ≤ 2 * bound := by omega
    have he : bound + i + 1 - (bound + 1) = i := by omega
    simp [live, hi, livePort, certificateAssignment, h₁, h₂, he]
  · have hn : ¬ i < y.length := by omega
    simp [live, hi, hn]

lemma certificateAssignment_prefix (bound : ℕ) (y : Word) (hy : y.length ≤ bound) :
    Prefix bound (certificateAssignment bound y) := by
  intro i _ h
  rw [certificateAssignment_live bound y hy] at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  omega

lemma certificateAssignment_valid (bound : ℕ) (y : Word) (hy : y.length ≤ bound) :
    (prefixExpr bound).eval (certificateAssignment bound y) = true :=
  (prefixExpr_correct bound _).mpr (certificateAssignment_prefix bound y hy)

end Lax429075Proofs.CertificateCircuit
