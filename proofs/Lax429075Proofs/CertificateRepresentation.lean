import Lax429075Proofs.CertificateAssignments

namespace Lax429075Proofs.CertificateCircuit

open Lax434930.PolynomialTime Lax429075.CNF Lax429075.Satisfiability

def Represents (bound : ℕ) (ρ : Assignment) (y : Word) : Prop :=
  y.length ≤ bound ∧ (∀ i, live bound ρ i = true ↔ i < y.length) ∧
    (∀ i, i < y.length → y[i]? = some (ρ (dataPort i)))

lemma assignment_represents (bound : ℕ) (y : Word) (hy : y.length ≤ bound) :
    Represents bound (certificateAssignment bound y) y := by
  refine ⟨hy, ?_, ?_⟩
  · intro i
    rw [certificateAssignment_live bound y hy]
    simp
  · intro i hi
    rw [certificateAssignment_data bound y i (by omega)]
    simp [assignment, hi]

lemma represents_agrees (bound : ℕ) (ρ σ : Assignment) (y : Word) (h : Represents bound ρ y)
    (ha : ∀ i < inputCount bound, σ i = ρ i) : Represents bound σ y := by
  refine ⟨h.1, ?_, ?_⟩
  · intro i
    have he : live bound σ i = live bound ρ i := by
      by_cases hi : i < bound
      · simp only [live, hi, if_true]
        exact ha _ (by simp only [livePort, inputCount]; omega)
      · simp [live, hi]
    rw [he]
    exact h.2.1 i
  · intro i hi
    rw [ha _ (by have hb := h.1; simp only [dataPort, inputCount]; omega)]
    exact h.2.2 i hi

end Lax429075Proofs.CertificateCircuit
