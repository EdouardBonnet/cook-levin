import Lax429075Proofs.AbsorbingRuns

namespace Lax429075Proofs.AbsoluteTape

open Turing Lax554803.MachineModels Lax554803.PolynomialTime

def Inside (radius : ℕ) (j : ℤ) : Prop := -(radius : ℤ) ≤ j ∧ j ≤ (radius : ℤ)

lemma inside_mono {a b : ℕ} {j : ℤ} (h : Inside a j) (hab : a ≤ b) : Inside b j := by
  dsimp [Inside] at *
  omega

lemma initial_outside (M : SingleTape) (w : Word) (radius : ℕ) (hw : w.length ≤ radius)
    (j : ℤ) (hj : ¬ Inside radius j) : (initial M w).cells j = default := by
  simp only [initial]
  split_ifs with hneg
  · have hi : w.length ≤ j.toNat := by
      dsimp [Inside] at hj
      omega
    simp [List.getElem?_eq_none hi]
  · rfl

lemma next_unchanged (M : SingleTape) (a : Cfg M) (j : ℤ) (hj : j ≠ a.head) :
    (next M a).cells j = a.cells j := by
  unfold next
  cases M.transition a.state (a.cells a.head) with
  | none => rfl
  | some p =>
    obtain ⟨q, op⟩ := p
    cases op with
    | move dir => cases dir <;> rfl
    | write b => exact Function.update_of_ne hj _ _

lemma run_outside (M : SingleTape) (w : Word) (radius t : ℕ)
    (hw : w.length ≤ radius) (ht : t ≤ radius) (j : ℤ) (hj : ¬ Inside radius j) :
    ((next M)^[t] (initial M w)).cells j = default := by
  induction t with
  | zero => exact initial_outside M w radius hw j hj
  | succ t ih =>
    have hh := inside_mono (head_bound M (initial M w) rfl t) (by omega : t ≤ radius)
    have hn : j ≠ ((next M)^[t] (initial M w)).head := by
      intro he
      exact hj (he ▸ hh)
    rw [Function.iterate_succ_apply', next_unchanged M _ j hn]
    exact ih (by omega)

end Lax429075Proofs.AbsoluteTape
