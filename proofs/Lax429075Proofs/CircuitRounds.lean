import Lax429075Proofs.CircuitVectors

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

def compileRounds {n : ℕ} (start : ℕ) (es : Fin n → Expr) : ℕ → (Fin n → ℕ) → VectorBlock n
  | 0, v => ⟨[], v⟩
  | t + 1, v =>
    let b := compileLayer start es v
    let c := compileRounds (start + b.gates.length) es t b.outputs
    ⟨b.gates ++ c.gates, c.outputs⟩

lemma compileRounds_length {n : ℕ} (start : ℕ) (es : Fin n → Expr) (t : ℕ) (v : Fin n → ℕ) :
    (compileRounds start es t v).gates.length = t * layerCost es := by
  induction t generalizing start v with
  | zero => simp [compileRounds]
  | succ t ih => simp [compileRounds, ih, compileLayer_length, Nat.succ_mul, Nat.add_comm]

lemma compileRounds_ordered {n : ℕ} (start : ℕ) (es : Fin n → Expr) (t : ℕ) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (hv : ∀ i, v i < start) :
    Ordered start (compileRounds start es t v).gates := by
  induction t generalizing start v with
  | zero => simp [compileRounds, Ordered]
  | succ t ih =>
    have hb := compileLayer_bounded start es v he hv
    refine ordered_append start _ _ (compileVector_ordered start _ hb) (ih _ _ ?_)
    exact compileVector_output start _ hb

lemma compileRounds_output {n : ℕ} (start : ℕ) (es : Fin n → Expr) (t : ℕ) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (hv : ∀ i, v i < start) (i : Fin n) :
    (compileRounds start es t v).outputs i < start + (compileRounds start es t v).gates.length := by
  induction t generalizing start v with
  | zero => exact hv i
  | succ t ih =>
    have hb := compileLayer_bounded start es v he hv
    have hh := ih (start + (compileLayer start es v).gates.length) (compileLayer start es v).outputs
      (compileVector_output start _ hb)
    simpa only [compileRounds, List.length_append, Nat.add_assoc] using hh

lemma compileRounds_sound {n : ℕ} (start : ℕ) (es : Fin n → Expr) (t : ℕ) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (ρ : Assignment)
    (h : Satisfies start (compileRounds start es t v).gates ρ) :
    (fun i => ρ ((compileRounds start es t v).outputs i)) =
      (evaluateLayer es)^[t] (fun i => ρ (v i)) := by
  induction t generalizing start v with
  | zero => rfl
  | succ t ih =>
    obtain ⟨hb, hc⟩ := (satisfies_append start _ _ ρ).mp h
    have hs := compileLayer_sound start es v he ρ hb
    have hh := ih _ _ hc
    simpa only [compileRounds, hs, Function.iterate_succ_apply] using hh

lemma compileRounds_complete {n : ℕ} (start : ℕ) (es : Fin n → Expr) (t : ℕ) (v : Fin n → ℕ)
    (he : ∀ i, (es i).Bounded n) (hv : ∀ i, v i < start) (ρ : Assignment) :
    ∃ σ, (∀ j < start, σ j = ρ j) ∧ Satisfies start (compileRounds start es t v).gates σ ∧
      (fun i => σ ((compileRounds start es t v).outputs i)) =
        (evaluateLayer es)^[t] (fun i => ρ (v i)) := by
  let σ := extendAll start (compileRounds start es t v).gates ρ
  have ha := extendAll_before start (compileRounds start es t v).gates ρ
  have hs := extendAll_satisfies start (compileRounds start es t v).gates ρ
    (compileRounds_ordered start es t v he hv)
  refine ⟨σ, ha, hs, ?_⟩
  have hh := compileRounds_sound start es t v he σ hs
  have hi : (fun i => σ (v i)) = (fun i => ρ (v i)) := by funext i; exact ha _ (hv i)
  rw [hi] at hh
  exact hh

end Lax429075Proofs.CircuitBuilder
