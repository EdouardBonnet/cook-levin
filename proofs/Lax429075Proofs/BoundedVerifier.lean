import Lax429075Proofs.WindowMachine
import Lax434930.Certificates

namespace Lax429075Proofs.WindowMachine

open Turing Lax434930.MachineModels Lax434930.PolynomialTime Lax434930.Certificates

lemma polynomial_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  intro x y hxy
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simpa only [Polynomial.eval_add] using Nat.add_le_add ihp ihq
  | monomial n c => simp only [Polynomial.eval_monomial]; gcongr

noncomputable def pairedBound (p : Polynomial ℕ) : Polynomial ℕ := 2 * Polynomial.X + p + 1

noncomputable def horizon (p q : Polynomial ℕ) : Polynomial ℕ := q.comp (pairedBound p) + pairedBound p + 1

lemma horizon_time (p q : Polynomial ℕ) (x y : Word) (hy : y.length ≤ p.eval x.length) :
    q.eval (pair x y).length ≤ (horizon p q).eval x.length := by
  have hl : (pair x y).length ≤ (pairedBound p).eval x.length := by
    rw [pair_length]
    simp only [pairedBound, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
    omega
  have h := polynomial_monotone q hl
  dsimp at h
  simp only [horizon, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
  omega

lemma horizon_input (p q : Polynomial ℕ) (x y : Word) (hy : y.length ≤ p.eval x.length) :
    (pair x y).length < (horizon p q).eval x.length := by
  rw [pair_length]
  simp only [horizon, pairedBound, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  omega

lemma run_accepts (M : SingleTape) (radius : ℕ) (w : Word) (d : TM0.Cfg M.Γ M.Q) (T : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M.transition) (TM0.init (w.map M.input)) (some d) T)
    (hd : TM0.step M.transition d = none) (hT : T ≤ radius) :
    M.accept ((next M radius)^[radius] (initial M radius w)).state = M.accept d.q := by
  have hf := run_represents M radius w radius le_rfl
  have ha := AbsoluteTape.iterate_matches M _ _ (AbsoluteTape.initial_matches M w) radius
  rw [AbsoluteTape.absorbing_at_time M h hd hT] at ha
  exact congrArg M.accept (hf.1.trans ha.1)

lemma bounded_verifier (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
    ∃ (M : SingleTape) (R : Polynomial ℕ), ∀ x y : Word, y.length ≤ p.eval x.length →
      (pair x y).length < R.eval x.length ∧
      (M.accept ((next M (R.eval x.length))^[R.eval x.length]
        (initial M (R.eval x.length) (pair x y))).state = true ↔ pair x y ∈ V) := by
  have hS : V ∈ SingleTapeP := by rw [Lax434930.ModelEquivalence.singleTapeP_eq_P]; exact hV
  obtain ⟨M, q, hM⟩ := hS
  refine ⟨M, horizon p q, ?_⟩
  intro x y hy
  obtain ⟨d, ⟨hd⟩, hhalt, haccept⟩ := hM (pair x y)
  refine ⟨horizon_input p q x y hy, ?_⟩
  rw [run_accepts M _ _ d _ hd hhalt (horizon_time p q x y hy)]
  exact haccept

end Lax429075Proofs.WindowMachine
