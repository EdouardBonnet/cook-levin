import Lax429075Proofs.AbsoluteTape

namespace Lax429075Proofs.AbsoluteTape

open Turing Lax554803.MachineModels Lax554803.PolynomialTime

lemma absorbing_iterate (M : SingleTape) (n : ℕ) {c d : TM0.Cfg M.Γ M.Q}
    (h : (fun q : Option (TM0.Cfg M.Γ M.Q) => q.bind (TM0.step M.transition))^[n]
      (some c) = some d) : (absorbing M)^[n] c = d := by
  induction n generalizing c with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hs : TM0.step M.transition c with
    | none =>
      have hn : (fun q : Option (TM0.Cfg M.Γ M.Q) => q.bind (TM0.step M.transition))^[n]
          none = none := Function.iterate_fixed rfl n
      simp only [Option.bind_some, hs, hn, reduceCtorEq] at h
    | some e =>
      have he : (fun q : Option (TM0.Cfg M.Γ M.Q) => q.bind (TM0.step M.transition))^[n]
          (some e) = some d := by simpa only [Option.bind_some, hs] using h
      simpa only [absorbing, hs, Option.getD_some] using ih he

lemma absorbing_at_time (M : SingleTape) {c d : TM0.Cfg M.Γ M.Q} {T N : ℕ}
    (h : StateTransition.EvalsToInTime (TM0.step M.transition) c (some d) T)
    (hd : TM0.step M.transition d = none) (hN : T ≤ N) :
    (absorbing M)^[N] c = d := by
  have hp := absorbing_iterate M h.steps h.evals_in_steps
  have ht : h.steps ≤ N := h.steps_le_m.trans hN
  rw [show N = (N - h.steps) + h.steps from (Nat.sub_add_cancel ht).symm,
    Function.iterate_add_apply, hp]
  exact Function.iterate_fixed (by simp [absorbing, hd]) _

def initial (M : SingleTape) (w : Word) : Cfg M :=
  ⟨default, 0, fun j => if 0 ≤ j then ((w[j.toNat]?).map M.input).getD default else default⟩

lemma initial_matches (M : SingleTape) (w : Word) :
    Matches M (initial M w) (TM0.init (w.map M.input)) := by
  refine ⟨rfl, ?_⟩
  intro j
  cases j with
  | ofNat n => simp [initial, TM0.init, Tape.mk₁, Tape.mk₂, ListBlank.nth_mk, List.getI]
  | negSucc n => simp [initial, TM0.init, Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk', ListBlank.nth_mk]

lemma run_accepts (M : SingleTape) (w : Word) (d : TM0.Cfg M.Γ M.Q) (T : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M.transition) (TM0.init (w.map M.input))
      (some d) T) (hd : TM0.step M.transition d = none) :
    M.accept ((next M)^[T] (initial M w)).state = M.accept d.q := by
  have hm := iterate_matches M _ _ (initial_matches M w) T
  rw [absorbing_at_time M h hd le_rfl] at hm
  exact congrArg M.accept hm.1

end Lax429075Proofs.AbsoluteTape
