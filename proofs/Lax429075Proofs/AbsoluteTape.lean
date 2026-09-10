import Lax554803.ModelEquivalence
import Mathlib.Tactic

namespace Lax429075Proofs.AbsoluteTape

open Turing Lax554803.MachineModels Lax554803.PolynomialTime

structure Cfg (M : SingleTape) where
  state : M.Q
  head : ℤ
  cells : ℤ → M.Γ

def next (M : SingleTape) (c : Cfg M) : Cfg M :=
  match M.transition c.state (c.cells c.head) with
  | none => c
  | some (q, .move .left) => ⟨q, c.head - 1, c.cells⟩
  | some (q, .move .right) => ⟨q, c.head + 1, c.cells⟩
  | some (q, .write a) => ⟨q, c.head, Function.update c.cells c.head a⟩

def absorbing (M : SingleTape) (c : TM0.Cfg M.Γ M.Q) : TM0.Cfg M.Γ M.Q :=
  (TM0.step M.transition c).getD c

def Matches (M : SingleTape) (a : Cfg M) (c : TM0.Cfg M.Γ M.Q) : Prop :=
  a.state = c.q ∧ ∀ j, a.cells j = c.Tape.nth (j - a.head)

lemma next_matches (M : SingleTape) (a : Cfg M) (c : TM0.Cfg M.Γ M.Q)
    (h : Matches M a c) : Matches M (next M a) (absorbing M c) := by
  have hh : a.cells a.head = c.Tape.head := by simpa using h.2 a.head
  unfold next absorbing
  rw [h.1, hh]
  cases ht : M.transition c.q c.Tape.head with
  | none => simpa [TM0.step, ht] using h
  | some p =>
    obtain ⟨q, op⟩ := p
    cases op with
    | move dir =>
      cases dir <;> simp only [TM0.step, ht, Option.map_some, Option.getD_some, Matches]
      · refine ⟨trivial, ?_⟩
        intro j
        simp only [Tape.move_left_nth]
        convert h.2 j using 1 <;> congr 1 <;> omega
      · refine ⟨trivial, ?_⟩
        intro j
        simp only [Tape.move_right_nth]
        convert h.2 j using 1 <;> congr 1 <;> omega
    | write b =>
      simp only [TM0.step, ht, Option.map_some, Option.getD_some, Matches]
      refine ⟨trivial, ?_⟩
      intro j
      by_cases hj : j = a.head
      · subst j
        simp [Tape.write]
      · simp [Function.update_apply, hj, sub_ne_zero.mpr hj, h.2 j]

lemma iterate_matches (M : SingleTape) (a : Cfg M) (c : TM0.Cfg M.Γ M.Q)
    (h : Matches M a c) (t : ℕ) :
    Matches M ((next M)^[t] a) ((absorbing M)^[t] c) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    simpa only [Function.iterate_succ_apply'] using next_matches M _ _ ih

lemma next_head (M : SingleTape) (c : Cfg M) :
    c.head - 1 ≤ (next M c).head ∧ (next M c).head ≤ c.head + 1 := by
  unfold next
  cases M.transition c.state (c.cells c.head) with
  | none => simp
  | some p =>
    obtain ⟨q, op⟩ := p
    cases op with
    | move dir => cases dir <;> simp <;> omega
    | write b => simp

lemma head_bound (M : SingleTape) (a : Cfg M) (ha : a.head = 0) (t : ℕ) :
    -(t : ℤ) ≤ ((next M)^[t] a).head ∧ ((next M)^[t] a).head ≤ (t : ℤ) := by
  induction t with
  | zero => simp [ha]
  | succ t ih =>
    have h := next_head M ((next M)^[t] a)
    rw [Function.iterate_succ_apply']
    push_cast
    omega

end Lax429075Proofs.AbsoluteTape
