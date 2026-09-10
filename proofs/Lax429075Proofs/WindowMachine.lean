import Lax429075Proofs.WindowPositions

namespace Lax429075Proofs.WindowMachine

open Turing Lax554803.MachineModels Lax554803.PolynomialTime

structure Cfg (M : SingleTape) (radius : ℕ) where
  state : M.Q
  head : Position radius
  cells : Position radius → M.Γ

def next (M : SingleTape) (radius : ℕ) (c : Cfg M radius) : Cfg M radius :=
  match M.transition c.state (c.cells c.head) with
  | none => c
  | some (q, .move .left) => ⟨q, position radius (coordinate radius c.head - 1), c.cells⟩
  | some (q, .move .right) => ⟨q, position radius (coordinate radius c.head + 1), c.cells⟩
  | some (q, .write a) => ⟨q, c.head, Function.update c.cells c.head a⟩

def Represents (M : SingleTape) (radius : ℕ) (f : Cfg M radius) (a : AbsoluteTape.Cfg M) : Prop :=
  f.state = a.state ∧ coordinate radius f.head = a.head ∧
    ∀ i, f.cells i = a.cells (coordinate radius i)

lemma next_represents (M : SingleTape) (radius : ℕ) (f : Cfg M radius) (a : AbsoluteTape.Cfg M)
    (h : Represents M radius f a) (hb : AbsoluteTape.Inside radius (AbsoluteTape.next M a).head) :
    Represents M radius (next M radius f) (AbsoluteTape.next M a) := by
  have hh : f.cells f.head = a.cells a.head := by rw [h.2.2 f.head, h.2.1]
  unfold next AbsoluteTape.next
  rw [h.1, hh]
  cases ht : M.transition a.state (a.cells a.head) with
  | none => exact h
  | some p =>
    obtain ⟨q, op⟩ := p
    cases op with
    | move dir =>
      cases dir
      · refine ⟨rfl, ?_, h.2.2⟩
        rw [h.2.1]
        exact coordinate_position radius _ (by simpa [AbsoluteTape.next, ht] using hb)
      · refine ⟨rfl, ?_, h.2.2⟩
        rw [h.2.1]
        exact coordinate_position radius _ (by simpa [AbsoluteTape.next, ht] using hb)
    | write b =>
      refine ⟨rfl, h.2.1, ?_⟩
      intro i
      by_cases hi : i = f.head
      · subst i
        simp only [Function.update_self]
        rw [h.2.1]
        simp
      · have hn : coordinate radius i ≠ a.head := by
          rw [← h.2.1]
          exact fun he => hi (coordinate_injective radius he)
        simp [Function.update_of_ne hi, Function.update_of_ne hn, h.2.2 i]

def initial (M : SingleTape) (radius : ℕ) (w : Word) : Cfg M radius :=
  ⟨default, position radius 0, fun i => (AbsoluteTape.initial M w).cells (coordinate radius i)⟩

lemma initial_represents (M : SingleTape) (radius : ℕ) (w : Word) :
    Represents M radius (initial M radius w) (AbsoluteTape.initial M w) := by
  refine ⟨rfl, coordinate_position radius 0 (by simp [AbsoluteTape.Inside]), fun _ => rfl⟩

lemma run_represents (M : SingleTape) (radius : ℕ) (w : Word) (t : ℕ) (ht : t ≤ radius) :
    Represents M radius ((next M radius)^[t] (initial M radius w))
      ((AbsoluteTape.next M)^[t] (AbsoluteTape.initial M w)) := by
  induction t with
  | zero => exact initial_represents M radius w
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    apply next_represents M radius _ _ (ih (by omega))
    have h := AbsoluteTape.inside_mono
      (AbsoluteTape.head_bound M (AbsoluteTape.initial M w) rfl (t + 1)) ht
    simpa only [Function.iterate_succ_apply'] using h

end Lax429075Proofs.WindowMachine
