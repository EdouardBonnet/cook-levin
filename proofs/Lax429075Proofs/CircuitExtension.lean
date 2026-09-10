import Lax429075Proofs.CircuitSemantics

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

def gateValue (g : Gate) (ρ : Assignment) (i : ℕ) : Bool :=
  match g with
  | .input => ρ i
  | .constant b => b
  | .neg a => !(ρ a)
  | .conj a b => ρ a && ρ b
  | .disj a b => ρ a || ρ b

def extendAll (start : ℕ) (gates : List Gate) (ρ : Assignment) : Assignment :=
  match gates with
  | [] => ρ
  | g :: gs => extendAll (start + 1) gs (Function.update ρ start (gateValue g ρ start))

lemma extendAll_before (start : ℕ) (gates : List Gate) (ρ : Assignment) (j : ℕ) (hj : j < start) :
    extendAll start gates ρ j = ρ j := by
  induction gates generalizing start ρ with
  | nil => rfl
  | cons g gs ih =>
    rw [extendAll, ih (start + 1) _ (by omega)]
    exact Function.update_of_ne (by omega) _ _

lemma gate_satisfied (g : Gate) (ρ σ : Assignment) (i : ℕ)
    (hv : σ i = gateValue g ρ i) (hi : ∀ j ∈ g.inputs, σ j = ρ j) :
    g.check σ i = true := by
  cases g with
  | input => rfl
  | constant b => simp_all [gateValue, Gate.check]
  | neg a =>
    have ha := hi a (by simp [Gate.inputs])
    simp_all [gateValue, Gate.check]
  | conj a b | disj a b =>
    have ha := hi a (by simp [Gate.inputs])
    have hb := hi b (by simp [Gate.inputs])
    simp_all [gateValue, Gate.check]

lemma ordered_cons (start : ℕ) (g : Gate) (gs : List Gate) (h : Ordered start (g :: gs)) :
    (∀ j ∈ g.inputs, j < start) ∧ Ordered (start + 1) gs := by
  constructor
  · exact fun j hj => h g start (by simp) j hj
  · intro q i hq j hj
    exact h q i (by simp [hq]) j hj

lemma extendAll_satisfies (start : ℕ) (gates : List Gate) (ρ : Assignment) (h : Ordered start gates) :
    Satisfies start gates (extendAll start gates ρ) := by
  induction gates generalizing start ρ with
  | nil => simp [Satisfies]
  | cons g gs ih =>
    obtain ⟨hhead, htail⟩ := ordered_cons start g gs h
    let first := Function.update ρ start (gateValue g ρ start)
    have ht := ih (start + 1) first htail
    have hv : extendAll (start + 1) gs first start = gateValue g ρ start := by
      rw [extendAll_before _ _ _ _ (by omega)]
      exact Function.update_self _ _ _
    have hi (j : ℕ) (hj : j ∈ g.inputs) : extendAll (start + 1) gs first j = ρ j := by
      have hj' := hhead j hj
      rw [extendAll_before _ _ _ _ (by omega)]
      exact Function.update_of_ne (by omega) _ _
    have hg := gate_satisfied g ρ (extendAll (start + 1) gs first) start hv hi
    intro q i hq
    have hm : (q, i) = (g, start) ∨ (q, i) ∈ gs.zipIdx (start + 1) := by simpa using hq
    rcases hm with he | hm
    · cases he
      exact hg
    · exact ht q i hm

lemma expr_agrees (e : Expr) (n : ℕ) (ρ σ : Assignment) (h : e.Bounded n)
    (ha : ∀ j < n, ρ j = σ j) : e.eval ρ = e.eval σ := by
  induction e with
  | wire i => exact ha i h
  | constant b => rfl
  | neg e ih => simp only [Expr.eval, ih h]
  | conj e f ihe ihf | disj e f ihe ihf => simp only [Expr.eval, ihe h.1, ihf h.2]

lemma compile_complete (start : ℕ) (e : Expr) (ρ : Assignment) (h : e.Bounded start) :
    ∃ σ, (∀ j < start, σ j = ρ j) ∧ Satisfies start (compile start e).gates σ ∧
      σ (compile start e).output = e.eval ρ := by
  let σ := extendAll start (compile start e).gates ρ
  have ha := extendAll_before start (compile start e).gates ρ
  have hs := extendAll_satisfies start (compile start e).gates ρ (compile_ordered start e h)
  refine ⟨σ, ha, hs, ?_⟩
  exact (compile_sound start e σ hs).trans (expr_agrees e start σ ρ h ha)

end Lax429075Proofs.CircuitBuilder
