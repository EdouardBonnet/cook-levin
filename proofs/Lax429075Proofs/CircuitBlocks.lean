import Lax429075Proofs.CircuitExpressionLists

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

structure Block where
  gates : List Gate
  outputs : List ℕ

def compileMany (start : ℕ) : List Expr → Block
  | [] => ⟨[], []⟩
  | e :: es =>
    let f := compile start e
    let b := compileMany (start + f.gates.length) es
    ⟨f.gates ++ b.gates, f.output :: b.outputs⟩

lemma compileMany_length (start : ℕ) (es : List Expr) :
    (compileMany start es).gates.length = (es.map Expr.cost).sum := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp [compileMany, compile_length, ih]

lemma compileMany_outputs_length (start : ℕ) (es : List Expr) :
    (compileMany start es).outputs.length = es.length := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp [compileMany, ih]

lemma compileMany_ordered (start : ℕ) (es : List Expr) (h : ∀ e ∈ es, e.Bounded start) :
    Ordered start (compileMany start es).gates := by
  induction es generalizing start with
  | nil => simp [compileMany, Ordered]
  | cons e es ih =>
    apply ordered_append start _ _ (compile_ordered start e (h e (by simp)))
    apply ih
    intro a ha
    exact bounded_mono a (h a (by simp [ha])) (Nat.le_add_right _ _)

lemma compileMany_outputs_bound (start : ℕ) (es : List Expr) (h : ∀ e ∈ es, e.Bounded start)
    (i : ℕ) (hi : i ∈ (compileMany start es).outputs) :
    i < start + (compileMany start es).gates.length := by
  induction es generalizing start with
  | nil => simp [compileMany] at hi
  | cons e es ih =>
    have hm : i = (compile start e).output ∨
        i ∈ (compileMany (start + (compile start e).gates.length) es).outputs := by
      simpa only [compileMany, List.mem_cons] using hi
    rcases hm with rfl | hm
    · have hh := compile_output start e (h e (by simp))
      simp only [compileMany, List.length_append]
      omega
    · have hh := ih (start + (compile start e).gates.length)
        (fun a ha => bounded_mono a (h a (by simp [ha])) (Nat.le_add_right _ _)) hm
      simp only [compileMany, List.length_append]
      omega

lemma compileMany_sound (start : ℕ) (es : List Expr) (ρ : Assignment)
    (h : Satisfies start (compileMany start es).gates ρ) :
    (compileMany start es).outputs.map ρ = es.map (Expr.eval ρ) := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hf, hb⟩ := (satisfies_append start _ _ ρ).mp h
    have he := compile_sound start e ρ hf
    have hs := ih _ hb
    simpa [compileMany, he] using congrArg (List.cons (e.eval ρ)) hs

lemma compileMany_complete (start : ℕ) (es : List Expr) (ρ : Assignment)
    (h : ∀ e ∈ es, e.Bounded start) :
    ∃ σ, (∀ j < start, σ j = ρ j) ∧ Satisfies start (compileMany start es).gates σ ∧
      (compileMany start es).outputs.map σ = es.map (Expr.eval ρ) := by
  let σ := extendAll start (compileMany start es).gates ρ
  have ha := extendAll_before start (compileMany start es).gates ρ
  have hs := extendAll_satisfies start (compileMany start es).gates ρ (compileMany_ordered start es h)
  refine ⟨σ, ha, hs, (compileMany_sound start es σ hs).trans ?_⟩
  apply List.map_congr_left
  intro e he
  exact expr_agrees e start σ ρ (h e he) ha

end Lax429075Proofs.CircuitBuilder
