import Lax429075Proofs.CircuitExpressionLists

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.CNF

def pad : ℕ → Expr → Expr
  | 0, e => e
  | k + 1, e => .conj (pad k e) (.constant true)

lemma pad_eval (k : ℕ) (e : Expr) (ρ : Assignment) : (pad k e).eval ρ = e.eval ρ := by
  induction k <;> simp_all [pad, Expr.eval]

lemma pad_cost (k : ℕ) (e : Expr) : (pad k e).cost = e.cost + 2 * k := by
  induction k <;> simp_all [pad, Expr.cost] <;> omega

lemma pad_bounded (k : ℕ) (e : Expr) (n : ℕ) (h : e.Bounded n) : (pad k e).Bounded n := by
  induction k with
  | zero => exact h
  | succ k ih => exact ⟨ih, trivial⟩

end Lax429075Proofs.CircuitBuilder
