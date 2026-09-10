import Lax429075Proofs.CircuitExtension

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits Lax429075.CNF

def Expr.rename (f : ℕ → ℕ) : Expr → Expr
  | .wire i => .wire (f i)
  | .constant b => .constant b
  | .neg a => .neg (a.rename f)
  | .conj a b => .conj (a.rename f) (b.rename f)
  | .disj a b => .disj (a.rename f) (b.rename f)

lemma eval_rename (f : ℕ → ℕ) (ρ : Assignment) (e : Expr) :
    (e.rename f).eval ρ = e.eval (ρ ∘ f) := by
  induction e <;> simp_all [Expr.rename, Expr.eval]

lemma cost_rename (f : ℕ → ℕ) (e : Expr) : (e.rename f).cost = e.cost := by
  induction e <;> simp_all [Expr.rename, Expr.cost]

lemma bounded_rename (f : ℕ → ℕ) (e : Expr) (n m : ℕ)
    (h : e.Bounded n) (hf : ∀ i < n, f i < m) : (e.rename f).Bounded m := by
  induction e with
  | wire i => exact hf i h
  | constant b => trivial
  | neg e ih => exact ih h
  | conj e g ihe ihg | disj e g ihe ihg => exact ⟨ihe h.1, ihg h.2⟩

def anyExpr : List Expr → Expr
  | [] => .constant false
  | e :: es => .disj e (anyExpr es)

def allExpr : List Expr → Expr
  | [] => .constant true
  | e :: es => .conj e (allExpr es)

lemma anyExpr_eval (es : List Expr) (ρ : Assignment) : (anyExpr es).eval ρ = es.any (Expr.eval ρ) := by
  induction es <;> simp_all [anyExpr, Expr.eval]

lemma allExpr_eval (es : List Expr) (ρ : Assignment) : (allExpr es).eval ρ = es.all (Expr.eval ρ) := by
  induction es <;> simp_all [allExpr, Expr.eval]

lemma anyExpr_bounded (es : List Expr) (n : ℕ) (h : ∀ e ∈ es, e.Bounded n) :
    (anyExpr es).Bounded n := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp), ih (by intro a ha; exact h a (by simp [ha]))⟩

lemma allExpr_bounded (es : List Expr) (n : ℕ) (h : ∀ e ∈ es, e.Bounded n) :
    (allExpr es).Bounded n := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp), ih (by intro a ha; exact h a (by simp [ha]))⟩

lemma anyExpr_cost (es : List Expr) : (anyExpr es).cost = (es.map Expr.cost).sum + es.length + 1 := by
  induction es <;> simp_all [anyExpr, Expr.cost] <;> omega

lemma allExpr_cost (es : List Expr) : (allExpr es).cost = (es.map Expr.cost).sum + es.length + 1 := by
  induction es <;> simp_all [allExpr, Expr.cost] <;> omega

end Lax429075Proofs.CircuitBuilder
