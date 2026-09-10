import Lax429075Proofs.CircuitAddresses

namespace Lax429075Proofs.CircuitBuilder

open Lax429075.Circuits

def foldExpr (conjunction : Bool) (es : List Expr) : Expr :=
  if conjunction then allExpr es else anyExpr es

def foldGate (conjunction : Bool) (a b : ℕ) : Gate :=
  if conjunction then .conj a b else .disj a b

def combineGates (conjunction : Bool) (current : ℕ) : List ℕ → List Gate
  | [] => []
  | a :: as => foldGate conjunction a current :: combineGates conjunction (current + 1) as

lemma combineGates_length (conjunction : Bool) (current : ℕ) (as : List ℕ) :
    (combineGates conjunction current as).length = as.length := by
  induction as generalizing current <;> simp_all [combineGates]

lemma combineGates_append (conjunction : Bool) (current : ℕ) (as bs : List ℕ) :
    combineGates conjunction current (as ++ bs) = combineGates conjunction current as ++
      combineGates conjunction (current + as.length) bs := by
  induction as generalizing current <;> simp_all [combineGates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma foldExpr_cost (conjunction : Bool) (es : List Expr) :
    (foldExpr conjunction es).cost = (es.map Expr.cost).sum + es.length + 1 := by
  cases conjunction <;> simp [foldExpr, anyExpr_cost, allExpr_cost]

lemma compile_fold_output (conjunction : Bool) (start : ℕ) (es : List Expr) :
    (compile start (foldExpr conjunction es)).output = start + (es.map Expr.cost).sum + es.length := by
  have h := compile_last start (foldExpr conjunction es) (by rw [foldExpr_cost]; omega)
  rw [foldExpr_cost] at h
  omega

lemma compile_fold_gates (conjunction : Bool) (start : ℕ) (es : List Expr) :
    (compile start (foldExpr conjunction es)).gates =
      (compileMany start es).gates ++
        (.constant conjunction :: combineGates conjunction (start + (compileMany start es).gates.length)
          (compileMany start es).outputs.reverse) := by
  induction es generalizing start with
  | nil => cases conjunction <;> rfl
  | cons e es ih =>
    have ho := compile_fold_output conjunction (start + (compile start e).gates.length) es
    cases conjunction <;>
      simp only [foldExpr, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] at ih ho ⊢ <;>
      simp only [anyExpr, allExpr, compile, ih, ho, compileMany, List.length_append, List.reverse_cons,
        combineGates_append, combineGates, List.length_reverse, compileMany_outputs_length,
        List.append_nil, List.append_assoc, List.cons_append, List.singleton_append, foldGate,
        Bool.false_eq_true, Bool.true_eq, ite_false, ite_true] <;>
      simp [compileMany_length, Nat.add_assoc]

end Lax429075Proofs.CircuitBuilder
