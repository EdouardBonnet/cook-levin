import Lax429075Proofs.ExpressionOperations

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime

variable {I : Type}

def Expression.select (n : Number I) : List (Expression I) → Expression I → Expression I
  | [], fallback => fallback
  | e :: es, fallback => Expression.choose (Test.eq n (.constant 0)) e
      (Expression.select (n.sub (.constant 1)) es fallback)

lemma Expression.select_value (n : Number I) (es : List (Expression I)) (fallback : Expression I)
    (a : I → Word) :
    (Expression.select n es fallback).value a =
      ((es[n.value a]?).getD fallback).value a := by
  induction es generalizing n with
  | nil => rfl
  | cons e es ih =>
    simp only [select, Expression.choose, Test.eq_value, Number.constant, decide_eq_true_eq]
    cases hn : n.value a with
    | zero => simp [hn]
    | succ k => simpa only [Nat.add_one_ne_zero, ite_false, ih, Number.sub, Number.constant, hn,
        Nat.add_sub_cancel, List.getElem?_cons_succ]

lemma Expression.select_cost (n : Number I) (es : List (Expression I)) (fallback : Expression I)
    (a : I → Word) (width : ℕ) (hf : (fallback.value a).cost = width)
    (he : ∀ e ∈ es, (e.value a).cost = width) :
    ((Expression.select n es fallback).value a).cost = width := by
  rw [Expression.select_value]
  cases h : es[n.value a]? with
  | none => exact hf
  | some e =>
    exact he e (List.mem_of_getElem? h)

end Lax429075Proofs.Streaming
