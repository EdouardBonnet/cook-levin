import Lax429075Proofs.ExpressionCode

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime CircuitBuilder

variable {I : Type}

def Expression.neg (e : Expression I) : Expression I where
  value a := .neg (e.value a)
  cost := e.cost.add (.constant 1)
  output := (Number.length none).add (e.cost.rename some)
  code :=
    let s : Number (Option I) := .length none
    let lifted := e.rename some
    .append (lifted.run s) ((GateCode.neg (lifted.outputAt s)).code (s.add lifted.cost))
  cost_correct a := by simp [Number.add, Number.constant, e.cost_correct, Expr.cost]
  output_correct a start := by
    simp [Number.add, Number.length, Number.rename, extend_some, extend, e.cost_correct, compile, compile_length]
  correct a start := by
    simp only [Code.eval, Expression.eval_run, GateCode.correct, GateCode.value, Expression.outputAt_value,
      Expression.rename, Number.length, Number.add, Number.rename, extend_some, extend,
      Option.elim_none, List.length_replicate, e.cost_correct]
    simp [compile, gatesWord_append, gatesWord_singleton, compile_length]

def Expression.binary (conjunction : Bool) (e f : Expression I) : Expression I where
  value a := if conjunction then .conj (e.value a) (f.value a) else .disj (e.value a) (f.value a)
  cost := (e.cost.add f.cost).add (.constant 1)
  output := ((Number.length none).add (e.cost.rename some)).add (f.cost.rename some)
  code :=
    let s : Number (Option I) := .length none
    let left := e.rename some
    let right := f.rename some
    let middle := s.add left.cost
    let last := middle.add right.cost
    let gate := if conjunction then GateCode.conj (left.outputAt s) (right.outputAt middle)
      else GateCode.disj (left.outputAt s) (right.outputAt middle)
    .append (.append (left.run s) (right.run middle)) (gate.code last)
  cost_correct a := by
    cases conjunction <;> simp [Number.add, Number.constant, e.cost_correct, f.cost_correct, Expr.cost]
  output_correct a start := by
    cases conjunction <;> simp [Number.add, Number.length, Number.rename, extend_some, extend,
      e.cost_correct, f.cost_correct, compile, compile_length]
  correct a start := by
    cases conjunction <;>
      simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
        Code.eval, Expression.eval_run, GateCode.correct, GateCode.value, Expression.outputAt_value,
        Expression.rename, Number.length, Number.add, Number.rename, extend_some, extend,
        Option.elim_none, List.length_replicate, e.cost_correct, f.cost_correct] <;>
      simp [compile, gatesWord_append, gatesWord_singleton, compile_length, List.append_assoc, Nat.add_assoc]

def Expression.conj (e f : Expression I) : Expression I := Expression.binary true e f

def Expression.disj (e f : Expression I) : Expression I := Expression.binary false e f

end Lax429075Proofs.Streaming
