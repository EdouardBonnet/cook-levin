import Lax429075Proofs.OutputGates
import Lax429075Proofs.CircuitAddresses

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime CircuitBuilder

variable {I J : Type}

def Number.bind (n : Number I) (m : Number (Option I)) : Number I where
  value a := m.value (extend a (List.replicate (n.value a) true))
  code := .bind n.code m.code
  correct a := by simp [Code.eval, n.correct, m.correct]

/-- An expression family with a uniform program for its gate clauses.
The additional argument supplies the first available gate address. -/
structure Expression (I : Type) where
  value : (I → Word) → Expr
  cost : Number I
  output : Number (Option I)
  code : Code (Option I)
  cost_correct : ∀ a, cost.value a = (value a).cost
  output_correct : ∀ a start, output.value (extend a (List.replicate start true)) =
    (compile start (value a)).output
  correct : ∀ a start, code.eval (extend a (List.replicate start true)) =
    gatesWord start (compile start (value a)).gates

def Expression.rename (f : I → J) (e : Expression I) : Expression J where
  value a := e.value (a ∘ f)
  cost := e.cost.rename f
  output := e.output.rename (Option.map f)
  code := e.code.rename (Option.map f)
  cost_correct a := e.cost_correct (a ∘ f)
  output_correct a start := by
    simp only [Number.rename, extend_map]
    exact e.output_correct (a ∘ f) start
  correct a start := by
    rw [Code.eval_rename, extend_map]
    exact e.correct (a ∘ f) start

def Expression.outputAt (e : Expression I) (start : Number I) : Number I := start.bind e.output

lemma Expression.outputAt_value (e : Expression I) (start : Number I) (a : I → Word) :
    (e.outputAt start).value a = (compile (start.value a) (e.value a)).output :=
  e.output_correct a (start.value a)

def Expression.run (e : Expression I) (start : Number I) : Code I := .bind start.code e.code

lemma Expression.eval_run (e : Expression I) (start : Number I) (a : I → Word) :
    (e.run start).eval a = gatesWord (start.value a) (compile (start.value a) (e.value a)).gates := by
  simp only [run, Code.eval, start.correct, e.correct]

def Expression.wire (n : Number I) : Expression I where
  value a := .wire (n.value a)
  cost := .constant 0
  output := n.rename some
  code := .literal []
  cost_correct a := rfl
  output_correct a start := rfl
  correct a start := rfl

def Expression.constant (t : Test I) : Expression I where
  value a := .constant (t.value a)
  cost := .constant 1
  output := .length none
  code := (GateCode.constant (t.rename some)).code (.length none)
  cost_correct a := rfl
  output_correct a start := by simp [Number.length, extend, compile]
  correct a start := by
    rw [GateCode.correct]
    simp [GateCode.value, Test.rename, Number.length, extend_some, extend, compile, gatesWord_singleton]

def Expression.choose (t : Test I) (e f : Expression I) : Expression I where
  value a := if t.value a then e.value a else f.value a
  cost := .choose t e.cost f.cost
  output := .choose (t.rename some) e.output f.output
  code := Code.when (t.rename some) e.code f.code
  cost_correct a := by simp only [Number.choose]; split <;> first | exact e.cost_correct a | exact f.cost_correct a
  output_correct a start := by
    simp only [Number.choose, Test.rename, extend_some]
    split <;> first | exact e.output_correct a start | exact f.output_correct a start
  correct a start := by
    rw [Code.eval_when]
    simp only [Test.rename, extend_some]
    split <;> first | exact e.correct a start | exact f.correct a start

end Lax429075Proofs.Streaming
