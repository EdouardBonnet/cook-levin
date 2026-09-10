import Lax429075Proofs.ExpressionOperations
import Lax429075Proofs.FoldGateStream

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime CircuitBuilder

variable {I : Type}

lemma code_append_eval (p q : Code I) (a : I → Word) :
    (Code.append p q).eval a = p.eval a ++ q.eval a := rfl

def foldCode (conjunction : Bool) (start n width : Number I) (term : Expression (Option I)) : Code I :=
  let i : Number (Option I) := .length none
  let s := start.rename some
  let w := width.rename some
  let count := n.rename some
  let terms := Code.loop n (term.run (s.add (i.mul w)))
  let initial := (GateCode.constant (.constant conjunction)).code (start.add (n.mul width))
  let current := (s.add (count.mul w)).add i
  let left := (s.add ((count.sub i).mul w)).sub (.constant 1)
  let gate := if conjunction then GateCode.conj left current else GateCode.disj left current
  .append terms (.append initial (Code.loop n (gate.code (current.add (.constant 1)))))

lemma foldCode_correct (conjunction : Bool) (start n width : Number I) (term : Expression (Option I))
    (a : I → Word) (hw : 0 < width.value a)
    (hc : ∀ i < n.value a, (term.value (extend a (List.replicate i true))).cost = width.value a) :
    (foldCode conjunction start n width term).eval a =
      gatesWord (start.value a) (compile (start.value a)
        (foldExpr conjunction ((List.range (n.value a)).map
          (fun i => term.value (extend a (List.replicate i true)))))).gates := by
  rw [compile_fold_uniform_word conjunction (start.value a) (width.value a) (n.value a) _ hw hc]
  cases conjunction <;>
    simp only [foldCode, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
      code_append_eval, Code.eval_loop, Expression.eval_run, GateCode.correct, GateCode.value,
      Number.add, Number.sub, Number.mul, Number.constant, Number.length, Number.rename,
      Test.constant, extend_some, extend, Option.elim_none, List.length_replicate, foldGate]

def Expression.fold (conjunction : Bool) (n width : Number I) (term : Expression (Option I))
    (hw : ∀ a, 0 < width.value a)
    (hc : ∀ a i, i < n.value a → (term.value (extend a (List.replicate i true))).cost = width.value a) :
    Expression I where
  value a := foldExpr conjunction ((List.range (n.value a)).map
    (fun i => term.value (extend a (List.replicate i true))))
  cost := ((n.mul width).add n).add (.constant 1)
  output := ((Number.length none).add ((n.mul width).rename some)).add (n.rename some)
  code := foldCode conjunction (.length none) (n.rename some) (width.rename some) (term.rename (Option.map some))
  cost_correct a := by
    simp only [Number.add, Number.mul, Number.constant, foldExpr_cost, List.length_map, List.length_range,
      uniform_sum_cost (n.value a) (width.value a) _ (hc a)]
  output_correct a start := by
    rw [compile_fold_output, uniform_sum_cost (n.value a) (width.value a) _ (hc a)]
    simp [Number.add, Number.mul, Number.length, Number.rename, extend_some, extend]
  correct a start := by
    have hh := foldCode_correct conjunction (Number.length none) (n.rename some) (width.rename some)
      (term.rename (Option.map some)) (extend a (List.replicate start true))
      (by simpa only [Number.rename, extend_some] using hw a) (by
        intro i hi
        simp only [Number.rename, extend_some] at hi
        simpa only [Expression.rename, Number.rename, extend_skip, extend_some] using hc a i hi)
    simpa only [Number.length, Number.rename, Expression.rename, extend_some, extend_skip,
      extend, Option.elim_none, List.length_replicate] using hh

end Lax429075Proofs.Streaming
