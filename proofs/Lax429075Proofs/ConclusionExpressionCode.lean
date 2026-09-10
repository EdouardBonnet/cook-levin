import Lax429075Proofs.VectorOutputCode
import Lax429075Proofs.CircuitAcceptance

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit WindowMachine CircuitBuilder CertificateCircuit

variable {I : Type}

def Expression.any : List (Expression I) → Expression I
  | [] => .constant (.constant false)
  | e :: es => Expression.disj e (Expression.any es)

lemma Expression.any_value (es : List (Expression I)) (a : I → Word) :
    (Expression.any es).value a = anyExpr (es.map fun e => e.value a) := by
  induction es <;> simp_all [Expression.any, Expression.disj, Expression.binary, Expression.constant, Test.constant, anyExpr]

def prefixTermCode (bound i : Number I) : Expression I :=
  Expression.disj (Expression.neg (Expression.wire ((bound.add (i.add (.constant 1))).add (.constant 1))))
    (Expression.wire ((bound.add i).add (.constant 1)))

lemma prefixTermCode_cost (bound i : Number I) (a : I → Word) :
    ((prefixTermCode bound i).value a).cost = 2 := rfl

def prefixCode (bound : Number I) : Expression I :=
  Expression.fold true (bound.sub (.constant 1)) (.constant 2)
    (prefixTermCode (bound.rename some) (.length none)) (fun _ => Nat.zero_lt_succ 1)
    (fun a i _ => prefixTermCode_cost _ _ (extend a (List.replicate i true)))

lemma prefixCode_value (bound : Number I) (a : I → Word) :
    (prefixCode bound).value a = prefixExpr (bound.value a) := by
  simp [prefixCode, Expression.fold, foldExpr, Number.sub, Number.constant, prefixTermCode,
    Expression.disj, Expression.binary, Expression.neg, Expression.wire, Number.add, Number.length,
    Number.rename, extend_some, extend, prefixExpr, livePort]

noncomputable def acceptanceCode (M : SingleTape) (base pitch : Number I) : Expression I :=
  Expression.any ((Finset.univ : Finset M.Q).toList.map fun q =>
    Expression.conj (Expression.wire (wireNumber base pitch (.constant (stateIndex M q))))
      (.constant (.constant (M.accept q))))

lemma acceptanceCode_value (M : SingleTape) (base pitch : Number I) (radius : ℕ) (a : I → Word) :
    (acceptanceCode M base pitch).value a =
      (acceptanceExpr M radius).rename (affineAddress (base.value a) (pitch.value a)) := by
  simp [acceptanceCode, Expression.any_value, List.map_map, Function.comp_def,
    Expression.conj, Expression.binary, Expression.wire, Expression.constant, Test.constant,
    wireNumber_value, Number.constant, acceptanceExpr, anyExpr_rename,
    MachineCircuit.wire, Expr.rename, bitIndex_state]

noncomputable def conclusionCode (M : SingleTape) (bound base pitch : Number I) : Expression I :=
  Expression.conj (prefixCode bound) (acceptanceCode M base pitch)

lemma conclusionCode_value (M : SingleTape) (bound base pitch : Number I) (radius : ℕ) (a : I → Word) :
    (conclusionCode M bound base pitch).value a = Expr.conj (prefixExpr (bound.value a))
      ((acceptanceExpr M radius).rename (affineAddress (base.value a) (pitch.value a))) := by
  simp only [conclusionCode, Expression.conj, Expression.binary, Bool.true_eq, ite_true, prefixCode_value]
  rw [acceptanceCode_value M base pitch radius]

end Lax429075Proofs.Streaming
