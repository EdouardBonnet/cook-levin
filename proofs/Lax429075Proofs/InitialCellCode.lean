import Lax429075Proofs.ExpressionOperations
import Lax429075Proofs.OutputDivision
import Lax429075Proofs.PairedInputBits
import Lax429075Proofs.InitialCircuitCells

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax434930.MachineModels
open CertificateCircuit CircuitBuilder
open scoped Classical

variable {I : Type}

def Expression.pad (k : ℕ) (e : Expression I) : Expression I :=
  match k with
  | 0 => e
  | k + 1 => Expression.conj (Expression.pad k e) (.constant (.constant true))

lemma Expression.pad_value (k : ℕ) (e : Expression I) (a : I → Word) :
    (Expression.pad k e).value a = CircuitBuilder.pad k (e.value a) := by
  induction k <;> simp_all [pad, Expression.conj, Expression.binary, Expression.constant, Test.constant,
    CircuitBuilder.pad]

def Test.choose (t u v : Test I) : Test I where
  value a := if t.value a then u.value a else v.value a
  code := Code.when t u.code v.code
  correct a := by rw [Code.eval_when]; split <;> first | exact u.correct a | exact v.correct a

def knownBitCode (input : I) (i : Number I) : Test I :=
  (Test.eq i ((Number.constant 2).mul (.length input))).or
    ((Test.eq (i.mod (.constant 2)) (.constant 1)).and (Test.input input (i.div (.constant 2))))

lemma knownBitCode_value (input : I) (i : Number I) (a : I → Word) :
    (knownBitCode input i).value a = prefixBit (a input) (i.value a) := by
  simp [knownBitCode, Test.or, Test.and, Test.eq_value, Test.input, Number.div, Number.mod,
    Number.constant, Number.mul, Number.length, prefixBit]

noncomputable def certificateCellCode (M : SingleTape) (bound i : Number I) (symbol : M.Γ) : Expression I :=
  let data := Expression.wire (i.add (.constant 1))
  let present := Expression.wire ((bound.add i).add (.constant 1))
  Expression.disj
    (Expression.conj present (Expression.disj
      (Expression.conj data (.constant (.constant (decide (M.input true = symbol)))))
      (Expression.conj (Expression.neg data) (.constant (.constant (decide (M.input false = symbol)))))))
    (Expression.conj (Expression.neg present) (.constant (.constant (decide (default = symbol)))))

lemma certificateCellCode_value (M : SingleTape) (bound i : Number I) (symbol : M.Γ) (a : I → Word) :
    (certificateCellCode M bound i symbol).value a = certificateCell M (bound.value a) (i.value a) symbol := by
  rfl

noncomputable def initialCellCode (M : SingleTape) (input : I) (bound radius position : Number I)
    (symbol : M.Γ) : Expression I :=
  let blank := Expression.pad 5 (.constant (.constant (decide (default = symbol))))
  let j := position.sub radius
  let prefixLength := ((Number.constant 2).mul (.length input)).add (.constant 1)
  let known := Expression.pad 5 (.constant (Test.choose (knownBitCode input j)
    (.constant (decide (M.input true = symbol))) (.constant (decide (M.input false = symbol)))))
  Expression.choose (Test.lt position radius) blank
    (Expression.choose (Test.lt j prefixLength) known
      (Expression.choose (Test.lt (j.sub prefixLength) bound)
        (certificateCellCode M bound (j.sub prefixLength) symbol) blank))

lemma initialCellCode_cost (M : SingleTape) (input : I) (bound radius position : Number I)
    (symbol : M.Γ) (a : I → Word) : ((initialCellCode M input bound radius position symbol).value a).cost = 11 := by
  simp only [initialCellCode, Expression.choose]
  split_ifs <;> simp [Expression.pad_value, Expression.constant, pad_cost, Expr.cost,
    certificateCellCode_value, certificateCell_cost]

end Lax429075Proofs.Streaming
