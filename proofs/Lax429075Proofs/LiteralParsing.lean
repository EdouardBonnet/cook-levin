import Lax429075Proofs.UnaryExecution
import Lax429075.Satisfiability

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax429075.Encoding Lax429075.CNF Lax429075.Satisfiability

structure Parsed (α : Type) where
  value : α
  rest : Word
  valid : Bool

def scanLiteral (xs : Word) : Parsed Literal :=
  let u := unary xs
  ⟨⟨u.index, u.rest.head?.getD false⟩, u.rest.tail, u.valid && u.rest.head?.isSome⟩

lemma scanLiteral_length (xs : Word) : (scanLiteral xs).rest.length ≤ xs.length := by
  have h := unary_length xs
  simp only [scanLiteral, List.length_tail]
  omega

lemma scanLiteral_sound (xs : Word) (h : (scanLiteral xs).valid = true) :
    xs = encodeLiteral (scanLiteral xs).value ++ (scanLiteral xs).rest := by
  have hv : (unary xs).valid = true ∧ (unary xs).rest.head?.isSome = true := by
    simpa only [scanLiteral, Bool.and_eq_true] using h
  have hu := unary_sound xs hv.1
  cases hr : (unary xs).rest with
  | nil => simp [hr] at hv
  | cons b rest =>
    simpa [scanLiteral, encodeLiteral, hr, List.append_assoc] using hu

lemma scanLiteral_encoded (l : Literal) (xs : Word) :
    scanLiteral (encodeLiteral l ++ xs) = ⟨l, xs, true⟩ := by
  have h : encodeLiteral l ++ xs = encodeNat l.index ++ (l.positive :: xs) := by
    simp [encodeLiteral, List.append_assoc]
  rw [h]
  simp [scanLiteral, unary_encoded]

def literalFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanLiteral xs).valid
    clause := flags.clause || (scanLiteral xs).value.eval (assignment ys)}

def literalCost (xs ys : Word) : ℕ :=
  7 * ys.length + 3 * (unary xs).index +
    2 * (ys.drop (unary xs).index).tail.length + 11

lemma literalCost_bound (xs ys : Word) : literalCost xs ys ≤ 12 * (xs.length + ys.length + 1) := by
  have hu := unary_length xs
  simp only [literalCost, List.length_tail, List.length_drop]
  omega

end Lax429075Proofs.VerifierProgram
