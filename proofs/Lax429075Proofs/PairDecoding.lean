import Lax429075Proofs.VerifierProgram
import Lax434930.Certificates

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930.Certificates

structure SplitInput where
  formula : Word
  certificate : Word
  valid : Bool
  deriving DecidableEq

def splitInput : Word → SplitInput
  | [] => ⟨[], [], false⟩
  | true :: y => ⟨[], y, true⟩
  | [false] => ⟨[], [], false⟩
  | false :: b :: rest =>
      let r := splitInput rest
      ⟨b :: r.formula, r.certificate, r.valid⟩

lemma splitInput_pair (x y : Word) : splitInput (pair x y) = ⟨x, y, true⟩ := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [pair, splitInput, ih]

lemma splitInput_unpair (w : Word) :
    unpair w = if (splitInput w).valid then some ((splitInput w).formula, (splitInput w).certificate) else none := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> rfl
  | cons_cons b c w ih _ =>
    cases b with
    | true => rfl
    | false =>
      simp only [unpair, splitInput, ih]
      cases (splitInput w).valid <;> rfl

lemma splitInput_sound (w : Word) (h : (splitInput w).valid = true) :
    w = pair (splitInput w).formula (splitInput w).certificate := by
  induction w using List.twoStepInduction with
  | nil => simp [splitInput] at h
  | singleton b => cases b <;> simp [splitInput, pair] at *
  | cons_cons b c w ih _ =>
    cases b with
    | true => rfl
    | false =>
      change false :: c :: w = false :: c :: pair (splitInput w).formula (splitInput w).certificate
      exact congrArg (fun xs => false :: c :: xs) (ih h)

lemma splitInput_length (w : Word) :
    (splitInput w).formula.length + (splitInput w).certificate.length ≤ w.length := by
  induction w using List.twoStepInduction with
  | nil => decide
  | singleton b => cases b <;> decide
  | cons_cons b c w ih _ => cases b <;> simp [splitInput] at * <;> omega

def decodeCost : Word → ℕ
  | [] => 4
  | true :: _ => 5
  | [false] => 7
  | false :: _ :: rest => 7 + decodeCost rest

lemma decodeCost_bound (w : Word) : decodeCost w ≤ 7 * w.length + 5 := by
  induction w using List.twoStepInduction with
  | nil => decide
  | singleton b => cases b <;> decide
  | cons_cons b c w ih _ => cases b <;> simp [decodeCost] at * <;> omega

end Lax429075Proofs.VerifierProgram
