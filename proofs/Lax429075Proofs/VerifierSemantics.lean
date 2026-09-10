import Lax429075Proofs.FormulaParsing
import Lax429075Proofs.PairDecoding

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930.Certificates
open Lax429075.Encoding Lax429075.CNF Lax429075.Satisfiability

def checkFormula (xs ys : Word) : Bool :=
  (scanFormula xs).valid && (scanFormula xs).rest.head?.isNone &&
    eval (scanFormula xs).value (assignment ys)

def decideVerifier (w : Word) : Bool :=
  let s := splitInput w
  s.valid && checkFormula s.formula s.certificate

lemma checkFormula_sound (xs ys : Word) (h : checkFormula xs ys = true) :
    ∃ F, encodeCNF F = xs ∧ eval F (assignment ys) = true := by
  have hv : ((scanFormula xs).valid = true ∧ (scanFormula xs).rest.head?.isNone = true) ∧
      eval (scanFormula xs).value (assignment ys) = true := by
    simpa only [checkFormula, Bool.and_eq_true] using h
  have he : (scanFormula xs).rest = [] := by
    cases hr : (scanFormula xs).rest <;> simp_all
  refine ⟨(scanFormula xs).value, ?_, hv.2⟩
  simpa [he] using (scanFormula_sound xs hv.1.1).symm

lemma checkFormula_encoded (F : Formula) (ys : Word) :
    checkFormula (encodeCNF F) ys = eval F (assignment ys) := by
  have h := scanFormula_encoded F []
  simp only [List.append_nil] at h
  simp [checkFormula, h]

lemma decideVerifier_correct (w : Word) : decideVerifier w = true ↔ w ∈ Verifier := by
  constructor
  · intro h
    have hv : (splitInput w).valid = true ∧
        checkFormula (splitInput w).formula (splitInput w).certificate = true := by
      simpa only [decideVerifier, Bool.and_eq_true] using h
    obtain ⟨F, hF, he⟩ := checkFormula_sound _ _ hv.2
    refine ⟨F, (splitInput w).certificate, ?_, he⟩
    rw [hF]
    exact splitInput_sound w hv.1
  · rintro ⟨F, ys, rfl, he⟩
    simpa [decideVerifier, splitInput_pair, checkFormula_encoded] using he

end Lax429075Proofs.VerifierProgram
