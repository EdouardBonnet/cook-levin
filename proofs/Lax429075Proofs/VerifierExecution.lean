import Lax429075Proofs.VerifierOutput
import Lax429075Proofs.VerifierSemantics

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

lemma ready_eq (xs ys : Word) (good : Bool) :
    ready xs ys good = parsing xs ys [] ⟨good, false, true, false⟩ none := by
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [ready, parsing]

lemma readyFormula_executes (xs ys : Word) (good : Bool) :
    ∃ t rest flags scratch,
      t ≤ 30 * (xs.length + 1) ^ 3 * (ys.length + 1) ∧ rest.length ≤ xs.length ∧
      (flags.valid && flags.conjunction) = (good && checkFormula xs ys) ∧
      Executes formula (ready xs ys good) (parsing rest ys [] flags scratch) t := by
  cases good with
  | false =>
    refine ⟨5, xs.tail.tail, ⟨false, false, true, false⟩, xs.tail.head?, ?_, ?_, rfl, ?_⟩
    · calc
        5 ≤ 30 * 1 ^ 3 * 1 := by norm_num
        _ ≤ 30 * (xs.length + 1) ^ 3 * (ys.length + 1) := by gcongr <;> omega
    · simp only [List.length_tail]; omega
    · rw [ready_eq]
      exact formula_invalid_executes xs ys _ none rfl
  | true =>
    obtain ⟨t, ht, he⟩ := formula_executes xs ys ⟨true, false, true, false⟩ none rfl
    refine ⟨t, (scanFormula xs).rest.tail,
      checkedFormulaFlags xs ys ⟨true, false, true, false⟩,
      (scanFormula xs).rest.head?, ?_, ?_, ?_, ?_⟩
    · exact ht.trans (by gcongr; norm_num)
    · have h := scanFormula_length xs
      simp only [List.length_tail]; omega
    · simp [checkedFormulaFlags, formulaFlags, checkFormula]
    · rw [ready_eq]
      exact he

lemma program_executes (w : Word) :
    ∃ t, t ≤ 100 * (w.length + 1) ^ 4 ∧
      Executes program (ioStore .input initial w)
        (ioStore .output initial [decideVerifier w]) t := by
  obtain ⟨d, hd, hdecode⟩ := decodePair_executes w
  obtain ⟨t, rest, flags, scratch, ht, hr, hb, he⟩ :=
    readyFormula_executes (splitInput w).formula (splitInput w).certificate (splitInput w).valid
  have hclean := cleanup_executes rest (splitInput w).certificate flags scratch
  have hout := output_executes flags
  rw [hb] at hout
  have h := Executes.seq hdecode (.seq he (.seq hclean hout))
  refine ⟨_, ?_, h⟩
  have hl := splitInput_length w
  have htf : t ≤ 30 * (w.length + 1) ^ 4 := ht.trans (by
    calc
      _ ≤ 30 * (w.length + 1) ^ 3 * (w.length + 1) := by gcongr <;> omega
      _ = 30 * (w.length + 1) ^ 4 := by ring)
  have hp : w.length + 1 ≤ (w.length + 1) ^ 4 := by
    calc
      w.length + 1 = (w.length + 1) * 1 ^ 3 := by ring
      _ ≤ (w.length + 1) * (w.length + 1) ^ 3 := by gcongr; omega
      _ = (w.length + 1) ^ 4 := by ring
  nlinarith

end Lax429075Proofs.VerifierProgram
