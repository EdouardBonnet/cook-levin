import Lax429075Proofs.FormulaParsing
import Lax429075Proofs.ClauseExecution

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax979537Proofs.StackProgram Lax429075.CNF

def formulaTail : Code := .seq (.loop continuing formulaBody) requireTerminator

lemma formulaFlags_cons (xs ys : Word) (flags : Flags) :
    formulaFlags (scanClause xs).rest ys (checkedClauseFlags xs ys flags) =
      formulaFlags (true :: xs) ys flags := by
  cases hv : (scanClause xs).valid with
  | true => simp [formulaFlags, checkedClauseFlags, scanFormula, scanMany, clauseValue,
      eval, lastClause, hv, Bool.and_assoc]
  | false => simp [formulaFlags, checkedClauseFlags, scanFormula, scanMany, clauseValue,
      eval, lastClause, scanClause_invalid_rest xs hv, hv, Bool.and_assoc]

lemma formulaTail_executes (xs ys : Word) (flags : Flags) (hv : flags.valid = true) :
    ∃ t, t ≤ 24 * (xs.length + 1) ^ 3 * (ys.length + 1) ∧
      Executes formulaTail (parsing xs.tail ys [] flags xs.head?)
        (parsing (scanFormula xs).rest ys [] (formulaFlags xs ys flags)
          (if (scanFormula xs).valid then some false else none)) t := by
  induction xs using WellFounded.induction (measure List.length).wf generalizing flags with
  | h xs ih =>
    cases xs with
    | nil =>
      refine ⟨2, by simp; omega, ?_⟩
      have h := Executes.seq (Executes.loop_false (p := formulaBody)
        (b := continuing) (s := parsing [] ys [] flags none) (by simp [continuing, parsing]))
        (parsing_require [] ys [] flags none)
      simpa [formulaTail, scanFormula, scanMany, formulaFlags, eval, lastClause] using h
    | cons b xs =>
      cases b with
      | false =>
        refine ⟨2, ?_, ?_⟩
        · calc
            2 ≤ 24 * 1 ^ 3 * 1 := by norm_num
            _ ≤ 24 * ((false :: xs).length + 1) ^ 3 * (ys.length + 1) := by gcongr <;> omega
        have h := Executes.seq (Executes.loop_false (p := formulaBody)
          (b := continuing) (s := parsing xs ys [] flags (some false))
          (by simp [continuing, parsing])) (parsing_require xs ys [] flags (some false))
        simpa [formulaTail, scanFormula, scanMany, formulaFlags, eval, lastClause, hv] using h
      | true =>
        obtain ⟨a, haBound, hl⟩ := clause_executes xs ys flags (some true) hv
        have hr := parsing_read (scanClause xs).rest ys [] (checkedClauseFlags xs ys flags)
          (if (scanClause xs).valid then some false else none)
        have hb : continuing (parsing (true :: xs).tail ys [] flags (true :: xs).head?).state = true := by
          simp [continuing, parsing, hv]
        cases ha : (scanClause xs).valid with
        | false =>
          have he : (scanClause xs).rest = [] := scanClause_invalid_rest xs ha
          have hstop := Executes.seq (Executes.loop_false (p := formulaBody) (b := continuing)
            (s := parsing (scanClause xs).rest.tail ys [] (checkedClauseFlags xs ys flags)
              (scanClause xs).rest.head?) (by simp [continuing, parsing, checkedClauseFlags, ha]))
            (parsing_require (scanClause xs).rest.tail ys [] (checkedClauseFlags xs ys flags)
              (scanClause xs).rest.head?)
          have h := loop_suffix_step hb (Executes.seq hl hr) hstop
          refine ⟨(a + 1) + (1 + 1) + 1, ?_, ?_⟩
          · simp only [List.length_cons]
            nlinarith [Nat.zero_le (xs.length ^ 2 * ys.length), Nat.zero_le (xs.length * ys.length)]
          · simpa [formulaTail, formulaBody, formulaFlags, checkedClauseFlags, scanFormula,
              scanMany, eval, lastClause, clauseValue, he, ha] using h
        | true =>
          obtain ⟨t, ht, hh⟩ := ih (scanClause xs).rest
            (by have h := scanClause_length xs; change _ < (true :: xs).length; simp; omega)
            (checkedClauseFlags xs ys flags) ha
          have h := loop_suffix_step hb (Executes.seq hl hr) hh
          refine ⟨(a + 1) + t + 1, ?_, ?_⟩
          · have hrec : t ≤ 24 * (xs.length + 1) ^ 3 * (ys.length + 1) := ht.trans (by
              gcongr
              exact scanClause_length xs)
            simp only [List.length_cons]
            nlinarith [Nat.zero_le (xs.length ^ 2 * ys.length), Nat.zero_le (xs.length * ys.length)]
          · rw [formulaFlags_cons] at h
            simpa only [formulaTail, formulaBody, scanFormula, scanMany, ha, Bool.true_and] using h

end Lax429075Proofs.VerifierProgram
