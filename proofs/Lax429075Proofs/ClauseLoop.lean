import Lax429075Proofs.ClauseParsing
import Lax429075Proofs.LoopSuffix

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax979537Proofs.StackProgram

def clauseTail : Code := .seq (.loop continuing clauseBody) requireTerminator

lemma clauseTail_executes (xs ys : Word) (flags : Flags) (hv : flags.valid = true) :
    ∃ t, t ≤ 16 * (xs.length + 1) ^ 2 * (ys.length + 1) ∧
      Executes clauseTail (parsing xs.tail ys [] flags xs.head?)
        (parsing (scanClause xs).rest ys [] (clauseFlags xs ys flags)
          (if (scanClause xs).valid then some false else none)) t := by
  induction xs using WellFounded.induction (measure List.length).wf generalizing flags with
  | h xs ih =>
    cases xs with
    | nil =>
      refine ⟨2, by simp; omega, ?_⟩
      have h := Executes.seq (Executes.loop_false (p := clauseBody)
        (b := continuing) (s := parsing [] ys [] flags none) (by simp [continuing, parsing]))
        (parsing_require [] ys [] flags none)
      simpa [clauseTail, scanClause, scanMany, clauseFlags, clauseValue] using h
    | cons b xs =>
      cases b with
      | false =>
        refine ⟨2, ?_, ?_⟩
        · calc
            2 ≤ 16 * 1 ^ 2 * 1 := by norm_num
            _ ≤ 16 * ((false :: xs).length + 1) ^ 2 * (ys.length + 1) := by gcongr <;> omega
        have h := Executes.seq (Executes.loop_false (p := clauseBody)
          (b := continuing) (s := parsing xs ys [] flags (some false))
          (by simp [continuing, parsing])) (parsing_require xs ys [] flags (some false))
        simpa [clauseTail, scanClause, scanMany, clauseFlags, clauseValue, hv] using h
      | true =>
        have hl := literal_executes xs ys flags (some true) hv
        have hr := parsing_read (scanLiteral xs).rest ys [] (literalFlags xs ys flags) none
        have hb : continuing (parsing (true :: xs).tail ys [] flags (true :: xs).head?).state = true := by
          simp [continuing, parsing, hv]
        cases ha : (scanLiteral xs).valid with
        | false =>
          have he : (scanLiteral xs).rest = [] := scanLiteral_invalid_rest xs ha
          have hstop := Executes.seq (Executes.loop_false (p := clauseBody) (b := continuing)
            (s := parsing (scanLiteral xs).rest.tail ys [] (literalFlags xs ys flags)
              (scanLiteral xs).rest.head?) (by simp [continuing, parsing, literalFlags, ha]))
            (parsing_require (scanLiteral xs).rest.tail ys [] (literalFlags xs ys flags)
              (scanLiteral xs).rest.head?)
          have h := loop_suffix_step hb (Executes.seq hl hr) hstop
          refine ⟨(literalCost xs ys + 1) + (1 + 1) + 1, ?_, ?_⟩
          · have hc := literalCost_bound xs ys
            simp only [List.length_cons]
            nlinarith [Nat.zero_le (xs.length * ys.length)]
          · simpa [clauseTail, clauseBody, clauseFlags, literalFlags, scanClause, scanMany,
              clauseValue, he, ha] using h
        | true =>
          obtain ⟨t, ht, hh⟩ := ih (scanLiteral xs).rest
            (by have h := scanLiteral_length xs; change _ < (true :: xs).length; simp; omega)
            (literalFlags xs ys flags) ha
          have h := loop_suffix_step hb (Executes.seq hl hr) hh
          refine ⟨(literalCost xs ys + 1) + t + 1, ?_, ?_⟩
          · have hc := literalCost_bound xs ys
            have hrec : t ≤ 16 * (xs.length + 1) ^ 2 * (ys.length + 1) := ht.trans (by
              gcongr
              exact scanLiteral_length xs)
            simp only [List.length_cons]
            nlinarith [Nat.zero_le (xs.length * ys.length)]
          · rw [clauseFlags_cons] at h
            simpa only [clauseTail, clauseBody, scanClause, scanMany, ha, Bool.true_and] using h

end Lax429075Proofs.VerifierProgram
