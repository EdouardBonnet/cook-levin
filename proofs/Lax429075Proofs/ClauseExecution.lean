import Lax429075Proofs.ClauseLoop

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax979537Proofs.StackProgram

def checkedClauseFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanClause xs).valid
    conjunction := flags.conjunction && clauseValue (scanClause xs).value ys
    clause := clauseValue (scanClause xs).value ys}

lemma clause_executes (xs ys : Word) (flags : Flags) (scratch : Option Bool)
    (hv : flags.valid = true) :
    ∃ t, t ≤ 20 * (xs.length + 1) ^ 2 * (ys.length + 1) ∧
      Executes clause (parsing xs ys [] flags scratch)
        (parsing (scanClause xs).rest ys [] (checkedClauseFlags xs ys flags)
          (if (scanClause xs).valid then some false else none)) t := by
  let f : Flags := {flags with clause := false}
  have ha := parsing_assign (fun s => {s with clause := false}) xs ys [] flags scratch
  have hr := parsing_read xs ys [] f scratch
  obtain ⟨t, ht, he⟩ := clauseTail_executes xs ys f hv
  have hz := parsing_assign (fun s => {s with conjunction := s.conjunction && s.clause})
    (scanClause xs).rest ys [] (clauseFlags xs ys f)
    (if (scanClause xs).valid then some false else none)
  cases he with
  | seq hl hq =>
    have h := Executes.seq ha (.seq hr (.seq hl (.seq hq hz)))
    refine ⟨_, ?_, by simpa [clause, f, clauseFlags, checkedClauseFlags] using h⟩
    have hp : 0 < (xs.length + 1) ^ 2 * (ys.length + 1) := by positivity
    nlinarith

end Lax429075Proofs.VerifierProgram
