import Lax429075Proofs.ClauseParsing

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax429075.Encoding Lax429075.CNF Lax429075.Satisfiability

def scanFormula : Word → Parsed Formula := scanMany scanClause scanClause_length

lemma scanFormula_length (xs : Word) : (scanFormula xs).rest.length ≤ xs.length :=
  scanMany_length _ _ xs

lemma scanFormula_sound (xs : Word) (hv : (scanFormula xs).valid = true) :
    xs = encodeCNF (scanFormula xs).value ++ (scanFormula xs).rest :=
  scanMany_sound _ _ _ scanClause_sound xs hv

lemma scanFormula_encoded (F : Formula) (xs : Word) :
    scanFormula (encodeCNF F ++ xs) = ⟨F, xs, true⟩ :=
  scanMany_encoded _ _ _ scanClause_encoded F xs

lemma scanFormula_invalid_rest (xs : Word) (hv : (scanFormula xs).valid = false) :
    (scanFormula xs).rest = [] :=
  scanMany_invalid_rest _ _ scanClause_invalid_rest xs hv

def lastClause (ys : Word) : Formula → Bool → Bool
  | [], previous => previous
  | C :: Cs, _ => lastClause ys Cs (clauseValue C ys)

def formulaFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanFormula xs).valid
    conjunction := flags.conjunction && eval (scanFormula xs).value (assignment ys)
    clause := lastClause ys (scanFormula xs).value flags.clause}

end Lax429075Proofs.VerifierProgram
