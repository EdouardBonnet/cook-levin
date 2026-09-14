import Lax429075Proofs.EmitClause
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.CNFOutput

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax429075.Encoding Lax429075.CNF Lax434930.PolynomialTime

variable {K Aux : Type} [DecidableEq K]

def formulaValue (v : K → ℕ) (a : Aux) (spec : List (List (LiteralPort K Aux))) : Formula :=
  spec.map (clauseValue v a)

def segment (F : Formula) : Word := F.flatMap (fun C => true :: encodeClause C)

lemma segment_encode (F : Formula) : segment F ++ [false] = encodeCNF F := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa only [segment, List.flatMap_cons, List.cons_append,
      List.append_assoc, encodeCNF, encodeList] using congrArg (fun w => true :: (encodeClause C ++ w)) ih

def formulaCost (v : K → ℕ) (spec : List (List (LiteralPort K Aux))) : ℕ :=
  (spec.map fun C => clauseCost v C + 1).sum + 1

def emitFormula (out tmp : K) : List (List (LiteralPort K Aux)) → BitProgram K Aux
  | [] => .atom (.load (fun s => (s.1, none)))
  | C :: Cs => .seq (emitBit out (fun _ => true))
      (.seq (emitClause out tmp C) (emitFormula out tmp Cs))

lemma emitFormula_executes (out tmp : K) (hot : out ≠ tmp)
    (spec : List (List (LiteralPort K Aux))) (v : K → ℕ) (s : BitStore K Aux)
    (hports : ∀ C ∈ spec, ∀ p ∈ C, p.1 ≠ out ∧ p.1 ≠ tmp)
    (hvalues : ∀ C ∈ spec, ∀ p ∈ C, s.stk p.1 = List.replicate (v p.1) true)
    (ht : s.stk tmp = []) (hs : s.state.2 = none) :
    Executes (emitFormula out tmp spec) s
      (emitted out (segment (formulaValue v s.state.1 spec)) s) (formulaCost v spec) := by
  induction spec generalizing s with
  | nil =>
    simpa [emitFormula, formulaValue, segment, formulaCost, emitted_empty] using!
      Executes.atom (.load (fun q : Aux × Option Bool => (q.1, none))) s
  | cons C Cs ih =>
    have hm := emitBit_executes out (fun _ : Aux => true) s hs
    let first := emitted out [true] s
    have hc := emitClause_executes out tmp hot C v first (hports C (by simp))
      (by
        intro p hp
        have hn := (hports C (by simp) p hp).1
        simpa [first, emitted_source out p.1 hn] using hvalues C (by simp) p hp)
      (by simpa [first, emitted_source out tmp (Ne.symm hot)] using ht) rfl
    let middle := emitted out (encodeClause (clauseValue v s.state.1 C)) first
    have he := ih middle (fun D hD => hports D (by simp [hD]))
      (by
        intro D hD p hp
        have hn := (hports D (by simp [hD]) p hp).1
        simpa [middle, first, emitted_source out p.1 hn] using hvalues D (by simp [hD]) p hp)
      (by simpa [middle, first, emitted_source out tmp (Ne.symm hot)] using ht) rfl
    have h := Executes.seq hm (.seq hc he)
    convert! h using 1 <;>
      simp [middle, first, formulaValue, formulaCost, segment, emitted_append, List.append_assoc] <;> omega

lemma formulaCost_bound (v : K → ℕ) (spec : List (List (LiteralPort K Aux))) (bound size : ℕ)
    (hsize : ∀ C ∈ spec, C.length ≤ size)
    (hvalues : ∀ C ∈ spec, ∀ p ∈ C, v p.1 ≤ bound) :
    formulaCost v spec ≤ ((7 * bound + 7) * size + 2) * spec.length + 1 := by
  induction spec with
  | nil => simp [formulaCost]
  | cons C Cs ih =>
    have hc := clauseCost_bound v C bound (hvalues C (by simp))
    have hl := hsize C (by simp)
    have ht := ih (fun D hD => hsize D (by simp [hD])) (fun D hD => hvalues D (by simp [hD]))
    simp only [formulaCost, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at *
    nlinarith

end Lax429075Proofs.CNFOutput
