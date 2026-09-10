import Lax429075Proofs.EmitLiteral

namespace Lax429075Proofs.CNFOutput

open Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
open Lax429075.Encoding Lax429075.CNF Lax434930.PolynomialTime

variable {K Aux : Type} [DecidableEq K]

abbrev LiteralPort (K Aux : Type) := K × (Aux → Bool)

def clauseValue (v : K → ℕ) (a : Aux) (spec : List (LiteralPort K Aux)) : Clause :=
  spec.map fun p => ⟨v p.1, p.2 a⟩

def clauseCost (v : K → ℕ) (spec : List (LiteralPort K Aux)) : ℕ :=
  (spec.map fun p => 7 * v p.1 + 7).sum + 1

def emitClause (out tmp : K) : List (LiteralPort K Aux) → BitProgram K Aux
  | [] => emitBit out (fun _ => false)
  | p :: ps => .seq (emitBit out (fun _ => true))
      (.seq (emitLiteral out tmp p.1 p.2) (emitClause out tmp ps))

lemma emitted_source (out key : K) (hne : key ≠ out) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).stk key = s.stk key := by simp [emitted, hne]

lemma emitClause_executes (out tmp : K) (hot : out ≠ tmp)
    (spec : List (LiteralPort K Aux)) (v : K → ℕ) (s : BitStore K Aux)
    (hports : ∀ p ∈ spec, p.1 ≠ out ∧ p.1 ≠ tmp)
    (hvalues : ∀ p ∈ spec, s.stk p.1 = List.replicate (v p.1) true)
    (ht : s.stk tmp = []) (hs : s.state.2 = none) :
    Executes (emitClause out tmp spec) s
      (emitted out (encodeClause (clauseValue v s.state.1 spec)) s) (clauseCost v spec) := by
  induction spec generalizing s with
  | nil => exact emitBit_executes out (fun _ => false) s hs
  | cons p ps ih =>
    have hp := hports p (by simp)
    have hm := emitBit_executes out (fun _ : Aux => true) s hs
    let first := emitted out [true] s
    have hl := emitLiteral_executes out tmp p.1 p.2 hp.1 hp.2 hot first (v p.1)
      (by simpa [first, emitted_source out p.1 hp.1] using hvalues p (by simp))
      (by simpa [first, emitted_source out tmp (Ne.symm hot)] using ht)
    let middle := emitted out (encodeLiteral ⟨v p.1, p.2 s.state.1⟩) first
    have he := ih middle (fun q hq => hports q (by simp [hq]))
      (by
        intro q hq
        have hq' := (hports q (by simp [hq])).1
        simpa [middle, first, emitted_source out q.1 hq'] using hvalues q (by simp [hq]))
      (by simpa [middle, first, emitted_source out tmp (Ne.symm hot)] using ht) rfl
    have h := Executes.seq hm (.seq hl he)
    convert h using 1 <;>
      simp [middle, first, clauseValue, clauseCost, encodeClause, encodeList,
        emitted_append, List.append_assoc] <;> omega

lemma clauseCost_bound (v : K → ℕ) (spec : List (LiteralPort K Aux)) (bound : ℕ)
    (h : ∀ p ∈ spec, v p.1 ≤ bound) : clauseCost v spec ≤ (7 * bound + 7) * spec.length + 1 := by
  induction spec with
  | nil => simp [clauseCost]
  | cons p ps ih =>
    have hp := h p (by simp)
    have hh := ih (fun q hq => h q (by simp [hq]))
    simp only [clauseCost, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ] at *
    omega

end Lax429075Proofs.CNFOutput
