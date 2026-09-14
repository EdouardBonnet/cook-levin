import Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy
import Lax429075.Encoding

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.CNFOutput

open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax429075.Encoding Lax429075.CNF Lax434930.PolynomialTime

variable {K Aux : Type} [DecidableEq K]

def emitted (out : K) (w : Word) (s : BitStore K Aux) : BitStore K Aux :=
  ⟨(s.state.1, none), Function.update s.stk out (w.reverse ++ s.stk out)⟩

@[simp] lemma emitted_aux (out : K) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).state.1 = s.state.1 := rfl

@[simp] lemma emitted_scratch (out : K) (w : Word) (s : BitStore K Aux) :
    (emitted out w s).state.2 = none := rfl

lemma emitted_empty (out : K) (s : BitStore K Aux) :
    emitted out [] s = ⟨(s.state.1, none), s.stk⟩ := by
  simp [emitted, Function.update_eq_self]

lemma emitted_append (out : K) (u v : Word) (s : BitStore K Aux) :
    emitted out v (emitted out u s) = emitted out (u ++ v) s := by
  simp [emitted, List.reverse_append, List.append_assoc, Function.update_idem]

def emitBit (out : K) (value : Aux → Bool) : BitProgram K Aux :=
  .atom (.push out (fun s => value s.1))

lemma emitBit_executes (out : K) (value : Aux → Bool) (s : BitStore K Aux) (hs : s.state.2 = none) :
    Executes (emitBit out value) s (emitted out [value s.state.1] s) 1 := by
  convert! Executes.atom (.push out (fun q : Aux × Option Bool => value q.1)) s using 1
  apply Store.ext
  · simp [Op.apply, emitted, ← hs]
  · simp [Op.apply, emitted]

def emitLiteral (out tmp index : K) (sign : Aux → Bool) : BitProgram K Aux :=
  .seq (Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy.copy index out tmp)
    (.seq (emitBit out (fun _ => false)) (emitBit out sign))

lemma emitLiteral_executes (out tmp index : K) (sign : Aux → Bool)
    (hio : index ≠ out) (hit : index ≠ tmp) (hot : out ≠ tmp)
    (s : BitStore K Aux) (n : ℕ) (hn : s.stk index = List.replicate n true) (ht : s.stk tmp = []) :
    Executes (emitLiteral out tmp index sign) s
      (emitted out (encodeLiteral ⟨n, sign s.state.1⟩) s) (7 * n + 6) := by
  have hc := Lax434930Proofs.InclusionAux.TimeCompiler.StackCopy.copy_store index out tmp hio hit hot s ht
  have he : (⟨(s.state.1, none), Function.update s.stk out (s.stk index ++ s.stk out)⟩ : BitStore K Aux) =
      emitted out (List.replicate n true) s := by simp [emitted, hn]
  rw [he, hn, List.length_replicate] at hc
  have hz := emitBit_executes out (fun _ : Aux => false) (emitted out (List.replicate n true) s) rfl
  have hs := emitBit_executes out sign (emitted out [false] (emitted out (List.replicate n true) s)) rfl
  have h := Executes.seq hc (.seq hz hs)
  simp only [emitted_append] at h
  convert! h using 1 <;> simp [encodeLiteral, encodeNat, List.append_assoc] <;> omega

end Lax429075Proofs.CNFOutput
