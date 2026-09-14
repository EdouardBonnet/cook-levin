import Lax429075Proofs.PairLoop

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer

def ready (x y : Word) (good : Bool) : Data :=
  ⟨(⟨good, false, true, false⟩, none), fun r =>
    if r = .input then y else if r = .formula then x else []⟩

lemma initial_read (w : Word) :
    Executes (read .input) (ioStore .input initial w)
      (decodingData (fun _ => []) w [] true false) 1 := by
  have he := Executes.atom (.pop Register.input (fun s : Control => fun b => (s.1, b)))
    (ioStore Register.input initial w : Data)
  convert! he using 1
  apply Store.ext
  · simp [ioStore, initial, Op.apply, decodingData]
  · funext r
    cases r <;> simp [ioStore, Op.apply, decodingData]

lemma decodePair_executes (w : Word) :
    ∃ t, t ≤ 10 * w.length + 8 ∧
      Executes decodePair (ioStore .input initial w)
        (ready (splitInput w).formula (splitInput w).certificate (splitInput w).valid) t := by
  have hread := initial_read w
  have hloop := decodingLoop_executes (fun _ => []) w [] true false
  let d := decodingDone (fun _ => []) (splitInput w) [] true false
  have htrans := transfer_store .reverse .formula (by decide) d
  have heq :
      (⟨(d.state.1, none), Function.update (Function.update d.stk .reverse []) .formula
        ((d.stk .reverse).reverse ++ d.stk .formula)⟩ : Data) =
      ready (splitInput w).formula (splitInput w).certificate (splitInput w).valid := by
    apply Store.ext
    · rfl
    · funext r
      cases r <;> simp [d, decodingDone, ready]
  rw [heq] at htrans
  refine ⟨_, ?_, .seq hread (.seq hloop htrans)⟩
  have ht := decodeCost_bound w
  have hl := splitInput_length w
  simp [d, decodingDone] at *
  omega

end Lax429075Proofs.VerifierProgram
