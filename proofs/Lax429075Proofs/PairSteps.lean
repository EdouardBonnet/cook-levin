import Lax429075Proofs.PairDecoding

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer

def decodingData (base : Register → Word) (xs rev : Word) (conj disj : Bool) : Data :=
  ⟨(⟨true, true, conj, disj⟩, xs.head?), Function.update (Function.update base .input xs.tail) .reverse rev⟩

def decodingDone (base : Register → Word) (out : SplitInput) (rev : Word) (conj disj : Bool) : Data :=
  ⟨(⟨out.valid, false, conj, disj⟩, if out.valid then some true else none),
    Function.update (Function.update base .input out.certificate) .reverse (out.formula.reverse ++ rev)⟩

lemma decodingBody_cons (base : Register → Word) (xs rev : Word) (b conj disj : Bool) :
    Executes decodingBody (decodingData base (false :: b :: xs) rev conj disj)
      (decodingData base xs (b :: rev) conj disj) 6 := by
  let d := decodingData base (false :: b :: xs) rev conj disj
  let op₁ : Op (fun _ : Register => Bool) Control := .pop .input (fun s v => (s.1, v))
  let op₂ : Op (fun _ : Register => Bool) Control := .push .reverse (fun s => s.2.getD false)
  have h₁ := Executes.atom op₁ d
  have h₂ := Executes.atom op₂ (op₁.apply d)
  have h₃ := Executes.atom op₁ (op₂.apply (op₁.apply d))
  have heq : op₁.apply (op₂.apply (op₁.apply d)) = decodingData base xs (b :: rev) conj disj := by
    apply Store.ext
    · simp [op₁, op₂, d, decodingData, Op.apply]
    · funext r
      cases r <;> simp [op₁, op₂, d, decodingData, Op.apply]
  have hh : Executes decodingBody d (op₁.apply (op₂.apply (op₁.apply d))) 6 :=
    .branch_true rfl (.branch_false rfl (.seq h₁ (.branch_true rfl (.seq h₂ h₃))))
  exact heq ▸ hh

lemma decodingBody_end (base : Register → Word) (xs rev : Word) (conj disj : Bool) :
    Executes decodingBody (decodingData base (true :: xs) rev conj disj)
      (decodingDone base ⟨[], xs, true⟩ rev conj disj) 3 := by
  exact .branch_true rfl (.branch_true rfl (.atom _ _))

lemma decodingBody_empty (base : Register → Word) (rev : Word) (conj disj : Bool) :
    Executes decodingBody (decodingData base [] rev conj disj)
      (decodingDone base ⟨[], [], false⟩ rev conj disj) 2 := by
  exact .branch_false rfl (.atom _ _)

lemma decodingBody_incomplete (base : Register → Word) (rev : Word) (conj disj : Bool) :
    Executes decodingBody (decodingData base [false] rev conj disj)
      (decodingDone base ⟨[], [], false⟩ rev conj disj) 5 := by
  let d := decodingData base [false] rev conj disj
  let op₁ : Op (fun _ : Register => Bool) Control := .pop .input (fun s v => (s.1, v))
  have h₁ := Executes.atom op₁ d
  have h₂ := Executes.atom (.load (fun s : Control => ({s.1 with valid := false, active := false}, s.2))) (op₁.apply d)
  have hh : Executes decodingBody d _ 5 :=
    .branch_true rfl (.branch_false rfl (.seq h₁ (.branch_false rfl h₂)))
  convert hh using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [d, op₁, decodingData, decodingDone, Op.apply]

end Lax429075Proofs.VerifierProgram
