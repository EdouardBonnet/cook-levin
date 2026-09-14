import Lax429075Proofs.FormulaExecution

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax434930Proofs.InclusionAux.TimeCompiler.StackClear

lemma parsing_clearInput (xs ys : Word) (flags : Flags) (scratch : Option Bool) :
    Executes (clear .input) (parsing xs ys [] flags scratch)
      (parsing xs [] [] flags none) (2 * ys.length + 2) := by
  have h := clear_store .input (parsing xs ys [] flags scratch)
  convert! h using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [parsing]

lemma parsing_clearFormula (xs : Word) (flags : Flags) :
    Executes (clear .formula) (parsing xs [] [] flags none)
      (parsing [] [] [] flags none) (2 * xs.length + 2) := by
  have h := clear_store .formula (parsing xs [] [] flags none)
  convert! h using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [parsing]

lemma parsing_clearEmpty (r : Register) (flags : Flags) :
    Executes (clear r) (parsing [] [] [] flags none) (parsing [] [] [] flags none) 2 := by
  have h := clear_store r (parsing [] [] [] flags none)
  have hs : (parsing [] [] [] flags none).stk = fun _ => [] := by funext k; cases k <;> rfl
  have he : (⟨((parsing [] [] [] flags none).state.1, none),
      Function.update (parsing [] [] [] flags none).stk r []⟩ : Data) =
      parsing [] [] [] flags none := by
    apply Store.ext
    · rfl
    · rw [hs]
      exact Function.update_eq_self _ _
  rw [he] at h
  simpa [hs] using! h

lemma cleanup_executes (xs ys : Word) (flags : Flags) (scratch : Option Bool) :
    Executes cleanup (parsing xs ys [] flags scratch) (parsing [] [] [] flags none)
      (2 * xs.length + 2 * ys.length + 10) := by
  have h := Executes.seq (parsing_clearInput xs ys flags scratch)
    (.seq (parsing_clearFormula xs flags) (.seq (parsing_clearEmpty .reverse flags)
      (.seq (parsing_clearEmpty .cursor flags) (parsing_clearEmpty .temporary flags))))
  convert! h using 1 <;> omega

lemma output_executes (flags : Flags) :
    Executes output (parsing [] [] [] flags none)
      (ioStore .output initial [flags.valid && flags.conjunction]) 2 := by
  let o : Op (fun _ : Register => Bool) Control := .push .output
    (fun s => s.1.valid && s.1.conjunction)
  have hp := Executes.atom o (parsing [] [] [] flags none)
  have hl := Executes.atom (.load (fun _ : Control => initial)) (o.apply (parsing [] [] [] flags none))
  have h := Executes.seq hp hl
  convert! h using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [Op.apply, parsing, ioStore, o]

end Lax429075Proofs.VerifierProgram
