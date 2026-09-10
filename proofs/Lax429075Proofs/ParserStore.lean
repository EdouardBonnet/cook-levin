import Lax429075Proofs.UnaryParsing

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer

def parsing (xs ys cursor : Word) (flags : Flags) (scratch : Option Bool) : Data :=
  ⟨(flags, scratch), fun r => match r with
    | .input => ys
    | .formula => xs
    | .cursor => cursor
    | _ => []⟩

lemma parsing_read (xs ys cursor : Word) (flags : Flags) (scratch : Option Bool) :
    Executes (read .formula) (parsing xs ys cursor flags scratch)
      (parsing xs.tail ys cursor flags xs.head?) 1 := by
  convert Executes.atom (.pop Register.formula (fun s : Control => fun b => (s.1, b)))
    (parsing xs ys cursor flags scratch) using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [parsing, Op.apply]

lemma parsing_assign (f : Flags → Flags) (xs ys cursor : Word)
    (flags : Flags) (scratch : Option Bool) :
    Executes (assign f) (parsing xs ys cursor flags scratch)
      (parsing xs ys cursor (f flags) scratch) 1 := .atom _ _

lemma parsing_require (xs ys cursor : Word) (flags : Flags) (scratch : Option Bool) :
    Executes requireTerminator (parsing xs ys cursor flags scratch)
      (parsing xs ys cursor {flags with valid := flags.valid && decide (scratch = some false)}
        scratch) 1 := .atom _ _

lemma parsing_copy (xs ys : Word) (flags : Flags) (scratch : Option Bool) :
    Executes (Lax979537Proofs.StackCopy.copy .input .cursor .temporary)
      (parsing xs ys [] flags scratch) (parsing xs ys ys flags none) (7 * ys.length + 4) := by
  have h := Lax979537Proofs.StackCopy.copy_store .input .cursor .temporary
    (by decide) (by decide) (by decide) (parsing xs ys [] flags scratch) rfl
  convert h using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [parsing]

lemma parsing_clear (xs ys cursor : Word) (flags : Flags) (scratch : Option Bool) :
    Executes (Lax979537Proofs.StackClear.clear .cursor)
      (parsing xs ys cursor flags scratch) (parsing xs ys [] flags none)
      (2 * cursor.length + 2) := by
  have h := Lax979537Proofs.StackClear.clear_store .cursor (parsing xs ys cursor flags scratch)
  convert h using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [parsing]

end Lax429075Proofs.VerifierProgram
