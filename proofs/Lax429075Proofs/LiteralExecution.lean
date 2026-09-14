import Lax429075Proofs.LiteralParsing

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram Lax429075.CNF
open Lax429075.Satisfiability

lemma parsing_sign (xs ys cursor : Word) (flags : Flags) (scratch : Option Bool) :
    Executes readSign (parsing xs ys cursor flags scratch)
      (parsing xs ys cursor.tail
        {flags with
          valid := flags.valid && scratch.isSome
          clause := flags.clause || if scratch.getD false then cursor.head?.getD false
            else !(cursor.head?.getD false)} none) 1 := by
  convert! Executes.atom (.pop Register.cursor (fun s : Control => fun value =>
    ({s.1 with
      valid := s.1.valid && s.2.isSome
      clause := s.1.clause || if s.2.getD false then value.getD false else !(value.getD false)}, none)))
    (parsing xs ys cursor flags scratch) using 1
  apply Store.ext
  · rfl
  · funext r
    cases r <;> simp [parsing, Op.apply]

lemma literal_executes (xs ys : Word) (flags : Flags) (scratch : Option Bool)
    (hv : flags.valid = true) :
    Executes literal (parsing xs ys [] flags scratch)
      (parsing (scanLiteral xs).rest ys [] (literalFlags xs ys flags) none)
      (literalCost xs ys) := by
  let u := unary xs
  let cursor := ys.drop u.index
  let f : Flags := {flags with valid := u.valid}
  let g : Flags := {f with
    valid := f.valid && u.rest.head?.isSome
    clause := f.clause || if u.rest.head?.getD false then cursor.head?.getD false
      else !(cursor.head?.getD false)}
  have h₁ := parsing_copy xs ys flags scratch
  have h₂ := parsing_read xs ys ys flags none
  have h₃ := indexLoop_executes xs ys ys flags hv
  have h₄ : Executes requireTerminator
      (parsing u.rest ys cursor flags (if u.valid then some false else none))
      (parsing u.rest ys cursor f (if u.valid then some false else none)) 1 := by
    convert! parsing_require u.rest ys cursor flags (if u.valid then some false else none) using 1
    congr 2
    cases hu : u.valid <;> simp [f, hv, hu]
  have h₅ := parsing_read u.rest ys cursor f (if u.valid then some false else none)
  have h₆ := parsing_sign u.rest.tail ys cursor f u.rest.head?
  have h₇ := parsing_clear u.rest.tail ys cursor.tail g none
  have hg : g = literalFlags xs ys flags := by
    simp [g, f, cursor, u, literalFlags, scanLiteral, Literal.eval, assignment,
      List.head?_drop]
  have h := Executes.seq h₁ (.seq h₂ (.seq h₃ (.seq h₄ (.seq h₅ (.seq h₆ h₇)))))
  rw [hg] at h
  convert! h using 1 <;> simp [literalCost, cursor, u] <;> omega

end Lax429075Proofs.VerifierProgram
