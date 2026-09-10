import Lax429075Proofs.ParserStore

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax979537Proofs.StackProgram

lemma indexBody_executes (xs ys cursor : Word) (flags : Flags) (scratch : Option Bool) :
    Executes indexBody (parsing xs ys cursor flags scratch)
      (parsing xs.tail ys cursor.tail flags xs.head?) 2 := by
  have hp := Executes.atom (.pop Register.cursor (fun s : Control => fun _ => s))
    (parsing xs ys cursor flags scratch)
  have heq : Op.apply (.pop Register.cursor (fun s : Control => fun _ => s))
      (parsing xs ys cursor flags scratch) = parsing xs ys cursor.tail flags scratch := by
    apply Store.ext
    · rfl
    · funext r
      cases r <;> simp [parsing, Op.apply]
  rw [heq] at hp
  exact .seq hp (parsing_read xs ys cursor.tail flags scratch)

lemma indexLoop_executes (xs ys cursor : Word) (flags : Flags) (hv : flags.valid = true) :
    Executes (.loop continuing indexBody) (parsing xs.tail ys cursor flags xs.head?)
      (parsing (unary xs).rest ys (cursor.drop (unary xs).index) flags
        (if (unary xs).valid then some false else none)) (3 * (unary xs).index + 1) := by
  induction xs generalizing cursor with
  | nil => exact .loop_false (by simp [continuing, parsing])
  | cons b xs ih =>
    cases b with
    | false => exact .loop_false (by simp [continuing, parsing])
    | true =>
      have h := Executes.loop_true (b := continuing)
        (by simp [continuing, parsing, hv])
        (indexBody_executes xs ys cursor flags (some true)) (ih cursor.tail)
      have ht : 2 + (3 * (unary xs).index + 1) + 1 = 3 * ((unary xs).index + 1) + 1 := by omega
      simpa [unary, ht, List.drop_tail] using h

end Lax429075Proofs.VerifierProgram
