import Lax429075Proofs.LiteralExecution

namespace Lax429075Proofs.VerifierProgram

open Lax979537Proofs.StackProgram

lemma loop_suffix_step {p q : Code} {b : Control → Bool} {s u t : Data} {a c : ℕ}
    (hb : b s.state = true) (hp : Executes p s u a)
    (hrest : Executes (.seq (.loop b p) q) u t c) :
    Executes (.seq (.loop b p) q) s t (a + c + 1) := by
  cases hrest with
  | seq hl hq =>
    convert Executes.seq (.loop_true hb hp hl) hq using 1 <;> omega

end Lax429075Proofs.VerifierProgram
