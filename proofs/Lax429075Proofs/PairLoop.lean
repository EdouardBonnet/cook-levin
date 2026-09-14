import Lax429075Proofs.PairSteps

set_option backward.isDefEq.respectTransparency false

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram

lemma decodingLoop_end (base : Register → Word) (xs rev : Word) (conj disj : Bool) :
    Executes decodingLoop (decodingData base (true :: xs) rev conj disj)
      (decodingDone base ⟨[], xs, true⟩ rev conj disj) 5 :=
  .loop_true rfl (decodingBody_end base xs rev conj disj) (.loop_false rfl)

lemma decodingLoop_empty (base : Register → Word) (rev : Word) (conj disj : Bool) :
    Executes decodingLoop (decodingData base [] rev conj disj)
      (decodingDone base ⟨[], [], false⟩ rev conj disj) 4 :=
  .loop_true rfl (decodingBody_empty base rev conj disj) (.loop_false rfl)

lemma decodingLoop_incomplete (base : Register → Word) (rev : Word) (conj disj : Bool) :
    Executes decodingLoop (decodingData base [false] rev conj disj)
      (decodingDone base ⟨[], [], false⟩ rev conj disj) 7 :=
  .loop_true rfl (decodingBody_incomplete base rev conj disj) (.loop_false rfl)

lemma decodingDone_cons (base : Register → Word) (xs rev : Word) (b conj disj : Bool) :
    decodingDone base (splitInput xs) (b :: rev) conj disj =
      decodingDone base (splitInput (false :: b :: xs)) rev conj disj := by
  simp [decodingDone, splitInput, List.reverse_cons, List.append_assoc]

lemma decodingLoop_executes (base : Register → Word) (xs rev : Word) (conj disj : Bool) :
    Executes decodingLoop (decodingData base xs rev conj disj)
      (decodingDone base (splitInput xs) rev conj disj) (decodeCost xs) := by
  induction xs using List.twoStepInduction generalizing rev with
  | nil => exact decodingLoop_empty base rev conj disj
  | singleton b =>
    cases b with
    | false => exact decodingLoop_incomplete base rev conj disj
    | true => exact decodingLoop_end base [] rev conj disj
  | cons_cons b c xs ih _ =>
    cases b with
    | true => exact decodingLoop_end base (c :: xs) rev conj disj
    | false =>
      have h := Executes.loop_true (b := fun s : Control => s.1.active && s.1.valid) rfl
        (decodingBody_cons base xs rev c conj disj) (ih (c :: rev))
      rw [decodingDone_cons] at h
      have ht : 6 + decodeCost xs + 1 = 7 + decodeCost xs := by omega
      simpa only [ht] using! h

end Lax429075Proofs.VerifierProgram
