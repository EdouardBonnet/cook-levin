import Lax429075Proofs.LiteralParsing

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax429075.Encoding

def scanMany {α : Type} (parse : Word → Parsed α)
    (shrink : ∀ xs, (parse xs).rest.length ≤ xs.length) : Word → Parsed (List α)
  | [] => ⟨[], [], false⟩
  | false :: xs => ⟨[], xs, true⟩
  | true :: xs =>
    let a := parse xs
    let as := scanMany parse shrink a.rest
    ⟨a.value :: as.value, as.rest, a.valid && as.valid⟩
termination_by xs => xs.length
decreasing_by have h := shrink xs; simp only [List.length_cons]; omega

lemma scanMany_length {α : Type} (parse : Word → Parsed α)
    (shrink : ∀ xs, (parse xs).rest.length ≤ xs.length) (xs : Word) :
    (scanMany parse shrink xs).rest.length ≤ xs.length := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    cases xs with
    | nil => simp [scanMany]
    | cons b xs =>
      cases b with
      | false => simp [scanMany]
      | true =>
        have ha := shrink xs
        have hi := ih (parse xs).rest (by change _ < (true :: xs).length; simp; omega)
        simpa only [scanMany] using hi.trans (by simp; omega)

lemma scanMany_sound {α : Type} (parse : Word → Parsed α) (enc : α → Word)
    (shrink : ∀ xs, (parse xs).rest.length ≤ xs.length)
    (sound : ∀ xs, (parse xs).valid = true → xs = enc (parse xs).value ++ (parse xs).rest)
    (xs : Word) (hv : (scanMany parse shrink xs).valid = true) :
    xs = encodeList enc (scanMany parse shrink xs).value ++ (scanMany parse shrink xs).rest := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    cases xs with
    | nil => simp [scanMany] at hv
    | cons b xs =>
      cases b with
      | false => simp [scanMany, encodeList]
      | true =>
        have hh : (parse xs).valid = true ∧
            (scanMany parse shrink (parse xs).rest).valid = true := by
          simpa only [scanMany, Bool.and_eq_true] using hv
        have hi := ih (parse xs).rest
          (by have h := shrink xs; change _ < (true :: xs).length; simp; omega) hh.2
        have hw := congrArg (List.cons true) ((sound xs hh.1).trans (by rw [hi]))
        simpa only [scanMany, encodeList, List.cons_append, List.append_assoc] using hw

lemma scanMany_encoded {α : Type} (parse : Word → Parsed α) (enc : α → Word)
    (shrink : ∀ xs, (parse xs).rest.length ≤ xs.length)
    (complete : ∀ a xs, parse (enc a ++ xs) = ⟨a, xs, true⟩)
    (as : List α) (xs : Word) :
    scanMany parse shrink (encodeList enc as ++ xs) = ⟨as, xs, true⟩ := by
  induction as with
  | nil => simp [encodeList, scanMany]
  | cons a as ih =>
    simp only [encodeList, List.cons_append, List.append_assoc, scanMany, complete]
    simpa only [ih, Bool.true_and]

lemma scanLiteral_invalid_rest (xs : Word) (hv : (scanLiteral xs).valid = false) :
    (scanLiteral xs).rest = [] := by
  have hn : (unary xs).valid = false → (unary xs).rest = [] := by
    clear hv
    induction xs with
    | nil => simp [unary]
    | cons b xs ih => cases b <;> simp_all [unary]
  cases hu : (unary xs).valid with
  | false => simp [scanLiteral, hn hu]
  | true =>
    have hs : (unary xs).rest.head?.isSome = false := by simpa [scanLiteral, hu] using hv
    cases hr : (unary xs).rest <;> simp_all [scanLiteral]

lemma scanMany_invalid_rest {α : Type} (parse : Word → Parsed α)
    (shrink : ∀ xs, (parse xs).rest.length ≤ xs.length)
    (bad : ∀ xs, (parse xs).valid = false → (parse xs).rest = [])
    (xs : Word) (hv : (scanMany parse shrink xs).valid = false) :
    (scanMany parse shrink xs).rest = [] := by
  induction xs using WellFounded.induction (measure List.length).wf with
  | h xs ih =>
    cases xs with
    | nil => simp [scanMany]
    | cons b xs =>
      cases b with
      | false => simp [scanMany] at hv
      | true =>
        cases ha : (parse xs).valid with
        | false => simp [scanMany, bad xs ha]
        | true =>
          have hs : (scanMany parse shrink (parse xs).rest).valid = false := by
            simpa only [scanMany, ha, Bool.true_and] using hv
          simpa only [scanMany] using ih (parse xs).rest
            (by have h := shrink xs; change _ < (true :: xs).length; simp; omega) hs

end Lax429075Proofs.VerifierProgram
