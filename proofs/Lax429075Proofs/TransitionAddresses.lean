import Lax429075Proofs.InitialBitCode

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax554803.MachineModels
open MachineCircuit WindowMachine CircuitBuilder

variable {I : Type}

def affineAddress (base pitch index : ℕ) : ℕ := base + (index + 1) * pitch - 1

def wireNumber (base pitch index : Number I) : Number I :=
  (base.add ((index.add (.constant 1)).mul pitch)).sub (.constant 1)

lemma wireNumber_value (base pitch index : Number I) (a : I → Word) :
    (wireNumber base pitch index).value a = affineAddress (base.value a) (pitch.value a) (index.value a) := rfl

def headIndexNumber (M : SingleTape) (position : Number I) : Number I :=
  (Number.constant (Fintype.card M.Q)).add position

noncomputable def cellIndexNumber (M : SingleTape) (radius position : Number I) (symbol : M.Γ) : Number I :=
  (((Number.constant (Fintype.card M.Q)).add (windowNumber radius)).add
    (position.mul (.constant (Fintype.card M.Γ)))).add (.constant (symbolIndex M symbol))

lemma move_left_value (radius : ℕ) (i : Position radius) :
    (position radius (coordinate radius i - 1)).val = i.val - 1 := by
  have h := i.isLt
  have he : ((i.val : ℤ) - radius - 1 + radius).toNat = i.val - 1 := by omega
  simp only [position, coordinate, he]
  exact Nat.mod_eq_of_lt (by omega)

lemma move_right_value (radius : ℕ) (i : Position radius) :
    (position radius (coordinate radius i + 1)).val =
      if i.val + 1 < 2 * radius + 1 then i.val + 1 else 0 := by
  have h := i.isLt
  have he : ((i.val : ℤ) - radius + 1 + radius).toNat = i.val + 1 := by omega
  simp only [position, coordinate, he]
  split_ifs with hi
  · exact Nat.mod_eq_of_lt hi
  · have hh : i.val + 1 = 2 * radius + 1 := by omega
    rw [hh, Nat.mod_self]

def nextPositionNumber (M : SingleTape) (radius position : Number I) (q : M.Q) (symbol : M.Γ) : Number I :=
  match M.transition q symbol with
  | some (_, .move .left) => position.sub (.constant 1)
  | some (_, .move .right) => Number.choose
      (Test.lt (position.add (.constant 1)) (windowNumber radius)) (position.add (.constant 1)) (.constant 0)
  | _ => position

lemma nextPositionNumber_value (M : SingleTape) (radius position : Number I) (q : M.Q) (symbol : M.Γ)
    (a : I → Word) (i : Position (radius.value a)) (hi : position.value a = i.val) :
    (nextPositionNumber M radius position q symbol).value a = (nextPosition M (radius.value a) q i symbol).val := by
  cases ht : M.transition q symbol with
  | none => simpa [nextPositionNumber, nextPosition, ht] using hi
  | some p =>
    obtain ⟨q', op⟩ := p
    cases op with
    | write s => simpa [nextPositionNumber, nextPosition, ht] using hi
    | move dir =>
      cases dir <;> simp [nextPositionNumber, nextPosition, ht, Number.sub, Number.add, Number.constant,
        Number.choose, Test.lt, windowNumber, Number.mul, hi, move_left_value, move_right_value]

end Lax429075Proofs.Streaming
