import Lax429075Proofs.TapeWindow

namespace Lax429075Proofs.WindowMachine

open AbsoluteTape

abbrev Position (radius : ℕ) := Fin (2 * radius + 1)

def coordinate (radius : ℕ) (i : Position radius) : ℤ := (i.val : ℤ) - radius

def position (radius : ℕ) (j : ℤ) : Position radius :=
  ⟨(j + radius).toNat % (2 * radius + 1), Nat.mod_lt _ (by omega)⟩

lemma coordinate_inside (radius : ℕ) (i : Position radius) : Inside radius (coordinate radius i) := by
  have h := i.isLt
  dsimp [Inside, coordinate]
  omega

lemma coordinate_position (radius : ℕ) (j : ℤ) (h : Inside radius j) :
    coordinate radius (position radius j) = j := by
  have hz : 0 ≤ j + radius := by dsimp [Inside] at h; omega
  have ht : (j + radius).toNat < 2 * radius + 1 := by dsimp [Inside] at h; omega
  simp only [coordinate, position, Nat.mod_eq_of_lt ht]
  omega

lemma position_coordinate (radius : ℕ) (i : Position radius) :
    position radius (coordinate radius i) = i := by
  apply Fin.ext
  simp [position, coordinate, Nat.mod_eq_of_lt i.isLt]

lemma coordinate_injective (radius : ℕ) : Function.Injective (coordinate radius) := by
  intro i j h
  have he := congrArg (position radius) h
  simpa only [position_coordinate] using he

end Lax429075Proofs.WindowMachine
