import Lax429075.Circuits

/-!
---
title: Gate clauses
type: definition
---
The Tseitin encoding assigns one variable to each gate. At most three
clauses enforce a gate's truth table, and a unit clause requires a true
output. Input gates have no constraints.
-/

namespace Lax429075.Tseitin

open CNF Circuits

def positive (i : ℕ) : Literal := ⟨i, true⟩
def negative (i : ℕ) : Literal := ⟨i, false⟩

def gateClauses (i : ℕ) : Gate → Formula
  | .input => []
  | .constant b => [[⟨i, b⟩]]
  | .neg a => [[positive i, positive a], [negative i, negative a]]
  | .conj a b => [[negative i, positive a], [negative i, positive b],
      [positive i, negative a, negative b]]
  | .disj a b => [[positive i, negative a], [positive i, negative b],
      [negative i, positive a, positive b]]

def encode (C : Circuit) : Formula :=
  [[positive C.output]] ++ C.gates.zipIdx.flatMap (fun gi => gateClauses gi.2 gi.1)

end Lax429075.Tseitin
