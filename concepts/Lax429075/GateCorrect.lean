import Lax429075.Tseitin

/-!
---
title: Correctness of gate clauses
type: lemma
---
The clauses for one gate hold exactly when its output agrees with its
Boolean operation.
-/

namespace Lax429075.GateCorrect

open CNF Circuits Tseitin

axiom correct (i : ℕ) (g : Gate) (ρ : Assignment) :
  eval (gateClauses i g) ρ = g.check ρ i

end Lax429075.GateCorrect
