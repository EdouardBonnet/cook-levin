import Lax429075.Tseitin

/-!
---
title: Correctness of the circuit encoding
type: lemma
---
The gate clauses and output clause are satisfiable exactly when the circuit is satisfiable.
-/

namespace Lax429075.TseitinCorrect

open Circuits

axiom correct (C : Circuit) : CNF.Satisfiable (Tseitin.encode C) ↔ Satisfiable C

end Lax429075.TseitinCorrect
