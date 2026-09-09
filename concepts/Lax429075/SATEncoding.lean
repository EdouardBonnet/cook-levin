import Lax429075.SAT

/-!
---
title: Satisfiability and binary encodings
type: lemma
---
An encoded formula belongs to the SAT language exactly when the formula is satisfiable.
-/

namespace Lax429075.SATEncoding

open CNF Encoding SAT

axiom correct (F : Formula) : encodeCNF F ∈ SAT ↔ Satisfiable F

end Lax429075.SATEncoding
