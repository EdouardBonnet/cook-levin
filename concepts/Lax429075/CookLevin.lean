import Lax429075.Satisfiability
import Lax429075.Reductions

/-!
---
title: The Cook–Levin theorem
type: theorem
---
Satisfiability of CNF formulas is NP-complete under polynomial many-one reductions.
-/

namespace Lax429075.CookLevin

open Satisfiability Reductions

axiom np_complete : NPComplete SAT

end Lax429075.CookLevin
