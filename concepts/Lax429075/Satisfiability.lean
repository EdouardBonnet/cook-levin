import Lax429075.Encoding
import Lax434930.Certificates

/-!
---
title: The satisfiability language and verifier
type: definition
---
SAT contains precisely the encodings of satisfiable CNF formulas.
A certificate is a finite list of truth values, extended by false outside
its length. The verifier accepts a paired formula encoding and certificate
when every clause is satisfied. Malformed encodings are outside the language.
-/

namespace Lax429075.Satisfiability

open CNF Encoding Lax434930.PolynomialTime Lax434930.Certificates

def assignment (y : Word) : Assignment := fun i => (y[i]?).getD false

def SAT : Language := {w | ∃ F, encodeCNF F = w ∧ Satisfiable F}

def Verifier : Language :=
  {z | ∃ (F : Formula) (y : Word), z = pair (encodeCNF F) y ∧ eval F (assignment y) = true}

end Lax429075.Satisfiability
