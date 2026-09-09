import Lax434930.NondeterministicPolynomialTime

/-!
---
title: Polynomial many-one reductions and NP-completeness
type: definition
---
A polynomial many-one reduction is one polynomial time computable function
on binary words that preserves membership. A language is NP-complete if it
belongs to NP and every language in NP reduces to it.
-/

namespace Lax429075.Reductions

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

def NPComplete (B : Language) : Prop := B ∈ NP ∧ ∀ A : Language, A ∈ NP → ManyOne A B

end Lax429075.Reductions
