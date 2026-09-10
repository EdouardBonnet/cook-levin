import Lax429075Proofs.OutputTests
import Lax429075Proofs.EmitGate

namespace Lax429075Proofs.Streaming

open Lax434930.PolynomialTime Lax429075.CNF Lax429075.Encoding Lax429075.Circuits Lax429075.Tseitin
open CNFOutput

variable {I : Type}

abbrev LiteralCode (I : Type) := Number I × Test I

def LiteralCode.value (l : LiteralCode I) (a : I → Word) : Literal := ⟨l.1.value a, l.2.value a⟩

def LiteralCode.code (l : LiteralCode I) : Code I :=
  .append l.1.code (.append (.literal [false]) l.2.code)

lemma LiteralCode.correct (l : LiteralCode I) (a : I → Word) :
    l.code.eval a = encodeLiteral (l.value a) := by
  simp [code, Code.eval, Number.correct, Test.correct, value, encodeLiteral, encodeNat]

def Code.clause : List (LiteralCode I) → Code I
  | [] => .literal [false]
  | l :: ls => .append (.literal [true]) (.append l.code (Code.clause ls))

lemma Code.eval_clause (C : List (LiteralCode I)) (a : I → Word) :
    (Code.clause C).eval a = encodeClause (C.map fun l => l.value a) := by
  induction C <;> simp_all [clause, Code.eval, LiteralCode.correct, encodeClause, encodeList]

def Code.segment : List (List (LiteralCode I)) → Code I
  | [] => .literal []
  | C :: Cs => .append (.literal [true]) (.append (Code.clause C) (Code.segment Cs))

lemma Code.eval_segment (F : List (List (LiteralCode I))) (a : I → Word) :
    (Code.segment F).eval a = CNFOutput.segment (F.map fun C => C.map fun l => l.value a) := by
  induction F <;> simp_all [Code.segment, Code.eval, Code.eval_clause, CNFOutput.segment]

inductive GateCode (I : Type) where
  | input
  | constant (b : Test I)
  | neg (n : Number I)
  | conj (n m : Number I)
  | disj (n m : Number I)

def GateCode.value (g : GateCode I) (a : I → Word) : Gate :=
  match g with
  | .input => .input
  | .constant b => .constant (b.value a)
  | .neg n => .neg (n.value a)
  | .conj n m => .conj (n.value a) (m.value a)
  | .disj n m => .disj (n.value a) (m.value a)

def GateCode.clauses (i : Number I) : GateCode I → List (List (LiteralCode I))
  | .input => []
  | .constant b => [[(i, b)]]
  | .neg n => [[(i, .constant true), (n, .constant true)], [(i, .constant false), (n, .constant false)]]
  | .conj n m => [[(i, .constant false), (n, .constant true)],
      [(i, .constant false), (m, .constant true)],
      [(i, .constant true), (n, .constant false), (m, .constant false)]]
  | .disj n m => [[(i, .constant true), (n, .constant false)],
      [(i, .constant true), (m, .constant false)],
      [(i, .constant false), (n, .constant true), (m, .constant true)]]

def GateCode.code (i : Number I) (g : GateCode I) : Code I := Code.segment (g.clauses i)

lemma GateCode.correct (i : Number I) (g : GateCode I) (a : I → Word) :
    (g.code i).eval a = CNFOutput.segment (gateClauses (i.value a) (g.value a)) := by
  rw [GateCode.code, Code.eval_segment]
  cases g <;> rfl

def gatesWord (start : ℕ) (gates : List Gate) : Word :=
  (gates.zipIdx start).flatMap (fun gi => CNFOutput.segment (gateClauses gi.2 gi.1))

lemma gatesWord_nil (start : ℕ) : gatesWord start [] = [] := rfl

lemma gatesWord_singleton (start : ℕ) (g : Gate) :
    gatesWord start [g] = CNFOutput.segment (gateClauses start g) := by simp [gatesWord]

lemma gatesWord_append (start : ℕ) (as bs : List Gate) :
    gatesWord start (as ++ bs) = gatesWord start as ++ gatesWord (start + as.length) bs := by
  simp [gatesWord, List.zipIdx_append, Nat.add_comm]

end Lax429075Proofs.Streaming
