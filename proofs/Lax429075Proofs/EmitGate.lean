import Lax429075Proofs.EmitFormula
import Lax429075.Tseitin

namespace Lax429075Proofs.CNFOutput

open Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
open Lax429075.Encoding Lax429075.CNF Lax429075.Circuits Lax429075.Tseitin

variable {K Aux : Type} [DecidableEq K]

inductive GateTemplate (K Aux : Type) where
  | input
  | constant (value : Aux → Bool)
  | neg (a : K)
  | conj (a b : K)
  | disj (a b : K)

def templateValue (v : K → ℕ) (a : Aux) : GateTemplate K Aux → Gate
  | .input => .input
  | .constant value => .constant (value a)
  | .neg i => .neg (v i)
  | .conj i j => .conj (v i) (v j)
  | .disj i j => .disj (v i) (v j)

def templateClauses (current : K) : GateTemplate K Aux → List (List (LiteralPort K Aux))
  | .input => []
  | .constant value => [[(current, value)]]
  | .neg i => [[(current, fun _ => true), (i, fun _ => true)],
      [(current, fun _ => false), (i, fun _ => false)]]
  | .conj i j => [[(current, fun _ => false), (i, fun _ => true)],
      [(current, fun _ => false), (j, fun _ => true)],
      [(current, fun _ => true), (i, fun _ => false), (j, fun _ => false)]]
  | .disj i j => [[(current, fun _ => true), (i, fun _ => false)],
      [(current, fun _ => true), (j, fun _ => false)],
      [(current, fun _ => false), (i, fun _ => true), (j, fun _ => true)]]

lemma templateClauses_value (current : K) (g : GateTemplate K Aux) (v : K → ℕ) (a : Aux) :
    formulaValue v a (templateClauses current g) = gateClauses (v current) (templateValue v a g) := by
  cases g <;> rfl

lemma templateClauses_count (current : K) (g : GateTemplate K Aux) :
    (templateClauses current g).length ≤ 3 := by cases g <;> simp [templateClauses]

lemma templateClause_length (current : K) (g : GateTemplate K Aux) (C : List (LiteralPort K Aux))
    (hC : C ∈ templateClauses current g) : C.length ≤ 3 := by
  cases g <;> simp_all [templateClauses] <;> aesop

def emitGate (out tmp current : K) (g : GateTemplate K Aux) : BitProgram K Aux :=
  emitFormula out tmp (templateClauses current g)

lemma emitGate_executes (out tmp current : K) (hot : out ≠ tmp) (g : GateTemplate K Aux)
    (v : K → ℕ) (s : BitStore K Aux) (bound : ℕ)
    (hports : ∀ C ∈ templateClauses current g, ∀ p ∈ C, p.1 ≠ out ∧ p.1 ≠ tmp)
    (hvalues : ∀ C ∈ templateClauses current g, ∀ p ∈ C, s.stk p.1 = List.replicate (v p.1) true)
    (hbound : ∀ C ∈ templateClauses current g, ∀ p ∈ C, v p.1 ≤ bound)
    (ht : s.stk tmp = []) (hs : s.state.2 = none) :
    ∃ t, t ≤ 70 * (bound + 1) ∧ Executes (emitGate out tmp current g) s
      (emitted out (segment (gateClauses (v current) (templateValue v s.state.1 g))) s) t := by
  have he := emitFormula_executes out tmp hot (templateClauses current g) v s hports hvalues ht hs
  rw [templateClauses_value] at he
  refine ⟨_, ?_, he⟩
  have hc := formulaCost_bound v (templateClauses current g) bound 3
    (templateClause_length current g) hbound
  have hl := templateClauses_count current g
  nlinarith

end Lax429075Proofs.CNFOutput
