import Lax979537Proofs.StackCopy
import Lax979537Proofs.StackClear
import Lax429075Proofs.DecoderSoundness

namespace Lax429075Proofs.VerifierProgram

open Lax434930.PolynomialTime Lax979537Proofs.StackProgram Lax979537Proofs.StackTransfer
open Lax979537Proofs

inductive Register where
  | input | formula | reverse | cursor | temporary | output
  deriving DecidableEq, Fintype

structure Flags where
  valid : Bool
  active : Bool
  conjunction : Bool
  clause : Bool
  deriving DecidableEq, Fintype

abbrev Control := Flags × Option Bool
abbrev Data := BitStore Register Flags
abbrev Code := BitProgram Register Flags

def initial : Control := (⟨true, true, true, false⟩, none)

local infixr:55 " ⋙ " => Program.seq

def assign (f : Flags → Flags) : Code := .atom (.load (fun s => (f s.1, s.2)))

def stop : Code := assign (fun s => {s with active := false})
def fail : Code := assign (fun s => {s with valid := false, active := false})

def decodingBody : Code :=
  .branch (fun s => s.2.isSome)
    (.branch (fun s => s.2.getD false) stop
      (read .input ⋙ .branch (fun s => s.2.isSome)
        (.atom (.push .reverse (fun s => s.2.getD false)) ⋙ read .input) fail)) fail

def decodingLoop : Code := .loop (fun s => s.1.active && s.1.valid) decodingBody

def decodePair : Code := read .input ⋙ decodingLoop ⋙ transfer .reverse .formula

def continuing (s : Control) : Bool := s.1.valid && decide (s.2 = some true)

def requireTerminator : Code := .atom (.load (fun s =>
  ({s.1 with valid := s.1.valid && decide (s.2 = some false)}, s.2)))

def indexBody : Code := .atom (.pop .cursor (fun s _ => s)) ⋙ read .formula

def readSign : Code := .atom (.pop .cursor (fun s value =>
  ({s.1 with
      valid := s.1.valid && s.2.isSome
      clause := s.1.clause || if s.2.getD false then value.getD false else !(value.getD false)}, none)))

def literal : Code :=
  StackCopy.copy .input .cursor .temporary ⋙ read .formula ⋙
    .loop continuing indexBody ⋙ requireTerminator ⋙ read .formula ⋙ readSign ⋙ StackClear.clear .cursor

def clauseBody : Code := literal ⋙ read .formula

def clause : Code :=
  assign (fun s => {s with clause := false}) ⋙ read .formula ⋙
    .loop continuing clauseBody ⋙ requireTerminator ⋙
    assign (fun s => {s with conjunction := s.conjunction && s.clause})

def formulaBody : Code := clause ⋙ read .formula

def formula : Code :=
  read .formula ⋙ .loop continuing formulaBody ⋙ requireTerminator ⋙ read .formula ⋙
    .atom (.load (fun s => ({s.1 with valid := s.1.valid && s.2.isNone}, s.2)))

def cleanup : Code :=
  StackClear.clear .input ⋙ StackClear.clear .formula ⋙ StackClear.clear .reverse ⋙
    StackClear.clear .cursor ⋙ StackClear.clear .temporary

def output : Code := .atom (.push .output (fun s => s.1.valid && s.1.conjunction)) ⋙
  .atom (.load (fun _ => initial))

def program : Code := decodePair ⋙ formula ⋙ cleanup ⋙ output

end Lax429075Proofs.VerifierProgram
