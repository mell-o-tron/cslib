/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Pace
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation

@[expose] public section

/-! # Linear Temporal Logic

Linear Temporal Logic (LTL) is a logic for reasoning about the validity of propositional atoms
in non-branching time.


## Main definitions

- `Proposition`: the language of propositions, parametrized on the type of atoms.
- `linear_structure`: a linear structure is represented as a mapping from atoms to the
set of instants in time (expressed as natural numbers) in which such atom is satisfied.
- `Satisfies_ls lts s a`: in the LS `ls`, proposition `p` is satisfied.
## Main statements

## References

-/

namespace Cslib.Logic.LTL

/-- Propositions, where AType is the type of atoms. -/
inductive Proposition (AType : Type) : Type u where
  | true
  | false
  | not (φ₁ : Proposition AType)
  | and (φ₁ φ₂ : Proposition AType)
  | or (φ₁ φ₂ : Proposition AType)
  | next (φ : Proposition AType)
  | eventually (φ : Proposition AType)
  | always (φ : Proposition AType)
  | until_op (φ : Proposition AType) (φ : Proposition AType)
  | atom (p : AType)

/-- Linear Structures, where AType is the type of atoms. -/
def linear_structure (AType : Type) : Type := AType -> Set Nat

def shift (ls : linear_structure t) (k : Nat) :=
  fun (x : t) =>
    let res := ls (x);
    let filtered_set := {n | n >= k ∧ n ∈ res};
    filtered_set.image (fun n => n - k)

/-- Satisfaction relation for linear structures -/
def SatisfiesLS (ls : linear_structure t) (φ : Proposition t) := match φ with
  | .true => True
  | .false => False
  | .and φ₁ φ₂ => SatisfiesLS ls φ₁ ∧ SatisfiesLS ls φ₂
  | .or φ₁ φ₂ => SatisfiesLS ls φ₁ ∨ SatisfiesLS ls φ₂
  | .atom (p) => 0 ∈ (ls p)
  | .not φ => ¬ (SatisfiesLS ls φ)
  | .next φ => SatisfiesLS (shift ls 1) φ
  | .eventually φ => ∃ k : Nat, SatisfiesLS (shift ls k) φ
  | .always φ => ∀ k : Nat , SatisfiesLS (shift ls k) φ
  | .until_op φ₁ φ₂ => ∃ k , (SatisfiesLS (shift ls k) φ₂ ∧ (∀ i : Nat ,
      i >= k ∨ SatisfiesLS (shift ls i) φ₁))


/- TODO: Satisfaction on transition systems.
src https://pages.di.unipi.it/gadducci/SVV-24/slideB/svv_b_01.pdf -/

/- TODO: Büchi automaton construction -/

/- TODO: Equivalences between the above -/


end Cslib.Logic.LTL
