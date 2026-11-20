import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRestrictedTensorProductIrreducibleCountableDimen.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.restrictedTensorProduct_irreducible_countable_dimension : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  first | exact @GlobalTheory.rtens_irreducible | exact GlobalTheory.rtens_irreducible | (intros; apply GlobalTheory.rtens_irreducible <;> assumption)
