import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutive
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ValCmp.Invol.cofRel_invol` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCofactorTwistRelationDualWeightInvolutive.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1), CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  first | exact @GlobalTheory.ValCmp.Invol.cofRel_invol | exact GlobalTheory.ValCmp.Invol.cofRel_invol | (intros; apply GlobalTheory.ValCmp.Invol.cofRel_invol <;> assumption)
