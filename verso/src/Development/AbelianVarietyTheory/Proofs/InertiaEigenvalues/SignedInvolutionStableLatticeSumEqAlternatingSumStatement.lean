import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumEqAlternatingSum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSignedInvolutionStableLatticeSumEqAlternatingSum.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.signedInvolutionStableLatticeSum_eq_alternating_sum : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), B.LieReg → IsFrame B e π S → ∀ I ⊆ S, ∀ u : B.A, IsUnit u → HH B π I (S \ I) u 1 = ∑ J ∈ S.powerset, (-1 : ℚ) ^ (J ∩ I).card * B.GG ((∏ j ∈ J, π j) * u) := by
  first | exact @GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG | exact GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG | (intros; apply GlobalTheory.UnitLemma.Desc.HH_eq_alternating_GG <;> assumption)
