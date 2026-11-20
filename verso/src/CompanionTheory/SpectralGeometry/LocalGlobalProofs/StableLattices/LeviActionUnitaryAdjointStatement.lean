import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionUnitaryAdjoint
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLeviActionUnitaryAdjoint.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.levi_action_unitary_adjoint : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), KUnit ε E → ∀ p q : Fin n, ε p = ε q → ∀ x z : Cn n V,
      ∑ A, ⟪lF E p q x A, z A⟫_ℂ = ∑ A, ⟪x A, lF E q p z A⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint | exact GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint | (intros; apply GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint <;> assumption)
