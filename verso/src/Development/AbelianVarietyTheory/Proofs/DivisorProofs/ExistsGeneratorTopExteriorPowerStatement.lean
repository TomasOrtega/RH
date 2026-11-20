import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTopExteriorPower
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGeneratorTopExteriorPower.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_generator_top_exterior_power : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (L : Type) [AddCommGroup L] [Module R L]
    [Module.Free R L] [Module.Finite R L] (n : ℕ), Module.finrank R L = n →
    ∀ (e : Fin n → (L →ₗ[R] R)) (D : R), D ≠ 0 → (∀ ω : L →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range e)) →
    ∀ (l : ℕ), ∃ (δ₀ : L [⋀^Fin n]→ₗ[R] R) (u₀ : R), Submodule.span R {δ₀} = ⊤ ∧
      Matrix.detRowAlternating.compLinearMap (LinearMap.pi e) = u₀ • δ₀ ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        n • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  first | exact @GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le | exact GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le | (intros; apply GlobalTheory.DetSpan.wedge_eq_smul_gen_val_le <;> assumption)
