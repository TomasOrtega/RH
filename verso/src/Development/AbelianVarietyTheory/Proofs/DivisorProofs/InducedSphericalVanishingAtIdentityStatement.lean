import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedSphericalVanishingAtIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInducedSphericalVanishingAtIdentity.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.induced_spherical_vanishing_at_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ), ∀ f ∈ indSp a a' α β,
    (∀ u ∈ KO k (Fin (a + a')), ∀ h, f (h * u) = f h) → f 1 = 0 → f = 0 := by
  first | exact @GlobalTheory.IndSpK.eq_zero_of_KO_invariant_of_apply_one | exact GlobalTheory.IndSpK.eq_zero_of_KO_invariant_of_apply_one | (intros; apply GlobalTheory.IndSpK.eq_zero_of_KO_invariant_of_apply_one <;> assumption)
