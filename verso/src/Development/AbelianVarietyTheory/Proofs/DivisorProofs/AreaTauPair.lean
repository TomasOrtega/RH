import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.LatConst

/- English proof (translation)
Establish `h1 : (tauPair τ).ω₁ = (τ : ℂ)` using `rfl`. Establish `h2 : (tauPair τ).ω₂ = 1` using `rfl`. Rewrite using `[area, h1, h2]`. Simplify using `[abs_of_pos τ.im_pos]`.
-/
theorem area_tauPair (τ : ℍ) : area (tauPair τ) = τ.im := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [area, h1, h2]
  simp [abs_of_pos τ.im_pos]

/- English proof (translation)
Establish `h1 : (tauPair τ).ω₁ = (τ : ℂ)` using `rfl`. Establish `h2 : (tauPair τ).ω₂ = 1` using `rfl`. Establish `h` using `(etaEisenstein (tauPair τ)).2`. Rewrite `h` using `[h1, h2]`. Rewrite using `[h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]`.

Use `tsum_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[EisensteinSeries.e2Summand]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Simplify using `[EisensteinSeries.eisSummand, zpow_ofNat]`.
-/
theorem wEta_one (τ : ℍ) : wEta (tauPair τ) 1 = EisensteinSeries.G2 τ := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  have h := (etaEisenstein (tauPair τ)).2
  rw [h1, h2] at h
  rw [h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]
  refine tsum_congr fun m => ?_
  rw [EisensteinSeries.e2Summand]
  refine tsum_congr fun n => ?_
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

/- English proof (translation)
Introduce `τ`. Use `⟨?_, area_tauPair τ⟩` and prove the remaining obligations. Establish `h` using `etaSplit (tauPair τ) 1`. Rewrite `h` using `[wEta_one, area_tauPair]`. Rewrite using `[G2s, h]`.

Simplify using the standard rewrite rules.
-/
theorem main : ∀ τ : ℍ, s2 (tauPair τ) = G2s τ ∧ area (tauPair τ) = τ.im := by
  intro τ
  refine ⟨?_, area_tauPair τ⟩
  have h := etaSplit (tauPair τ) 1
  rw [wEta_one, area_tauPair] at h
  rw [G2s, h]
  simp

end GlobalTheory.WpFam.LatConst
