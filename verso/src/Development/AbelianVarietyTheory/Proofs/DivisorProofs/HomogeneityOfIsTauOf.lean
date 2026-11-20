import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam

/- English proof (translation)
Rewrite using `[← L.deriv_weierstrassP, ← L'.deriv_weierstrassP, Formalism.L2.Th1.F.LatOnly.wp_eq h]`.
-/
theorem derivWeierstrassP_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  rw [← L.deriv_weierstrassP, ← L'.deriv_weierstrassP, Formalism.L2.Th1.F.LatOnly.wp_eq h]

/- English proof (translation)
Unfold `PeriodPair.derivWeierstrassP`. Establish `hs` using `Formalism.L2.Th1.F.Homog.tsum_scale L c hc (fun w => 2 / (c * z - w) ^ 3)`. Rewrite using `[hs]`. Establish `hterm : ∀ l : L.lattice, 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3)`. Introduce `l`.

Rewrite using `[← mul_sub, mul_pow, div_mul_eq_div_div, div_eq_inv_mul (2 / c ^ 3), div_eq_mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tsum_congr hterm, tsum_mul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivWeierstrassP_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  have hs := Formalism.L2.Th1.F.Homog.tsum_scale L c hc (fun w => 2 / (c * z - w) ^ 3)
  rw [hs]
  have hterm : ∀ l : L.lattice, 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3) := by
    intro l
    rw [← mul_sub, mul_pow, div_mul_eq_div_div, div_eq_inv_mul (2 / c ^ 3), div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  ring

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[h.2 x, Formalism.L2.Th1.F.Homog.mem_scale, PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, rfl⟩`. Use `⟨u, v, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(u : ℂ) * (τ : ℂ) + (v : ℂ) * 1 = c⁻¹ * (c * ((u : ℂ) * (τ : ℂ) + (v : ℂ)))`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ h.1, one_mul, mul_one]`. Introduce and unpack `⟨m, n, hmn⟩`. Use `⟨m, n, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(m : ℂ) * (τ : ℂ) + (n : ℂ) * 1 = c⁻¹ * x at hmn`.

Rewrite `hmn` using `[mul_one]`. Rewrite using `[hmn, ← mul_assoc, mul_inv_cancel₀ h.1, one_mul]`.
-/
theorem lattice_eq_scalePair_tauPair {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.lattice = (scalePair (tauPair τ) c h.1).lattice := by
  ext x
  rw [h.2 x, Formalism.L2.Th1.F.Homog.mem_scale, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨u, v, rfl⟩
    refine ⟨u, v, ?_⟩
    change (u : ℂ) * (τ : ℂ) + (v : ℂ) * 1 = c⁻¹ * (c * ((u : ℂ) * (τ : ℂ) + (v : ℂ)))
    rw [← mul_assoc, inv_mul_cancel₀ h.1, one_mul, mul_one]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (τ : ℂ) + (n : ℂ) * 1 = c⁻¹ * x at hmn
    rw [mul_one] at hmn
    rw [hmn, ← mul_assoc, mul_inv_cancel₀ h.1, one_mul]

/- English proof (translation)
Introduce `L c τ h`. Establish `hl` using `lattice_eq_scalePair_tauPair h`. Use `⟨fun z => ?_, fun z => ?_, fun z => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hl, Formalism.L2.Th1.F.Homog.mem_scale, ← mul_assoc, inv_mul_cancel₀ h.1, one_mul]`. Rewrite using `[Formalism.L2.Th1.F.LatOnly.wp_eq hl, Formalism.L2.Th1.F.Homog.wp_scale]`.

Rewrite using `[derivWeierstrassP_eq_of_lattice_eq hl, derivWeierstrassP_scalePair]`. Rewrite using `[Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq hl, Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale]`. Rewrite using `[Formalism.L2.Th1.F.LatOnly.area_eq hl, Formalism.L2.Th1.F.Homog.area_scale]`.
-/
theorem homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  intro L c τ h
  have hl := lattice_eq_scalePair_tauPair h
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hl, Formalism.L2.Th1.F.Homog.mem_scale, ← mul_assoc, inv_mul_cancel₀ h.1, one_mul]
  · rw [Formalism.L2.Th1.F.LatOnly.wp_eq hl, Formalism.L2.Th1.F.Homog.wp_scale]
  · rw [derivWeierstrassP_eq_of_lattice_eq hl, derivWeierstrassP_scalePair]
  · rw [Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq hl, Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale]
  · rw [Formalism.L2.Th1.F.LatOnly.area_eq hl, Formalism.L2.Th1.F.Homog.area_scale]

end GlobalTheory.WpFam
