import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace RhoSigmaFinite

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]`.
-/
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]

variable (E k) in

def rho : Measure (GA E k) := Measure.sum fun ξ : RowT E k k => Measure.dirac (ratGL E k (gam ξ))

omit [IsTotallyComplex E] in
/- English proof (translation)
Rewrite using `[rho]`. Use `infer_instance`.
-/
theorem rho_sFinite [Countable (RowT E k k)] : SFinite (rho E k) := by
  rw [rho]; infer_instance

omit [IsTotallyComplex E] in
/- English proof (translation)
Rewrite using `[rho, lintegral_sum_measure]`. Simplify using `only [lintegral_dirac]`.
-/
theorem lint_rho (F : GA E k → ℝ≥0∞) : ∫⁻ r, F r ∂rho E k = ∑' ξ : RowT E k k, F (ratGL E k (gam ξ)) := by
  rw [rho, lintegral_sum_measure]
  simp only [lintegral_dirac]

omit [IsTotallyComplex E] in
/- English proof (translation)
Distinguish the cases in `hi : Integrable (fun r => Φ (r * g)) (rho E k)`. Rewrite using `[rho, integral_sum_measure hi, sumF]`. Simplify using `only [integral_dirac]`. Rewrite using `[integral_undef hi, sumF, tsum_eq_zero_of_not_summable]`. Introduce `hs`.

Apply `hi` to reduce the goal to its premises. Use `⟨(hΦ.comp (measurable_mul_const g)).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[HasFiniteIntegral, lint_rho]`. Establish `h1 : Summable fun ξ : RowT E k k => ‖Φ (ratGL E k (gam ξ) * g)‖₊` using `NNReal.summable_coe.mp (by simpa using hs.norm)`. Establish `h2` using `ENNReal.tsum_coe_ne_top_iff_summable.mpr h1`.

Simplify `h2.lt_top` using `[enorm_eq_nnnorm]`.
-/
theorem int_rho (Φ : GA E k → ℂ) (hΦ : Measurable Φ) (g : GA E k) :
    ∫ r, Φ (r * g) ∂rho E k = sumF Φ g := by
  by_cases hi : Integrable (fun r => Φ (r * g)) (rho E k)
  · rw [rho, integral_sum_measure hi, sumF]
    simp only [integral_dirac]
  · rw [integral_undef hi, sumF, tsum_eq_zero_of_not_summable]
    intro hs
    apply hi
    refine ⟨(hΦ.comp (measurable_mul_const g)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lint_rho]
    have h1 : Summable fun ξ : RowT E k k => ‖Φ (ratGL E k (gam ξ) * g)‖₊ :=
      NNReal.summable_coe.mp (by simpa using hs.norm)
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mpr h1
    simpa [enorm_eq_nnnorm] using h2.lt_top

end RhoSigmaFinite

open RhoSigmaFinite in
set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Introduce `hQ1 hQ2 hN0 hN3 hN4a E _ _ _ k μ _ hk β hβ`. Establish `: Countable (RowT E k k)` using `(hN0 E k k hk le_rfl).2.2.2.2.2.2.1`. Establish `: SFinite (rho E k)` using `rho_sFinite`. Take `⟨hsf, hinv, hae⟩` from `(hN3 E k).1 (k - 1) (by omega)`. Establish `key : ∀ g, ∑' ξ : RowT E k k, ∫⁻ h, β ((ratGL E k (gam ξ))⁻¹ * h * g) ∂nuP E k (k - 1) = 1`.

Introduce `g`. Rewrite using `[← hN4a E k k hk le_rfl (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))]`. Conclude with `hβ.2 g`. Use `set β' : GA E k → ℝ≥0∞ := fun g => ∑' ξ : RowT E k k, β ((ratGL E k (gam ξ))⁻¹ * g) with hβ'`. Establish `hwt : IsWt (nuP E k (k - 1)) β'`.

Use `⟨Measurable.ennreal_tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [hβ']`. Rewrite using `[lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g))) fun ξ => (hβ.1.comp ((measurable_const_mul _).comp (measurable_mul_const g))).aemeasurable]`. Simplify `key g` using `only [mul_assoc]`. Establish `hH : ∀ᵐ h ∂nuP E k (k - 1), h ∈ {x : GA E k | ∃ γ, IsMir (k - 1) γ ∧ ratGL E k γ = x}` using `by filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩`.

Rewrite using `[hh, uu_eq_one (by omega) hu, mul_one]`. Conclude with `⟨γ, hγ, rfl⟩`. Establish `hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (k - 1) ∂rho E k = 1` using `fun g => by`. Rewrite using `[lint_rho]`. Conclude with `key g`.

Use `⟨β', hwt, fun Φ hΦ hΦi => ?_, fun Φ hΦ hΦi hint => ?_⟩` and prove the remaining obligations. Use `hQ1 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g)` as an intermediate fact. Rewrite using `[this]`. Simplify using `only [lint_rho]`. Use `(hQ2 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g) hint).2` as an intermediate fact.

Rewrite using `[this]`. Simplify using `only [int_rho Φ hΦ]`.
-/
theorem unipotent_integral_of : Q1 → Q2 → N0 → N3 → CosetIntegralParabolic → U0 := by
  intro hQ1 hQ2 hN0 hN3 hN4a E _ _ _ k μ _ hk β hβ
  have : Countable (RowT E k k) := (hN0 E k k hk le_rfl).2.2.2.2.2.2.1
  have : SFinite (rho E k) := rho_sFinite
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).1 (k - 1) (by omega)
  have key : ∀ g, ∑' ξ : RowT E k k, ∫⁻ h, β ((ratGL E k (gam ξ))⁻¹ * h * g) ∂nuP E k (k - 1) = 1 := by
    intro g
    rw [← hN4a E k k hk le_rfl (fun h => β (h * g)) (hβ.1.comp (measurable_mul_const g))]
    exact hβ.2 g
  set β' : GA E k → ℝ≥0∞ := fun g => ∑' ξ : RowT E k k, β ((ratGL E k (gam ξ))⁻¹ * g) with hβ'
  have hwt : IsWt (nuP E k (k - 1)) β' := by
    refine ⟨Measurable.ennreal_tsum fun ξ => hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_tsum (f := fun ξ h => β ((ratGL E k (gam ξ))⁻¹ * (h * g)))
      fun ξ => (hβ.1.comp ((measurable_const_mul _).comp (measurable_mul_const g))).aemeasurable]
    simpa only [mul_assoc] using key g
  have hH : ∀ᵐ h ∂nuP E k (k - 1), h ∈ {x : GA E k | ∃ γ, IsMir (k - 1) γ ∧ ratGL E k γ = x} := by
    filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
    rw [hh, uu_eq_one (by omega) hu, mul_one]
    exact ⟨γ, hγ, rfl⟩
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k (k - 1) ∂rho E k = 1 := fun g => by
    rw [lint_rho]; exact key g
  refine ⟨β', hwt, fun Φ hΦ hΦi => ?_, fun Φ hΦ hΦi hint => ?_⟩
  · have := hQ1 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g)
    rw [this]
    simp only [lint_rho]
  · have := (hQ2 (GA E k) μ (nuP E k (k - 1)) (rho E k) _ β' β hinv hH hwt hβ.1 hone Φ hΦ
      (by rintro _ ⟨γ, hγ, rfl⟩ g; exact hΦi γ hγ g) hint).2
    rw [this]
    simp only [int_rho Φ hΦ]

end PositivityTheory.AdelicQuotientData

end
