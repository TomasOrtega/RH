import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply F₀ (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)]`. Establish `h1 : algebraMap F₀ (LaurentSeries K₁) r = HahnSeries.ofPowerSeries ℤ K₁ (algebraMap F₀ (PowerSeries K₁) r)` using `rfl`. Establish `h2 : algebraMap F₀ (PowerSeries K₁) r = PowerSeries.C (R` using `K₁) (algebraMap F₀ K₁ r) := by first`. Consider the case `(rw [IsScalarTower.algebraMap_apply F₀ K₁ (PowerSeries K₁)]; rfl)`. Consider the case `exact MvPowerSeries.algebraMap_apply`.

Consider the case `exact PowerSeries.algebraMap_apply' r`. Consider the case `simp [Algebra.algebraMap_eq_smul_one]`. Simplify using `only [arcι, RingHom.comp_apply, MvPolynomial.algebraMap_apply, h1, h2]`.
-/
theorem arcS_pin (Dw : Datum H) (K₁ : Type) [Field K₁] {F₀ : Type} [Field F₀] [Algebra F₀ K₁] (r : F₀) :
    algebraMap F₀ (ArcS Dw K₁) r = arcι Dw K₁ (PowerSeries.C (R := K₁) (algebraMap F₀ K₁ r)) := by
  rw [IsScalarTower.algebraMap_apply F₀ (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)]
  have h1 : algebraMap F₀ (LaurentSeries K₁) r =
      HahnSeries.ofPowerSeries ℤ K₁ (algebraMap F₀ (PowerSeries K₁) r) := rfl
  have h2 : algebraMap F₀ (PowerSeries K₁) r = PowerSeries.C (R := K₁) (algebraMap F₀ K₁ r) := by
    first
      | (rw [IsScalarTower.algebraMap_apply F₀ K₁ (PowerSeries K₁)]; rfl)
      | exact MvPowerSeries.algebraMap_apply
      | exact PowerSeries.algebraMap_apply' r
      | simp [Algebra.algebraMap_eq_smul_one]
  simp only [arcι, RingHom.comp_apply, MvPolynomial.algebraMap_apply, h1, h2]

end Formalism.L2.Pj.QAt
