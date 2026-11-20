import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq

noncomputable section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotProduct

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂]
  [MeasurableMul₂ G₁] [MeasurableMul₂ G₂] {T₁ : Subgroup G₁} {T₂ : Subgroup G₂}
  {ν₁ : Measure T₁} [SFinite ν₁] {ν₂ : Measure T₂} [SFinite ν₂] {ν : Measure (T₁.prod T₂)}

def split (t : T₁.prod T₂) : T₁ × T₂ :=
  (⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩)

/- English proof (translation)
The claim follows from `((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk ((measurable_snd.comp measurable_subtype_coe).subtype_mk)`.
-/
theorem measurable_split : Measurable (split : T₁.prod T₂ → T₁ × T₂) :=
  ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)

/- English proof (translation)
Establish `hm : Measurable fun p : T₁ × T₂ => ρ ((p.1 : G₁) * g.1, (p.2 : G₂) * g.2)` using `hρ.comp ((((measurable_subtype_coe.comp measurable_fst).mul_const g.1)).prodMk ((measurable_subtype_coe.comp measurable_snd).mul_const g.2))`. Rewrite using `[← lintegral_prod _ hm.aemeasurable, ← hν, lintegral_map hm measurable_split]`. Both sides reduce to the same expression.
-/
theorem lintegral_prod_subgroup (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : Measurable ρ) (g : G₁ × G₂) :
    ∫⁻ h : T₁.prod T₂, ρ ((h : G₁ × G₂) * g) ∂ν =
      ∫⁻ t₁ : T₁, ∫⁻ t₂ : T₂, ρ ((t₁ : G₁) * g.1, (t₂ : G₂) * g.2) ∂ν₂ ∂ν₁ := by
  have hm : Measurable fun p : T₁ × T₂ => ρ ((p.1 : G₁) * g.1, (p.2 : G₂) * g.2) :=
    hρ.comp ((((measurable_subtype_coe.comp measurable_fst).mul_const g.1)).prodMk
      ((measurable_subtype_coe.comp measurable_snd).mul_const g.2))
  rw [← lintegral_prod _ hm.aemeasurable, ← hν, lintegral_map hm measurable_split]
  rfl

/- English proof (translation)
Use `⟨Measurable.lintegral_prod_right' (f := fun p : G₁ × T₂ => ρ (p.1, (p.2 : G₂))) (hρ.1.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))), fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `hρ.2 (g, 1)`. Rewrite `h` using `[lintegral_prod_subgroup hν hρ.1]`. Simplify using `using h`.
-/
theorem normaliser_fst (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₁ ν₁ fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₁ × T₂ => ρ (p.1, (p.2 : G₂)))
    (hρ.1.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))), fun g => ?_⟩
  have h := hρ.2 (g, 1)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  simpa using h

/- English proof (translation)
Use `⟨Measurable.lintegral_prod_right' (f := fun p : G₂ × T₁ => ρ ((p.2 : G₁), p.1)) (hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk measurable_fst)), fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `hρ.2 (1, g)`. Rewrite `h` using `[lintegral_prod_subgroup hν hρ.1]`. Rewrite using `[lintegral_lintegral_swap]`. Simplify using `using h`.

Establish `hm : Measurable fun p : T₂ × T₁ => ρ ((p.2 : G₁), (p.1 : G₂) * g)` using `hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk ((measurable_subtype_coe.comp measurable_fst).mul_const g))`. Conclude with `hm.aemeasurable`.
-/
theorem normaliser_snd (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₂ ν₂ fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₂ × T₁ => ρ ((p.2 : G₁), p.1))
    (hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk measurable_fst)), fun g => ?_⟩
  have h := hρ.2 (1, g)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  rw [lintegral_lintegral_swap]
  · simpa using h
  · have hm : Measurable fun p : T₂ × T₁ => ρ ((p.2 : G₁), (p.1 : G₂) * g) :=
      hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk
        ((measurable_subtype_coe.comp measurable_fst).mul_const g))
    exact hm.aemeasurable

/- English proof (translation)
Establish `hm : Measurable fun x : G₁ × G₂ => ρ₁ x.1 * ρ₂ x.2` using `(h₁.1.comp measurable_fst).mul (h₂.1.comp measurable_snd)`. Use `⟨hm, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_prod_subgroup hν hm]`. Establish `hc : ∀ t₁ : T₁, ∫⁻ t₂ : T₂, ρ₁ ((t₁ : G₁) * g.1) * ρ₂ ((t₂ : G₂) * g.2) ∂ν₂ = ρ₁ ((t₁ : G₁) * g.1)` using `fun t₁ => by`. Establish `hm₂ : Measurable fun t₂ : T₂ => ρ₂ ((t₂ : G₂) * g.2)` using `h₂.1.comp (measurable_subtype_coe.mul_const g.2)`.

Rewrite using `[lintegral_const_mul _ hm₂, h₂.2, mul_one]`. Simplify using `only [hc]`. Conclude with `h₁.2 g.1`.
-/
theorem normaliser_mul (hν : ν.map split = ν₁.prod ν₂) {ρ₁ : G₁ → ℝ≥0∞} {ρ₂ : G₂ → ℝ≥0∞}
    (h₁ : IsQuotNormaliser T₁ ν₁ ρ₁) (h₂ : IsQuotNormaliser T₂ ν₂ ρ₂) :
    IsQuotNormaliser (T₁.prod T₂) ν fun x => ρ₁ x.1 * ρ₂ x.2 := by
  have hm : Measurable fun x : G₁ × G₂ => ρ₁ x.1 * ρ₂ x.2 :=
    (h₁.1.comp measurable_fst).mul (h₂.1.comp measurable_snd)
  refine ⟨hm, fun g => ?_⟩
  rw [lintegral_prod_subgroup hν hm]
  have hc : ∀ t₁ : T₁, ∫⁻ t₂ : T₂, ρ₁ ((t₁ : G₁) * g.1) * ρ₂ ((t₂ : G₂) * g.2) ∂ν₂ =
      ρ₁ ((t₁ : G₁) * g.1) := fun t₁ => by
    have hm₂ : Measurable fun t₂ : T₂ => ρ₂ ((t₂ : G₂) * g.2) :=
      h₂.1.comp (measurable_subtype_coe.mul_const g.2)
    rw [lintegral_const_mul _ hm₂, h₂.2, mul_one]
  simp only [hc]
  exact h₁.2 g.1

end GlobalTheory.CompanionTheory.QuotProduct

namespace GlobalTheory.CompanionTheory.QuotProduct

/- English proof (translation)
Introduce `G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν₁ _ _ ν₂ _ _ ν _ _ F hF hν hinv hfib`. Distinguish the cases in `hex : ∃ ρ, IsQuotNormaliser (T₁.prod T₂) ν ρ`. Take `⟨ρ, hρ⟩` from `hex`. Establish `hν' : ν.map split = ν₁.prod ν₂` using `hν`. Establish `n₁` using `normaliser_fst hν' hρ`.

Establish `n₂` using `normaliser_snd hν' hρ`. Establish `n` using `normaliser_mul hν' n₁ n₂`. Use `set ρ₁ : G₁ → ℝ≥0∞ := fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂`. Use `set ρ₂ : G₂ → ℝ≥0∞ := fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁`. Rewrite using `[GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hinv n]`.

Distinguish the cases in `hi : Integrable (fun x : G₁ × G₂ => F x * (((ρ₁ x.1 * ρ₂ x.2).toReal : ℝ) : ℂ)) (μ₁.prod μ₂)`. Rewrite using `[integral_prod_symm _ hi]`. Use `integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x₂ => ?_)` and prove the remaining obligations. Establish `hFx : Measurable fun x₁ => F (x₁, x₂)` using `hF.comp (measurable_id.prodMk measurable_const)`. Establish `hinvx : ∀ h ∈ T₁, ∀ g, F (h * g, x₂) = F (g, x₂)` using `fun h hh g => by`.

Simplify using `using hinv (h, 1) (Subgroup.mem_prod.2 ⟨hh, T₂.one_mem⟩) (g, x₂)`. Establish `hq` using `hfib x₂`. Rewrite `hq` using `[GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hFx hinvx n₁]`. Establish `: ∀ x₁, F (x₁, x₂) * (((ρ₁ x₁ * ρ₂ x₂).toReal : ℝ) : ℂ) = (F (x₁, x₂) * (((ρ₁ x₁).toReal : ℝ) : ℂ)) * (((ρ₂ x₂).toReal : ℝ) : ℂ)` using `fun x₁ => by`. Rewrite using `[ENNReal.toReal_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, Pi.zero_apply]`. Rewrite using `[integral_mul_const, hq, zero_mul]`. Conclude with `integral_undef hi`.

Simplify using `only [quotIntegral, dif_neg hex]`.
-/
theorem quotProd_holds : PositivityTheory.Rg.BcB.D4.QuotProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν₁ _ _ ν₂ _ _ ν _ _ F hF hν hinv hfib
  by_cases hex : ∃ ρ, IsQuotNormaliser (T₁.prod T₂) ν ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hν' : ν.map split = ν₁.prod ν₂ := hν
    have n₁ := normaliser_fst hν' hρ
    have n₂ := normaliser_snd hν' hρ
    have n := normaliser_mul hν' n₁ n₂
    set ρ₁ : G₁ → ℝ≥0∞ := fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂
    set ρ₂ : G₂ → ℝ≥0∞ := fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁
    rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hinv n]
    by_cases hi : Integrable (fun x : G₁ × G₂ => F x * (((ρ₁ x.1 * ρ₂ x.2).toReal : ℝ) : ℂ)) (μ₁.prod μ₂)
    · rw [integral_prod_symm _ hi]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      have hFx : Measurable fun x₁ => F (x₁, x₂) := hF.comp (measurable_id.prodMk measurable_const)
      have hinvx : ∀ h ∈ T₁, ∀ g, F (h * g, x₂) = F (g, x₂) := fun h hh g => by
        simpa using hinv (h, 1) (Subgroup.mem_prod.2 ⟨hh, T₂.one_mem⟩) (g, x₂)
      have hq := hfib x₂
      rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hFx hinvx n₁] at hq
      have : ∀ x₁, F (x₁, x₂) * (((ρ₁ x₁ * ρ₂ x₂).toReal : ℝ) : ℂ) =
          (F (x₁, x₂) * (((ρ₁ x₁).toReal : ℝ) : ℂ)) * (((ρ₂ x₂).toReal : ℝ) : ℂ) := fun x₁ => by
        rw [ENNReal.toReal_mul]; push_cast; ring
      simp only [this, Pi.zero_apply]
      rw [integral_mul_const, hq, zero_mul]
    · exact integral_undef hi
  · simp only [quotIntegral, dif_neg hex]

/- English proof (translation)
Introduce `_` and use `quotProd_holds`.
-/
theorem quotProd_of_normEq : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.D4.QuotProd :=
  fun _ => quotProd_holds

end GlobalTheory.CompanionTheory.QuotProduct

end
