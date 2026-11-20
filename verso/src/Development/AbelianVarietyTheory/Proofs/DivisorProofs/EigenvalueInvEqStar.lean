import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.DoubleCosetAdjoint

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (φ : G → ℂ)

/- English proof (translation)
Use `(GlobalTheory.fundamentalDomain_integral_mul_right μ Γ 𝓕 (fun g => star (φ (g * x)) * φ (g * y)) c h (fun γ hγ g => by simp only [mul_assoc, hΓ γ hγ])).2` as an intermediate fact. Simplify `this` using `only [mul_assoc]`.
-/
theorem pairing_shift (h : IsFundamentalDomain Γ 𝓕 μ) (hΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g)
    (c x y : G) :
    ∫ g in 𝓕, star (φ (g * (c * x))) * φ (g * (c * y)) ∂μ
      = ∫ g in 𝓕, star (φ (g * x)) * φ (g * y) ∂μ := by
  have := (GlobalTheory.fundamentalDomain_integral_mul_right μ Γ 𝓕
    (fun g => star (φ (g * x)) * φ (g * y)) c h
    (fun γ hγ g => by simp only [mul_assoc, hΓ γ hγ])).2
  simpa only [mul_assoc] using this

/- English proof (translation)
Establish `h1 : ∀ z : G, IntegrableOn (fun g => star (φ (g * z)) * φ (g * z)) 𝓕 μ` using `fun z => (GlobalTheory.fundamentalDomain_integral_mul_right μ Γ 𝓕 (fun g => star (φ g) * φ g) z h (fun γ hγ g => by simp only [hΓ γ hγ])).1.1 hi`. Use `Integrable.mono' ((h1 x).norm.add (h1 y).norm) ?_ (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `(Continuous.mul (continuous_star.comp (hc.comp (continuous_mul_right x))) (hc.comp (continuous_mul_right y))).aestronglyMeasurable`. Simplify using `only [norm_mul, norm_star, Pi.add_apply]`. Use polynomial arithmetic with `[sq_nonneg (‖φ (g * x)‖ - ‖φ (g * y)‖), norm_nonneg (φ (g * x)), norm_nonneg (φ (g * y)), mul_nonneg (norm_nonneg (φ (g * x))) (norm_nonneg (φ (g * y)))]`.
-/
theorem pairing_integrable (h : IsFundamentalDomain Γ 𝓕 μ) (hc : Continuous φ)
    (hΓ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g)
    (hi : IntegrableOn (fun g => star (φ g) * φ g) 𝓕 μ) (x y : G) :
    IntegrableOn (fun g => star (φ (g * x)) * φ (g * y)) 𝓕 μ := by
  have h1 : ∀ z : G, IntegrableOn (fun g => star (φ (g * z)) * φ (g * z)) 𝓕 μ := fun z =>
    (GlobalTheory.fundamentalDomain_integral_mul_right μ Γ 𝓕
      (fun g => star (φ g) * φ g) z h
      (fun γ hγ g => by simp only [hΓ γ hγ])).1.1 hi
  refine Integrable.mono' ((h1 x).norm.add (h1 y).norm) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (Continuous.mul (continuous_star.comp (hc.comp (continuous_mul_right x)))
      (hc.comp (continuous_mul_right y))).aestronglyMeasurable
  · simp only [norm_mul, norm_star, Pi.add_apply]
    nlinarith [sq_nonneg (‖φ (g * x)‖ - ‖φ (g * y)‖), norm_nonneg (φ (g * x)),
      norm_nonneg (φ (g * y)), mul_nonneg (norm_nonneg (φ (g * x))) (norm_nonneg (φ (g * y)))]

end

/- English proof (translation)
Introduce `G _ _ _ _ _ _ μ _ _ Γ J _ 𝓕 φ α R R' a b h hc hΓ hJ hi hne hR hR' hcard ha hb`. Establish `e1 : ∀ γ ∈ R, ∫ g in 𝓕, star (φ (g * γ)) * φ (g * 1) ∂μ = ∫ g in 𝓕, star (φ (g * 1)) * φ (g * α⁻¹) ∂μ`. Introduce `γ hγ`. Take `⟨k₁, k₂, rfl⟩` from `hR.1 γ hγ`. Rewrite using `[← pairing_shift μ Γ 𝓕 φ h hΓ α 1 α⁻¹, ← pairing_shift μ Γ 𝓕 φ h hΓ (k₁ : G) (α * 1) (α * α⁻¹)]`.

Simplify using `only [mul_one, mul_inv_cancel, ← mul_assoc, hJ _ k₁.2, hJ _ k₂.2]`. Establish `e2 : ∀ γ ∈ R', ∫ g in 𝓕, star (φ (g * 1)) * φ (g * γ) ∂μ = ∫ g in 𝓕, star (φ (g * 1)) * φ (g * α⁻¹) ∂μ`. Introduce `γ hγ`. Take `⟨k₁, k₂, rfl⟩` from `hR'.1 γ hγ`. Rewrite using `[← pairing_shift μ Γ 𝓕 φ h hΓ (k₁ : G) 1 α⁻¹]`.

Simplify using `only [mul_one, ← mul_assoc, hJ _ k₁.2, hJ _ k₂.2]`. Establish `s1 : ∑ γ ∈ R, ∫ g in 𝓕, star (φ (g * γ)) * φ (g * 1) ∂μ = star a * ∫ g in 𝓕, star (φ g) * φ g ∂μ`. Rewrite using `[← integral_finset_sum _ (fun γ _ => pairing_integrable μ Γ 𝓕 φ h hc hΓ hi γ 1), ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [mul_one]`.

Rewrite using `[← Finset.sum_mul, ← star_sum, ha, star_mul', mul_assoc]`. Establish `s2 : ∑ γ ∈ R', ∫ g in 𝓕, star (φ (g * 1)) * φ (g * γ) ∂μ = b * ∫ g in 𝓕, star (φ g) * φ g ∂μ`. Rewrite using `[← integral_finset_sum _ (fun γ _ => pairing_integrable μ Γ 𝓕 φ h hc hΓ hi 1 γ), ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [mul_one]`.

Rewrite using `[← Finset.mul_sum, hb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `s1` using `[Finset.sum_congr rfl e1, Finset.sum_const, hcard]`. Rewrite `s2` using `[Finset.sum_congr rfl e2, Finset.sum_const, s1]`. Conclude with `mul_right_cancel₀ hne s2`.
-/
theorem eigenvalue_inv_eq_star : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ J : Subgroup G) [Countable Γ] (𝓕 : Set G) (φ : G → ℂ) (α : G) (R R' : Finset G) (a b : ℂ), IsFundamentalDomain Γ 𝓕 μ → Continuous φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → (∀ k ∈ J, ∀ g, φ (g * k) = φ g) → IntegrableOn (fun g => star (φ g) * φ g) 𝓕 μ → ∫ g in 𝓕, star (φ g) * φ g ∂μ ≠ 0 → Bridge.IsDC J α R → Bridge.IsDC J α⁻¹ R' → R.card = R'.card → (∀ g, ∑ γ ∈ R, φ (g * γ) = a * φ g) → (∀ g, ∑ γ ∈ R', φ (g * γ) = b * φ g) → star a = b := by
  intro G _ _ _ _ _ _ μ _ _ Γ J _ 𝓕 φ α R R' a b h hc hΓ hJ hi hne hR hR' hcard ha hb
  have e1 : ∀ γ ∈ R, ∫ g in 𝓕, star (φ (g * γ)) * φ (g * 1) ∂μ
      = ∫ g in 𝓕, star (φ (g * 1)) * φ (g * α⁻¹) ∂μ := by
    intro γ hγ
    obtain ⟨k₁, k₂, rfl⟩ := hR.1 γ hγ
    rw [← pairing_shift μ Γ 𝓕 φ h hΓ α 1 α⁻¹,
      ← pairing_shift μ Γ 𝓕 φ h hΓ (k₁ : G) (α * 1) (α * α⁻¹)]
    simp only [mul_one, mul_inv_cancel, ← mul_assoc, hJ _ k₁.2, hJ _ k₂.2]
  have e2 : ∀ γ ∈ R', ∫ g in 𝓕, star (φ (g * 1)) * φ (g * γ) ∂μ
      = ∫ g in 𝓕, star (φ (g * 1)) * φ (g * α⁻¹) ∂μ := by
    intro γ hγ
    obtain ⟨k₁, k₂, rfl⟩ := hR'.1 γ hγ
    rw [← pairing_shift μ Γ 𝓕 φ h hΓ (k₁ : G) 1 α⁻¹]
    simp only [mul_one, ← mul_assoc, hJ _ k₁.2, hJ _ k₂.2]
  have s1 : ∑ γ ∈ R, ∫ g in 𝓕, star (φ (g * γ)) * φ (g * 1) ∂μ
      = star a * ∫ g in 𝓕, star (φ g) * φ g ∂μ := by
    rw [← integral_finset_sum _ (fun γ _ => pairing_integrable μ Γ 𝓕 φ h hc hΓ hi γ 1),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [mul_one]
    rw [← Finset.sum_mul, ← star_sum, ha, star_mul', mul_assoc]
  have s2 : ∑ γ ∈ R', ∫ g in 𝓕, star (φ (g * 1)) * φ (g * γ) ∂μ
      = b * ∫ g in 𝓕, star (φ g) * φ g ∂μ := by
    rw [← integral_finset_sum _ (fun γ _ => pairing_integrable μ Γ 𝓕 φ h hc hΓ hi 1 γ),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [mul_one]
    rw [← Finset.mul_sum, hb]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_const, hcard] at s1
  rw [Finset.sum_congr rfl e2, Finset.sum_const, s1] at s2
  exact mul_right_cancel₀ hne s2

end GlobalTheory.DoubleCosetAdjoint
