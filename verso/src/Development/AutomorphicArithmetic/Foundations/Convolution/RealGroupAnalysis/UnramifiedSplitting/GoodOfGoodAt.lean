import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiLoc

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem psi_sg {K : Type} [Field K] [NumberField K] (v : P K) (x : Kv v) :
    ψ (sg v x) = UpperTheory.V.Af.Smo.psiL v x := rfl

/- English proof (translation)
Establish `h1` using `HeightOneSpectrum.Support.finite (𝓞 K) a`. Establish `h2` using `HeightOneSpectrum.Support.finite (𝓞 K) a⁻¹`. Use `filter_upwards [h1.compl_mem_cofinite, h2.compl_mem_cofinite] with v hv1 hv2`. Establish `e : Valued.v (algebraMap K (Kv v) a) = v.valuation K a` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a`. Rewrite using `[e]`.

Establish `n1 : v.valuation K a ≤ 1` using `not_lt.1 hv1`. Establish `n2 : (v.valuation K a)⁻¹ ≤ 1`. Establish `: v.valuation K a⁻¹ ≤ 1` using `not_lt.1 hv2`. Rewrite `this` using `[map_inv₀]`. Then use the resulting hypothesis. Establish `h0 : v.valuation K a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha`.

Conclude with `le_antisymm n1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 n2)`.
-/
private theorem val_ae {K : Type} [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    ∀ᶠ v : P K in cofinite, Valued.v (algebraMap K (Kv v) a) = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 K) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 K) a⁻¹
  filter_upwards [h1.compl_mem_cofinite, h2.compl_mem_cofinite] with v hv1 hv2
  have e : Valued.v (algebraMap K (Kv v) a) = v.valuation K a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  have n1 : v.valuation K a ≤ 1 := not_lt.1 hv1
  have n2 : (v.valuation K a)⁻¹ ≤ 1 := by
    have : v.valuation K a⁻¹ ≤ 1 := not_lt.1 hv2
    rwa [map_inv₀] at this
  have h0 : v.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  exact le_antisymm n1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 n2)

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [psi_sg]`. Conclude with `AddChar.map_add_eq_mul _ x y`. Conclude with `(psi_sg v x).trans (h1 x hx)`.

Assume the negation of the conclusion as `hni`. Establish `hlt : 1 < Valued.v x` using `not_le.1 hni`. Take `⟨ϖ, hϖ⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))`. Take `⟨y, hy, hy1⟩` from `h2 ϖ hϖ`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hlt` using `[map_zero]`. Conclude with `not_lt_zero' hlt`. Establish `hv0 : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx0`. Establish `hxe : WithZero.exp (1 : ℤ) ≤ Valued.v x`.

Rewrite using `[← WithZero.exp_log hv0]`. Rewrite `hlt` using `[← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Establish `hyv : Valued.v (ϖ * y) ≤ 1` using `hy`.

Rewrite `hyv` using `[map_mul, hϖ]`. Establish `hye : Valued.v y ≤ WithZero.exp (1 : ℤ)`. Use `mul_le_mul_right hyv (WithZero.exp (1 : ℤ))` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← WithZero.exp_add, show (1 : ℤ) + -1 = 0 by norm_num, WithZero.exp_zero, one_mul, mul_one]`. Then use the resulting hypothesis. Establish `hc : IsInt (y * x⁻¹)`.

Express the relevant statement in the definitionally equal form `Valued.v (y * x⁻¹) ≤ 1`. Rewrite using `[map_mul, map_inv₀]`. Conclude with `mul_inv_le_one_of_le₀ (hye.trans hxe) zero_le'`. Use `hx _ hc` as an intermediate fact. Rewrite `this` using `[mul_assoc, inv_mul_cancel₀ hx0, mul_one]`.

Conclude with `hy1 ((psi_sg v y).symm.trans this)`.
-/
private theorem good_of_goodAt {K : Type} [Field K] [NumberField K] (v : P K)
    (h : UpperTheory.V.Af.Smo.GoodAt v (UpperTheory.V.Af.Smo.psiL v)) :
    Good fun x : Kv v => ψ (sg v x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [psi_sg]
    exact AddChar.map_add_eq_mul _ x y
  · exact (psi_sg v x).trans (h1 x hx)
  · by_contra hni
    have hlt : 1 < Valued.v x := not_le.1 hni
    obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
    obtain ⟨y, hy, hy1⟩ := h2 ϖ hϖ
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hlt
      exact not_lt_zero' hlt
    have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hxe : WithZero.exp (1 : ℤ) ≤ Valued.v x := by
      rw [← WithZero.exp_log hv0]
      rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      omega
    have hyv : Valued.v (ϖ * y) ≤ 1 := hy
    rw [map_mul, hϖ] at hyv
    have hye : Valued.v y ≤ WithZero.exp (1 : ℤ) := by
      have := mul_le_mul_right hyv (WithZero.exp (1 : ℤ))
      rwa [← mul_assoc, ← WithZero.exp_add, show (1 : ℤ) + -1 = 0 by norm_num, WithZero.exp_zero,
        one_mul, mul_one] at this
    have hc : IsInt (y * x⁻¹) := by
      change Valued.v (y * x⁻¹) ≤ 1
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ (hye.trans hxe) zero_le'
    have := hx _ hc
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    exact hy1 ((psi_sg v y).symm.trans this)

/- English proof (translation)
Introduce `K _ _ δ hδ`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Use `filter_upwards [(UpperTheory.V.Af.Smo.psiLoc K).2, val_ae (2 : K) h2, val_ae δ hδ] with v hg ht hd`. Rewrite `ht` using `[map_ofNat]`. Conclude with `⟨good_of_goodAt v hg, ht, hd⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.gdAe :
    ∀ (K : Type) [Field K] [NumberField K] (δ : K), δ ≠ 0 → ∀ᶠ v in cofinite, Gd δ v := by
  intro K _ _ δ hδ
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  filter_upwards [(UpperTheory.V.Af.Smo.psiLoc K).2, val_ae (2 : K) h2, val_ae δ hδ] with v hg ht hd
  rw [map_ofNat] at ht
  exact ⟨good_of_goodAt v hg, ht, hd⟩
