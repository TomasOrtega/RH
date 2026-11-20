import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Mathlib.FieldTheory.Galois.Infinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Introduce `l _ E a b c d x ha hb hc hd hb1 had hx hrel`. Establish `hn : ∀ (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l), ‖σ y‖ = ‖y‖`. Introduce `σ y`. Use `show spectralNorm ℚ_[l] (PadicAlgCl l) (σ y) = spectralNorm ℚ_[l] (PadicAlgCl l) y`. Unfold `spectralNorm`.

Rewrite using `[minpoly.algEquiv_eq]`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`. Rewrite `hσ` using `[IntermediateField.mem_fixingSubgroup_iff]`. Establish `hrel' : c + d * σ x = (a + b * σ x) * σ x`.

Establish `h` using `congrArg σ hrel`. Simplify `h` using `only [map_add, map_mul, hσ a ha, hσ b hb, hσ c hc, hσ d hd]`. Assume the negation of the conclusion as `hne`. Establish `hyn : ‖σ x‖ ≤ 1` using `by rw [hn]; exact hx`. Establish `key : (σ x - x) * (b * (x + σ x) - (d - a)) = 0` using `by linear_combination hrel - hrel'`.

Establish `hsub : σ x - x ≠ 0` using `sub_ne_zero.mpr hne`. Establish `heq : b * (x + σ x) = d - a` using `sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hsub)`. Establish `hlt : ‖a - d‖ < 1`. Rewrite using `[← norm_neg, neg_sub, ← heq, norm_mul]`. Establish `hxy : ‖x + σ x‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max x (σ x)).trans (max_le hx hyn)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt` using `[had]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem UpperTheory.symmetric_cube_root_mem :
    UpperTheory.V.Sd.S3.RootMem := by
  intro l _ E a b c d x ha hb hc hd hb1 had hx hrel
  have hn : ∀ (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l), ‖σ y‖ = ‖y‖ := by
    intro σ y
    show spectralNorm ℚ_[l] (PadicAlgCl l) (σ y) = spectralNorm ℚ_[l] (PadicAlgCl l) y
    unfold spectralNorm
    rw [minpoly.algEquiv_eq]
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hrel' : c + d * σ x = (a + b * σ x) * σ x := by
    have h := congrArg σ hrel
    simpa only [map_add, map_mul, hσ a ha, hσ b hb, hσ c hc, hσ d hd] using h
  by_contra hne
  have hyn : ‖σ x‖ ≤ 1 := by rw [hn]; exact hx
  have key : (σ x - x) * (b * (x + σ x) - (d - a)) = 0 := by linear_combination hrel - hrel'
  have hsub : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  have heq : b * (x + σ x) = d - a := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hsub)
  have hlt : ‖a - d‖ < 1 := by
    rw [← norm_neg, neg_sub, ← heq, norm_mul]
    have hxy : ‖x + σ x‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x (σ x)).trans (max_le hx hyn)
    calc ‖b‖ * ‖x + σ x‖ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hb1
  rw [had] at hlt
  exact lt_irrefl _ hlt
