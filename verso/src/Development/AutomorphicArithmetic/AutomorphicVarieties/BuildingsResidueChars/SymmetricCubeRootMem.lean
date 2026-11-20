import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Mathlib.FieldTheory.Galois.Infinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
