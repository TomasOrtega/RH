import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.RelDiffTop

open NumberField Module

noncomputable section

namespace PIW.CMDiscSq

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_star_ne {E : Type} [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ x : E, star x ≠ x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P hP
  refine ⟨algebraMap (𝓞 E) E θ, ?_⟩
  rw [← ht]
  intro h
  apply hθ
  have : t = θ := RingOfIntegers.coe_injective h
  rw [this, sub_self]
  exact P.zero_mem

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Supply the required witnesses or components. It suffices to derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finrank_two_of {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (x : E) (hx : star x ≠ x) :
    finrank F E = 2 := by
  have hmem : ∀ a : E, star a = a → ∃ c : F, algebraMap F E c = a := by
    intro a ha
    have : a ∈ Set.range (algebraMap F E) := by rw [hR]; exact ha
    exact this
  have hfix : ∀ c : F, star (algebraMap F E c) = algebraMap F E c := by
    intro c
    have : algebraMap F E c ∈ Set.range (algebraMap F E) := ⟨c, rfl⟩
    rw [hR] at this
    exact this
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let v : Fin 2 → E := ![1, x]
  have hli : LinearIndependent F v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [map_zero, zero_mul, add_zero] at hst
      exact ⟨(FaithfulSMul.algebraMap_injective F E) (by rw [hst, map_zero]), rfl⟩
    · exfalso
      have htE : algebraMap F E t ≠ 0 := by
        intro h0
        apply ht
        exact (FaithfulSMul.algebraMap_injective F E) (by rw [h0, map_zero])
      have hxe : x = algebraMap F E (-s / t) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hst
      apply hx
      rw [hxe, hfix]
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro y _
    have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
      rw [star_div₀, star_sub, star_sub, star_star, star_star]
      rw [← neg_sub y, ← neg_sub x, neg_div_neg_eq]
    obtain ⟨b, hb'⟩ := hmem _ hb
    have ha : star (y - algebraMap F E b * x) = y - algebraMap F E b * x := by
      rw [star_sub, star_mul', hfix, hb']
      field_simp
      ring
    obtain ⟨a, ha'⟩ := hmem _ ha
    have hy : y = a • v 0 + b • v 1 := by
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one]
      rw [ha']
      ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have bas := Basis.mk hli hsp
  rw [finrank_eq_card_basis bas, Fintype.card_fin]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem relDegTwo : RelDegTwo := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨x, hx⟩ := exists_star_ne hFE.1
  exact finrank_two_of hFE.2 x hx

end PIW.CMDiscSq
