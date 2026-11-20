import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in
/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma natAbs_discr_pow_finrank_le_natAbs_discr (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    (discr K).natAbs ^ Module.finrank K L ≤ (discr L).natAbs := by
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  refine Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) ?_
  rw [h]
  exact Dvd.intro_left _ rfl

set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Establish an intermediate fact. Check the signs of the components of the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    Real.log (Module.finrank ℚ K) ≤ Real.log (Module.finrank ℚ L) ∧
      Real.log |((NumberField.discr K : ℤ) : ℝ)| / Module.finrank ℚ K ≤
        Real.log |((NumberField.discr L : ℤ) : ℝ)| / Module.finrank ℚ L := by
  have hmul := Module.finrank_mul_finrank ℚ K L
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hm : 0 < Module.finrank K L := Module.finrank_pos
  have hnR : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast hn
  have hmR : (0 : ℝ) < Module.finrank K L := by exact_mod_cast hm
  have hNR : ((Module.finrank ℚ L : ℕ) : ℝ) = Module.finrank ℚ K * Module.finrank K L := by
    rw [← hmul]; push_cast; ring
  constructor
  · apply Real.log_le_log hnR
    rw [hNR]
    have : (1 : ℝ) ≤ Module.finrank K L := by exact_mod_cast hm
    nlinarith
  · have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := by
      have := discr_ne_zero K
      positivity
    have hle : |((discr K : ℤ) : ℝ)| ^ Module.finrank K L ≤ |((discr L : ℤ) : ℝ)| := by
      have h := natAbs_discr_pow_finrank_le_natAbs_discr K L
      have h' : (((discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) ≤ ((discr L).natAbs : ℝ) := by
        exact_mod_cast h
      simpa [Nat.cast_natAbs, Int.cast_abs] using h'
    have hlog : (Module.finrank K L : ℝ) * Real.log |((discr K : ℤ) : ℝ)| ≤
        Real.log |((discr L : ℤ) : ℝ)| := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hK _) hle
    rw [hNR, div_le_div_iff₀ hnR (mul_pos hnR hmR)]
    nlinarith

set_option autoImplicit false in
open NumberField IsDedekindDomain in
open scoped IntermediateField nonZeroDivisors in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Equip the data with the indicated structure.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem _root_.GlobalTheory.FieldSize.sz_mono_and_of_le :
    (∀ (F : IntermediateField ℚ ℂ) (a b a' b' : ℝ), _root_.GlobalTheory.FieldSize.Sz F a b →
        a ≤ a' → b ≤ b' → _root_.GlobalTheory.FieldSize.Sz F a' b') ∧
      ∀ (F F' : IntermediateField ℚ ℂ) (a b : ℝ), F ≤ F' →
        _root_.GlobalTheory.FieldSize.Sz F' a b → _root_.GlobalTheory.FieldSize.Sz F a b := by
  constructor
  · rintro F a b a' b' ⟨hF, h1, h2⟩ ha hb
    exact ⟨hF, h1.trans ha, h2.trans hb⟩
  · rintro F F' a b hFF' ⟨hF', h1, h2⟩
    haveI : FiniteDimensional ℚ F' := hF'
    haveI hF : FiniteDimensional ℚ F :=
      FiniteDimensional.of_injective (IntermediateField.inclusion hFF').toLinearMap
        (IntermediateField.inclusion hFF').injective
    haveI : NumberField F := ⟨⟩
    haveI : NumberField F' := ⟨⟩
    letI : Algebra F F' := (IntermediateField.inclusion hFF').toRingHom.toAlgebra
    obtain ⟨g1, g2⟩ := _root_.GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower F F'
    exact ⟨hF, g1.trans h1, g2.trans h2⟩

end GlobalTheory.FieldSize
