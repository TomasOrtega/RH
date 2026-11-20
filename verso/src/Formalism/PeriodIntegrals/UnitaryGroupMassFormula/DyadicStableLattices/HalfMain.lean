import Formalism.PeriodIntegrals.GoodTwo
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt

noncomputable section

namespace PI.GoodTwo.HalfW

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem twist : Twist := by
  intro K _ _ _ W g2 g3 hΔ hg hrel
  have hc := W.c_relation
  have key : 27 * W.c₄ ^ 3 * g3 ^ 2 = g2 ^ 3 * W.c₆ ^ 2 := by
    linear_combination (-1 : K) * hrel - g2 ^ 3 * hc
  have hD : W.c₄ ^ 3 - W.c₆ ^ 2 ≠ 0 := by
    rw [← hc]; exact mul_ne_zero (by norm_num) hΔ
  by_cases h2 : g2 = 0
  · have h3 : g3 ≠ 0 := by
      rintro rfl; apply hg; rw [h2]; ring
    have hc4 : W.c₄ = 0 := by
      have h0 : 27 * W.c₄ ^ 3 * g3 ^ 2 = 0 := by rw [key, h2]; ring
      simpa [h3] using h0
    have hc6 : W.c₆ ≠ 0 := by
      intro h; apply hD; rw [hc4, h]; ring
    have hw : W.c₆ / 216 / g3 ≠ 0 := div_ne_zero (div_ne_zero hc6 (by norm_num)) h3
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (W.c₆ / 216 / g3) (by norm_num : 0 < 6)
    refine ⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩
    · rw [hc4, h2]; ring
    · rw [hu]; field_simp
  by_cases h3 : g3 = 0
  · have hc6 : W.c₆ = 0 := by
      have h0 : g2 ^ 3 * W.c₆ ^ 2 = 0 := by rw [← key, h3]; ring
      simpa [h2] using h0
    have hc4 : W.c₄ ≠ 0 := by
      intro h; apply hD; rw [hc6, h]; ring
    have hw : W.c₄ / 12 / g2 ≠ 0 := div_ne_zero (div_ne_zero hc4 (by norm_num)) h2
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (W.c₄ / 12 / g2) (by norm_num : 0 < 4)
    refine ⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩
    · rw [hu]; field_simp
    · rw [hc6, h3]; ring
  have hc4 : W.c₄ ≠ 0 := by
    intro h
    have h0 : g2 ^ 3 * W.c₆ ^ 2 = 0 := by rw [← key, h]; ring
    have hc6 : W.c₆ = 0 := by simpa [h2] using h0
    apply hD; rw [hc6, h]; ring
  have hc6 : W.c₆ ≠ 0 := by
    intro h
    have h0 : 27 * W.c₄ ^ 3 * g3 ^ 2 = 0 := by rw [key, h]; ring
    apply hc4; simpa [h3] using h0
  have hA : W.c₄ / 12 ≠ 0 := div_ne_zero hc4 (by norm_num)
  have hB : W.c₆ / 216 ≠ 0 := div_ne_zero hc6 (by norm_num)
  have keyAB : (W.c₄ / 12) ^ 3 * g3 ^ 2 = g2 ^ 3 * (W.c₆ / 216) ^ 2 := by
    linear_combination (1 / 46656 : K) * key
  have hw : W.c₆ / 216 * g2 / (W.c₄ / 12 * g3) ≠ 0 :=
    div_ne_zero (mul_ne_zero hB h2) (mul_ne_zero hA h3)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) (by norm_num : 0 < 2)
  have hw2 : (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) ^ 2 * g2 = W.c₄ / 12 := by
    rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 (mul_ne_zero hA h3))]
    linear_combination (-1 : K) * keyAB
  have hw3 : (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) ^ 3 * g3 = W.c₆ / 216 := by
    rw [div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 3 (mul_ne_zero hA h3))]
    linear_combination (-(W.c₆ / 216 * g3)) * keyAB
  refine ⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩
  · rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu, hw2]
  · rw [show u ^ 6 = (u ^ 2) ^ 3 by ring, hu, hw3]

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Treat this case separately. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact.

Establish an intermediate fact. Evaluate the numerical expressions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Evaluate the numerical expressions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_three : ‖(3 : ℂ_[2])‖ = 1 := by
  have h2 : ‖(3 : ℚ_[2])‖ = 1 := by
    first
      | have e := Padic.eq_padicNorm (p := 2) (3 : ℚ)
        have h3 : padicNorm 2 ((3 : ℕ) : ℚ) = 1 := (padicNorm.nat_eq_one_iff 3).mpr (by norm_num)
        push_cast at e h3
        rw [e, h3]; norm_num
      | have hle : ‖(3 : ℚ_[2])‖ ≤ 1 := by
          have := Padic.norm_int_le_one (p := 2) 3
          push_cast at this; exact this
        have h2n : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
          have := Padic.norm_p (p := 2)
          push_cast at this; rw [this]; norm_num
        have hm : ‖(1 : ℚ_[2])‖ ≤ max ‖(3 : ℚ_[2])‖ ‖(2 : ℚ_[2])‖ := by
          have := IsUltrametricDist.norm_sub_le_max (3 : ℚ_[2]) 2
          norm_num at this ⊢; exact this
        rw [norm_one, h2n] at hm
        have : 1 ≤ ‖(3 : ℚ_[2])‖ := by
          rcases le_max_iff.mp hm with h | h
          · exact h
          · norm_num at h
        exact le_antisymm hle this
  have h1 : ((algebraMap ℚ_[2] (PadicAlgCl 2) 3 : PadicAlgCl 2) : ℂ_[2]) = 3 := by
    rw [map_ofNat]
    exact map_ofNat UniformSpace.Completion.coeRingHom 3
  rw [← h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem half : Half := by
  intro d L hsq hd hcm ι
  have hd4 : d % 4 = 3 := by omega
  have hj : ‖ι (jInv L)‖ ≤ 1 := ReciprocityTheory.ChartRestriction.L1.jInt d L hsq hd4 hcm 2 ι
  obtain ⟨a, ha, hc4, hΔ⟩ := Formalism.ELL.deuring_model ℂ_[2] norm_three (ι (jInv L)) hj
  have hD : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := Formalism.L2.Th1.F.discNeZero L
  have hΔ0 : (Formalism.ELL.deuring a).Δ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hΔ
    exact zero_ne_one hΔ
  have hDι : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 ≠ 0 := by
    intro h
    apply hD
    apply ι.injective
    simpa [map_sub, map_mul, map_pow, map_ofNat] using h
  have hjD : ι (jInv L) * (ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2) = 1728 * ι L.g₂ ^ 3 := by
    have e : jInv L * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1728 * L.g₂ ^ 3 := by
      unfold jInv
      field_simp
    have e' := congrArg ι e
    simpa [map_mul, map_sub, map_pow, map_ofNat] using e'
  have hrel : (Formalism.ELL.deuring a).c₄ ^ 3 * (ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2) =
      1728 * ι L.g₂ ^ 3 * (Formalism.ELL.deuring a).Δ := by
    rw [hc4]
    linear_combination (Formalism.ELL.deuring a).Δ * hjD
  obtain ⟨u, hu, h4, h6⟩ := twist ℂ_[2] (Formalism.ELL.deuring a) (ι L.g₂) (ι L.g₃) hΔ0 hDι hrel
  have hu' : ι.symm u ≠ 0 := by simpa using hu
  have hc : (ι.symm u)⁻¹ ≠ 0 := inv_ne_zero hu'
  have hh := Formalism.L2.Th1.F.homogeneity L (ι.symm u)⁻¹ hc
  refine ⟨(ι.symm u)⁻¹, hc, Formalism.ELL.deuring a, ⟨?_, ?_⟩, ?_⟩
  · rw [h4, hh.2.2.2.2.2.2.2.2.2.1]
    simp
  · rw [h6, hh.2.2.2.2.2.2.2.2.2.2]
    simp
  · refine ⟨by simpa [Formalism.ELL.deuring] using ha, by simp [Formalism.ELL.deuring], by simp [Formalism.ELL.deuring],
      by simp [Formalism.ELL.deuring], by simp [Formalism.ELL.deuring], hΔ⟩

end PI.GoodTwo.HalfW
