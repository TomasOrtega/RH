import Formalism.PeriodIntegrals.GoodTwo
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt

noncomputable section

namespace PI.GoodTwo.HalfW

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

/- English proof (translation)
Introduce `K _ _ _ W g2 g3 hΔ hg hrel`. Establish `hc` using `W.c_relation`. Establish `key : 27 * W.c₄ ^ 3 * g3 ^ 2 = g2 ^ 3 * W.c₆ ^ 2`. Take the linear combination `(-1 : K) * hrel - g2 ^ 3 * hc`. Establish `hD : W.c₄ ^ 3 - W.c₆ ^ 2 ≠ 0`.

Rewrite using `[← hc]; exact mul_ne_zero (by norm_num) hΔ`. Distinguish the cases in `h2 : g2 = 0`. Establish `h3 : g3 ≠ 0`. Introduce and unpack `rfl`. Apply `hg` to reduce the goal to its premises.

Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc4 : W.c₄ = 0`. Establish `h0 : 27 * W.c₄ ^ 3 * g3 ^ 2 = 0` using `by rw [key, h2]; ring`. Simplify `h0` using `[h3]`.

Establish `hc6 : W.c₆ ≠ 0`. Introduce `h`. Apply `hD` to reduce the goal to its premises. Rewrite using `[hc4, h]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hw : W.c₆ / 216 / g3 ≠ 0` using `div_ne_zero (div_ne_zero hc6 (by norm_num)) h3`. Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (W.c₆ / 216 / g3) (by norm_num : 0 < 6)`. Use `⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc4, h2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hu]`. Clear the denominators using the available nonvanishing facts. Distinguish the cases in `h3 : g3 = 0`. Establish `hc6 : W.c₆ = 0`. Establish `h0 : g2 ^ 3 * W.c₆ ^ 2 = 0` using `by rw [← key, h3]; ring`.

Simplify `h0` using `[h2]`. Establish `hc4 : W.c₄ ≠ 0`. Introduce `h`. Apply `hD` to reduce the goal to its premises. Rewrite using `[hc6, h]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hw : W.c₄ / 12 / g2 ≠ 0` using `div_ne_zero (div_ne_zero hc4 (by norm_num)) h2`. Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (W.c₄ / 12 / g2) (by norm_num : 0 < 4)`. Use `⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hu]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hc6, h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc4 : W.c₄ ≠ 0`. Introduce `h`.

Establish `h0 : g2 ^ 3 * W.c₆ ^ 2 = 0` using `by rw [← key, h]; ring`. Establish `hc6 : W.c₆ = 0` using `by simpa [h2] using h0`. Apply `hD` to reduce the goal to its premises. Rewrite using `[hc6, h]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc6 : W.c₆ ≠ 0`. Introduce `h`. Establish `h0 : 27 * W.c₄ ^ 3 * g3 ^ 2 = 0` using `by rw [key, h]; ring`. Apply `hc4` to reduce the goal to its premises. Simplify `h0` using `[h3]`.

Establish `hA : W.c₄ / 12 ≠ 0` using `div_ne_zero hc4 (by norm_num)`. Establish `hB : W.c₆ / 216 ≠ 0` using `div_ne_zero hc6 (by norm_num)`. Establish `keyAB : (W.c₄ / 12) ^ 3 * g3 ^ 2 = g2 ^ 3 * (W.c₆ / 216) ^ 2`. Take the linear combination `(1 / 46656 : K) * key`. Establish `hw : W.c₆ / 216 * g2 / (W.c₄ / 12 * g3) ≠ 0` using `div_ne_zero (mul_ne_zero hB h2) (mul_ne_zero hA h3)`.

Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) (by norm_num : 0 < 2)`. Establish `hw2 : (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) ^ 2 * g2 = W.c₄ / 12`. Rewrite using `[div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 (mul_ne_zero hA h3))]`. Take the linear combination `(-1 : K) * keyAB`. Establish `hw3 : (W.c₆ / 216 * g2 / (W.c₄ / 12 * g3)) ^ 3 * g3 = W.c₆ / 216`.

Rewrite using `[div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 3 (mul_ne_zero hA h3))]`. Take the linear combination `(-(W.c₆ / 216 * g3)) * keyAB`. Use `⟨u, fun hu0 => hw (by rw [← hu, hu0]; ring), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show u ^ 4 = (u ^ 2) ^ 2 by ring, hu, hw2]`. Rewrite using `[show u ^ 6 = (u ^ 2) ^ 3 by ring, hu, hw3]`.
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
Establish `h2 : ‖(3 : ℚ_[2])‖ = 1` using `by first`. Consider the case `have e := Padic.eq_padicNorm (p := 2) (3 : ℚ)`. Establish `h3 : padicNorm 2 ((3 : ℕ) : ℚ) = 1` using `(padicNorm.nat_eq_one_iff 3).mpr (by norm_num)`. Move the coercions through the operations in `at e h3`. Rewrite using `[e, h3]`.

Evaluate the numerical expressions. Consider the case `have hle : ‖(3 : ℚ_[2])‖ ≤ 1 := by`. Use `Padic.norm_int_le_one (p := 2) 3` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `h2n : ‖(2 : ℚ_[2])‖ = 1 / 2`. Use `Padic.norm_p (p := 2)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Evaluate the numerical expressions.

Establish `hm : ‖(1 : ℚ_[2])‖ ≤ max ‖(3 : ℚ_[2])‖ ‖(2 : ℚ_[2])‖`. Use `IsUltrametricDist.norm_sub_le_max (3 : ℚ_[2]) 2` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Conclude with `this`. Rewrite `hm` using `[norm_one, h2n]`.

Establish `: 1 ≤ ‖(3 : ℚ_[2])‖`. Break down `le_max_iff.mp hm with h | h` into its components or cases. Conclude with `h`. Evaluate the numerical expressions using `at h`. Conclude with `le_antisymm hle this`.

Establish `h1 : ((algebraMap ℚ_[2] (PadicAlgCl 2) 3 : PadicAlgCl 2) : ℂ_[2]) = 3`. Rewrite using `[map_ofNat]`. Conclude with `map_ofNat UniformSpace.Completion.coeRingHom 3`. Rewrite using `[← h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h2]`.
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
Introduce `d L hsq hd hcm ι`. Establish `hd4 : d % 4 = 3` using `by omega`. Establish `hj : ‖ι (jInv L)‖ ≤ 1` using `ReciprocityTheory.ChartRestriction.L1.jInt d L hsq hd4 hcm 2 ι`. Take `⟨a, ha, hc4, hΔ⟩` from `Formalism.ELL.deuring_model ℂ_[2] norm_three (ι (jInv L)) hj`. Establish `hD : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0` using `Formalism.L2.Th1.F.discNeZero L`.

Establish `hΔ0 : (Formalism.ELL.deuring a).Δ ≠ 0`. Introduce `h`. Rewrite `hΔ` using `[h, norm_zero]`. Conclude with `zero_ne_one hΔ`. Establish `hDι : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 ≠ 0`.

Introduce `h`. Apply `hD` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Simplify `h` using `[map_sub, map_mul, map_pow, map_ofNat]`. Establish `hjD : ι (jInv L) * (ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2) = 1728 * ι L.g₂ ^ 3`.

Establish `e : jInv L * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1728 * L.g₂ ^ 3`. Unfold `jInv`. Clear the denominators using the available nonvanishing facts. Establish `e'` using `congrArg ι e`. Simplify `e'` using `[map_mul, map_sub, map_pow, map_ofNat]`.

Establish `hrel : (Formalism.ELL.deuring a).c₄ ^ 3 * (ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2) = 1728 * ι L.g₂ ^ 3 * (Formalism.ELL.deuring a).Δ`. Rewrite using `[hc4]`. Take the linear combination `(Formalism.ELL.deuring a).Δ * hjD`. Take `⟨u, hu, h4, h6⟩` from `twist ℂ_[2] (Formalism.ELL.deuring a) (ι L.g₂) (ι L.g₃) hΔ0 hDι hrel`. Establish `hu' : ι.symm u ≠ 0` using `by simpa using hu`.

Establish `hc : (ι.symm u)⁻¹ ≠ 0` using `inv_ne_zero hu'`. Establish `hh` using `Formalism.L2.Th1.F.homogeneity L (ι.symm u)⁻¹ hc`. Use `⟨(ι.symm u)⁻¹, hc, Formalism.ELL.deuring a, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h4, hh.2.2.2.2.2.2.2.2.2.1]`. Simplify using the standard rewrite rules.

Rewrite using `[h6, hh.2.2.2.2.2.2.2.2.2.2]`. Simplify using the standard rewrite rules. Use `⟨by simpa [Formalism.ELL.deuring] using ha, by simp [Formalism.ELL.deuring], by simp [Formalism.ELL.deuring], by simp [Formalism.ELL.deuring], by simp [Formalism.ELL.deuring], hΔ⟩` and prove the remaining obligations.
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
