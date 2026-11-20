import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensDiv
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensPair
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSpace
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDual

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `h : (starRingEnd ℂ) (χ a) = χ⁻¹ a` using `MulChar.star_apply' χ a`. Rewrite using `[h, ← MulChar.mul_apply, mul_inv_cancel]`.
-/
lemma char_mul_conj_self {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ a) = (1 : DirichletCharacter ℂ M) a := by
  have h : (starRingEnd ℂ) (χ a) = χ⁻¹ a := MulChar.star_apply' χ a
  rw [h, ← MulChar.mul_apply, mul_inv_cancel]

/- English proof (translation)
Establish `h : (starRingEnd ℂ) (χ' a) = χ'⁻¹ a` using `MulChar.star_apply' χ' a`. Rewrite using `[h, ← MulChar.mul_apply]`.
-/
lemma char_mul_conj {M : ℕ} [NeZero M] (χ χ' : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ' a) = (χ * χ'⁻¹) a := by
  have h : (starRingEnd ℂ) (χ' a) = χ'⁻¹ a := MulChar.star_apply' χ' a
  rw [h, ← MulChar.mul_apply]

/- English proof (translation)
Take `⟨hl, hu, hi⟩` from `hp`. Take `⟨hl', hu', hi'⟩` from `hp'`. Establish `hU0 : (0 : ℝ) < U` using `by exact_mod_cast hU`. Establish `hU1 : (1 : ℝ) ≤ U` using `by exact_mod_cast hU`. Establish `hM0 : (0 : ℝ) ≤ (M : ℝ)` using `by positivity`.

Use `set w : ℂ := (p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ)) with hw`. Establish `hwre : w.re = p.2.re + p'.2.re - 2 * σ`. Simplify using `only [hw, add_re, sub_re, ofReal_re, conj_re]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwim : w.im = p.2.im - p'.2.im`.

Simplify using `only [hw, add_im, sub_im, ofReal_im, conj_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw0 : 0 ≤ w.re` using `by rw [hwre]; linarith`. Establish `hw1 : w.re ≤ 1` using `by rw [hwre]; linarith`. Establish `hwn : ‖w‖ ≤ 1 + 2 * T`.

Use `(Complex.norm_le_abs_re_add_abs_im w).trans ?_` and prove the remaining obligations. Rewrite using `[abs_of_nonneg hw0, hwim]`. Establish `: |p.2.im - p'.2.im| ≤ |p.2.im| + |p'.2.im|` using `abs_sub _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : 4 * ((M : ℝ) + 1) * (1 + ‖w‖) ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T)`.

Establish `: 1 + ‖w‖ ≤ 2 + 2 * T` using `by linarith`. Use `gcongr`. Establish `hB0 : 0 ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T)` using `by positivity`. Establish `hq0 : 0 ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|)` using `by positivity`. Distinguish the cases in `h1 : p' = p`.

Rewrite using `[if_pos h1, if_pos (by rw [h1])]`. Establish `hdiag : ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) * (n : ℂ) ^ (-w)‖ ≤ U`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ n ∈ Ioc U (2 * U), ‖p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) * (n : ℂ) ^ (-w)‖ ≤ 1`. Introduce `n hn`.

Establish `hn1 : 1 ≤ n` using `by have := (mem_Ioc.1 hn).1; omega`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj]`. Establish `a1 : ‖p.1 (n : ZMod M)‖ ≤ 1` using `DirichletCharacter.norm_le_one _ _`. Establish `a2 : ‖p'.1 (n : ZMod M)‖ ≤ 1` using `DirichletCharacter.norm_le_one _ _`. Establish `a3 : ‖(n : ℂ) ^ (-w)‖ ≤ 1` using `norm_natCast_cpow_neg_le_one hn1 hw0`.

Combine the equalities or inequalities in the displayed calculation. Use `(sum_le_sum this).trans ?_` and prove the remaining obligations. Rewrite using `[sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]`. Conclude with `(by omega : 2 * U - U ≤ U)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg h1]`. Distinguish the cases in `h2 : p'.1 = p.1`. Rewrite using `[if_pos h2]`. Establish `hgap : 1 ≤ |p.2.im - p'.2.im|` using `hsp (fun h => h1 h.symm) h2.symm`. Establish `him : w.im ≠ 0`.

Rewrite using `[hwim]`. Introduce `h0`. Rewrite `hgap` using `[h0, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsame` using `pair_same_bound M w hw0 hw1 him U hU`.

Establish `heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) * (n : ℂ) ^ (-w) = ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w)`. Use `sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[h2, char_mul_conj_self]`. Rewrite using `[heq]`. Establish `hUp : (U : ℝ) ^ (1 - w.re) ≤ U`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdiv : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|)`. Rewrite using `[hwim, mul_one_div]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_neg h2]`. Establish `hne : p.1 * p'.1⁻¹ ≠ 1`. Introduce `h`. Conclude with `h2 (mul_inv_eq_one.1 h).symm`. Establish `hcross` using `pair_cross_bound M (p.1 * p'.1⁻¹) hne w hw0 U hU`.

Establish `heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) * (n : ℂ) ^ (-w) = ∑ n ∈ Ioc U (2 * U), (p.1 * p'.1⁻¹) (n : ZMod M) * (n : ℂ) ^ (-w)`. Use `sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[char_mul_conj]`. Rewrite using `[heq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma offdiag_term {M : ℕ} [NeZero M] (σ T : ℝ) (U : ℕ) (hU : 1 ≤ U) (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    (p p' : DirichletCharacter ℂ M × ℂ)
    (hp : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) (hp' : σ ≤ p'.2.re ∧ p'.2.re ≤ 1 ∧ |p'.2.im| ≤ T)
    (hsp : p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) :
    ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (if p' = p then (U : ℝ) else 0) +
        (if p'.1 = p.1 then 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) else 0) +
        4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
  obtain ⟨hl, hu, hi⟩ := hp
  obtain ⟨hl', hu', hi'⟩ := hp'
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  set w : ℂ := (p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ)) with hw
  have hwre : w.re = p.2.re + p'.2.re - 2 * σ := by
    simp only [hw, add_re, sub_re, ofReal_re, conj_re]; ring
  have hwim : w.im = p.2.im - p'.2.im := by
    simp only [hw, add_im, sub_im, ofReal_im, conj_im]; ring
  have hw0 : 0 ≤ w.re := by rw [hwre]; linarith
  have hw1 : w.re ≤ 1 := by rw [hwre]; linarith
  have hwn : ‖w‖ ≤ 1 + 2 * T := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_nonneg hw0, hwim]
    have : |p.2.im - p'.2.im| ≤ |p.2.im| + |p'.2.im| := abs_sub _ _
    linarith
  have hB : 4 * ((M : ℝ) + 1) * (1 + ‖w‖) ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
    have : 1 + ‖w‖ ≤ 2 + 2 * T := by linarith
    gcongr
  have hB0 : 0 ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hq0 : 0 ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by positivity
  by_cases h1 : p' = p
  · rw [if_pos h1, if_pos (by rw [h1])]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-w)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Ioc U (2 * U), ‖p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w)‖ ≤ 1 := by
        intro n hn
        have hn1 : 1 ≤ n := by have := (mem_Ioc.1 hn).1; omega
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have a1 : ‖p.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a2 : ‖p'.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a3 : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := norm_natCast_cpow_neg_le_one hn1 hw0
        calc ‖p.1 (n : ZMod M)‖ * ‖p'.1 (n : ZMod M)‖ * ‖(n : ℂ) ^ (-w)‖ ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
      refine (sum_le_sum this).trans ?_
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      exact_mod_cast (by omega : 2 * U - U ≤ U)
    linarith
  · rw [if_neg h1]
    by_cases h2 : p'.1 = p.1
    · rw [if_pos h2]
      have hgap : 1 ≤ |p.2.im - p'.2.im| := hsp (fun h => h1 h.symm) h2.symm
      have him : w.im ≠ 0 := by
        rw [hwim]; intro h0; rw [h0, abs_zero] at hgap; linarith
      have hsame := pair_same_bound M w hw0 hw1 him U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [h2, char_mul_conj_self]
      rw [heq]
      have hUp : (U : ℝ) ^ (1 - w.re) ≤ U := by
        calc (U : ℝ) ^ (1 - w.re) ≤ (U : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
          _ = U := Real.rpow_one _
      have hdiv : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by
        rw [hwim, mul_one_div]
        gcongr
      linarith
    · rw [if_neg h2]
      have hne : p.1 * p'.1⁻¹ ≠ 1 := by
        intro h; exact h2 (mul_inv_eq_one.1 h).symm
      have hcross := pair_cross_bound M (p.1 * p'.1⁻¹) hne w hw0 U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (p.1 * p'.1⁻¹) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [char_mul_conj]
      rw [heq]
      linarith

/- English proof (translation)
Introduce `M _ S σ T U hU hT hσ hS hsp p hp`. Establish `hU0 : (0 : ℝ) ≤ U` using `by positivity`. Establish `hM0 : (0 : ℝ) ≤ (M : ℝ)` using `by positivity`. Establish `hterm` using `fun p' (hp' : p' ∈ S) => offdiag_term σ T U hU hT hσ p p' (hS p hp) (hS p' hp') (hsp p hp p' hp')`. Use `(sum_le_sum hterm).trans ?_` and prove the remaining obligations.

Rewrite using `[sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq' S p, if_pos hp, ← sum_filter, ← mul_sum]`. Use `set Fib : Finset (DirichletCharacter ℂ M × ℂ) := S.filter (fun p' => p'.1 = p.1) with hFib`. Use `set P : Finset ℝ := Fib.image (fun p' => p'.2.im) with hP`. Establish `hinj : Set.InjOn (fun p' : DirichletCharacter ℂ M × ℂ => p'.2.im) (Fib : Set _)`. Introduce `a ha b hb hab`.

Establish `ha'` using `mem_filter.1 (mem_coe.1 ha)`. Establish `hb'` using `mem_filter.1 (mem_coe.1 hb)`. Assume the negation of the conclusion as `hne`. Use `hsp a ha'.1 b hb'.1 hne (ha'.2.trans hb'.2.symm)` as an intermediate fact. Simplify using `only at hab`.

Rewrite `this` using `[hab, sub_self, abs_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpF : p ∈ Fib` using `mem_filter.2 ⟨hp, rfl⟩`. Establish `htP : p.2.im ∈ P` using `mem_image_of_mem _ hpF`. Establish `hsp'` using `(zero_spacing P T (by linarith) (by`.

Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `mem_image.1 hx`. Conclude with `(hS a (mem_filter.1 ha).1).2.2)`. Use the proof step `(by`. Introduce `x hx y hy hxy`.

Take `⟨a, ha, rfl⟩` from `mem_image.1 hx`. Take `⟨b, hb, rfl⟩` from `mem_image.1 hy`. Establish `ha'` using `mem_filter.1 ha`. Establish `hb'` using `mem_filter.1 hb`. Conclude with `hsp a ha'.1 b hb'.1 (fun h => hxy (by rw [h])) (ha'.2.trans hb'.2.symm))).2 _ htP`.

Establish `hsumeq : ∑ p' ∈ Fib, 1 / |p.2.im - p'.2.im| = ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|`. Rewrite using `[← add_zero (∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|)]`. Establish `h0 : (0 : ℝ) = 1 / |p.2.im - p.2.im|` using `by simp`. Rewrite using `[h0, sum_erase_add P _ htP, hP, sum_image hinj]`. Rewrite using `[hsumeq]`.

Establish `hc0 : (0 : ℝ) ≤ S.card` using `by positivity`. Establish `hB0 : 0 ≤ ((M : ℝ) + 1) * (2 + 2 * T)` using `by positivity`. Establish `h1 : 4 * (U : ℝ) * ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| ≤ 4 * (U : ℝ) * (2 * (1 + Real.log (2 * T + 1)))` using `by gcongr`. Establish `h2 : (S.card : ℝ) * (4 * ((M : ℝ) + 1) * (2 + 2 * T)) ≤ (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T))`. Apply `mul_le_mul_of_nonneg_left _ hc0` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem off_diagonal_bound : Offdiag := by
  intro M _ S σ T U hU hT hσ hS hsp p hp
  classical
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hterm := fun p' (hp' : p' ∈ S) =>
    offdiag_term σ T U hU hT hσ p p' (hS p hp) (hS p' hp') (hsp p hp p' hp')
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq' S p, if_pos hp,
    ← sum_filter, ← mul_sum]
  set Fib : Finset (DirichletCharacter ℂ M × ℂ) := S.filter (fun p' => p'.1 = p.1) with hFib
  set P : Finset ℝ := Fib.image (fun p' => p'.2.im) with hP
  have hinj : Set.InjOn (fun p' : DirichletCharacter ℂ M × ℂ => p'.2.im) (Fib : Set _) := by
    intro a ha b hb hab
    have ha' := mem_filter.1 (mem_coe.1 ha)
    have hb' := mem_filter.1 (mem_coe.1 hb)
    by_contra hne
    have := hsp a ha'.1 b hb'.1 hne (ha'.2.trans hb'.2.symm)
    simp only at hab
    rw [hab, sub_self, abs_zero] at this
    linarith
  have hpF : p ∈ Fib := mem_filter.2 ⟨hp, rfl⟩
  have htP : p.2.im ∈ P := mem_image_of_mem _ hpF
  have hsp' := (zero_spacing P T (by linarith)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact (hS a (mem_filter.1 ha).1).2.2)
    (by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
      have ha' := mem_filter.1 ha
      have hb' := mem_filter.1 hb
      exact hsp a ha'.1 b hb'.1 (fun h => hxy (by rw [h])) (ha'.2.trans hb'.2.symm))).2 _ htP
  have hsumeq : ∑ p' ∈ Fib, 1 / |p.2.im - p'.2.im| = ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| := by
    rw [← add_zero (∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|)]
    have h0 : (0 : ℝ) = 1 / |p.2.im - p.2.im| := by simp
    rw [h0, sum_erase_add P _ htP, hP, sum_image hinj]
  rw [hsumeq]
  have hc0 : (0 : ℝ) ≤ S.card := by positivity
  have hB0 : 0 ≤ ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have h1 : 4 * (U : ℝ) * ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| ≤
      4 * (U : ℝ) * (2 * (1 + Real.log (2 * T + 1))) := by gcongr
  have h2 : (S.card : ℝ) * (4 * ((M : ℝ) + 1) * (2 + 2 * T)) ≤
      (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  linarith

/- English proof (translation)
Establish `h` using `Complex.cpow_conj (n : ℂ) (-z) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)`. Rewrite `h` using `[map_neg]`. Rewrite using `[h, Complex.conj_natCast]`.
-/
lemma conj_natCast_cpow_neg' (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have h := Complex.cpow_conj (n : ℂ) (-z) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [map_neg] at h
  rw [h, Complex.conj_natCast]

/- English proof (translation)
Introduce `α S f ρ Y N U σ θ G K hU hθ hσ hG hK hf hρ hoff hlarge hsmall`. Use `set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(σ : ℂ)) with hb`. Use `set v : α → ℕ → ℂ := fun p n => f p n * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) with hv`. Establish `hU0 : (0 : ℝ) < U` using `by exact_mod_cast hU`. Establish `hbv : ∀ p, ∀ n ∈ Ioc U (2 * U), b n * v p n = mco Y N n * f p n * (n : ℂ) ^ (-ρ p)`.

Introduce `p n hn`. Establish `hn0 : (n : ℂ) ≠ 0`. Use `(mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)` as an intermediate fact. Establish `: (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) = (n : ℂ) ^ (-ρ p)`. Rewrite using `[← Complex.cpow_add _ _ hn0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hb, hv]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsum : ∀ p, ∑ n ∈ Ioc U (2 * U), b n * v p n = blkD Y N U (f p) (ρ p)`. Introduce `p`. Unfold `blkD`. Conclude with `sum_congr rfl (hbv p)`. Establish `heq : ∀ p p', ∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n) = ∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) * (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ))))`.

Introduce `p p'`. Use `sum_congr rfl (fun n hn => ?_)` and prove the remaining obligations. Establish `hn0 : (n : ℂ) ≠ 0`. Use `(mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)` as an intermediate fact. Simplify using `only [hv]`.

Rewrite using `[map_mul, conj_natCast_cpow_neg']`. Establish `: (n : ℂ) ^ (-(ρ p - (σ : ℂ))) * (n : ℂ) ^ (-(starRingEnd ℂ) (ρ p' - (σ : ℂ))) = (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ))))`. Rewrite using `[← Complex.cpow_add _ _ hn0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hΔ : ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n)‖ ≤ (U : ℝ) * G + (S.card : ℝ) * K`. Introduce `p hp`. Simplify using `only [heq]`.

Conclude with `hoff p hp`. Establish `hΔ0 : (0 : ℝ) ≤ (U : ℝ) * G + (S.card : ℝ) * K` using `by positivity`. Establish `hmain` using `duality_inequality α ℕ S (Ioc U (2 * U)) b v _ hΔ0 hΔ`. Simplify using `only [hsum] at hmain`. Use `set a : ℝ := 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 with ha`.

Establish `hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ a`. Use `le_trans (le_of_eq ?_) (coefficient_block_bound Y N U σ hU hσ)` and prove the remaining obligations. Use `sum_congr rfl (fun n hn => ?_)` and prove the remaining obligations. Establish `hn1 : 0 < n` using `by have := (mem_Ioc.1 hn).1; omega`. Simplify using `only [hb, norm_mul, norm_natCast_cpow_of_pos hn1, neg_re, ofReal_re]`.

Establish `hlow : (S.card : ℝ) * θ ^ 2 ≤ ∑ p ∈ S, ‖blkD Y N U (f p) (ρ p)‖ ^ 2`. Establish `: ∀ p ∈ S, θ ^ 2 ≤ ‖blkD Y N U (f p) (ρ p)‖ ^ 2`. Introduce `p hp`. Conclude with `pow_le_pow_left₀ hθ.le (hlarge p hp) 2`. Establish `h` using `sum_le_sum this`.

Rewrite `h` using `[sum_const, nsmul_eq_mul]`. Conclude with `h`. Establish `haU : a * U = 2 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3`. Establish `: (U : ℝ) ^ (2 - 2 * σ) = (U : ℝ) ^ (1 - 2 * σ) * (U : ℝ) ^ (1 : ℝ)`. Rewrite using `[← Real.rpow_add hU0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Real.rpow_one, ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (S.card : ℝ) * θ ^ 2 ≤ a * ((U : ℝ) * G + (S.card : ℝ) * K)` using `hlow.trans (hmain.trans (mul_le_mul_of_nonneg_right hbn hΔ0))`.

Establish `hS0 : (0 : ℝ) ≤ S.card` using `by positivity`. Establish `h2 : (S.card : ℝ) * θ ^ 2 ≤ 2 * (a * U) * G`. Use `mul_le_mul_of_nonneg_left hsmall hS0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hθ2 : 0 < θ ^ 2` using `by positivity`.

Rewrite using `[le_div_iff₀ hθ2]`. Rewrite `h2` using `[haU]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dyadic_block_count : BlockCnt := by
  intro α S f ρ Y N U σ θ G K hU hθ hσ hG hK hf hρ hoff hlarge hsmall
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(σ : ℂ)) with hb
  set v : α → ℕ → ℂ := fun p n => f p n * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) with hv
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hbv : ∀ p, ∀ n ∈ Ioc U (2 * U), b n * v p n = mco Y N n * f p n * (n : ℂ) ^ (-ρ p) := by
    intro p n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    have : (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) = (n : ℂ) ^ (-ρ p) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    simp only [hb, hv]
    rw [← this]; ring
  have hsum : ∀ p, ∑ n ∈ Ioc U (2 * U), b n * v p n = blkD Y N U (f p) (ρ p) := by
    intro p; unfold blkD; exact sum_congr rfl (hbv p)
  have heq : ∀ p p', ∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n) =
      ∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
    intro p p'
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    simp only [hv]
    rw [map_mul, conj_natCast_cpow_neg']
    have : (n : ℂ) ^ (-(ρ p - (σ : ℂ))) * (n : ℂ) ^ (-(starRingEnd ℂ) (ρ p' - (σ : ℂ))) =
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    rw [← this]; ring
  have hΔ : ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n)‖ ≤
      (U : ℝ) * G + (S.card : ℝ) * K := by
    intro p hp
    simp only [heq]
    exact hoff p hp
  have hΔ0 : (0 : ℝ) ≤ (U : ℝ) * G + (S.card : ℝ) * K := by positivity
  have hmain := duality_inequality α ℕ S (Ioc U (2 * U)) b v _ hΔ0 hΔ
  simp only [hsum] at hmain
  set a : ℝ := 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 with ha
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ a := by
    refine le_trans (le_of_eq ?_) (coefficient_block_bound Y N U σ hU hσ)
    refine sum_congr rfl (fun n hn => ?_)
    have hn1 : 0 < n := by have := (mem_Ioc.1 hn).1; omega
    simp only [hb, norm_mul, norm_natCast_cpow_of_pos hn1, neg_re, ofReal_re]
  have hlow : (S.card : ℝ) * θ ^ 2 ≤ ∑ p ∈ S, ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
    have : ∀ p ∈ S, θ ^ 2 ≤ ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
      intro p hp
      exact pow_le_pow_left₀ hθ.le (hlarge p hp) 2
    have h := sum_le_sum this
    rw [sum_const, nsmul_eq_mul] at h
    exact h
  have haU : a * U = 2 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
    have : (U : ℝ) ^ (2 - 2 * σ) = (U : ℝ) ^ (1 - 2 * σ) * (U : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hU0]; congr 1; ring
    rw [this, Real.rpow_one, ha]; ring
  have h1 : (S.card : ℝ) * θ ^ 2 ≤ a * ((U : ℝ) * G + (S.card : ℝ) * K) :=
    hlow.trans (hmain.trans (mul_le_mul_of_nonneg_right hbn hΔ0))
  have hS0 : (0 : ℝ) ≤ S.card := by positivity
  have h2 : (S.card : ℝ) * θ ^ 2 ≤ 2 * (a * U) * G := by
    have := mul_le_mul_of_nonneg_left hsmall hS0
    nlinarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  rw [le_div_iff₀ hθ2]
  rw [haU] at h2
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
