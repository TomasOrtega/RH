import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionSmall

/- English proof (translation)
The claim follows from `fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)`.
-/
theorem mkF_den_ne_zero {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a) :
    P.mkF s.den ≠ 0 := fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)

/- English proof (translation)
Establish `hG` using `mkF_den_ne_zero s`. Rewrite using `[← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h, IntegralSection.toFun]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem den_mul_sub_mem {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q : MvPolynomial (Coord n) ℤ} (h : P.mkF p = s.toFun * P.mkF q) :
    s.den * p - s.num * q ∈ P.ideal := by
  have hG := mkF_den_ne_zero s
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h, IntegralSection.toFun]
  field_simp
  ring

/- English proof (translation)
Establish `hG` using `mkF_den_ne_zero s`. Establish `h'` using `(P.mkF_eq_zero_iff _).mpr h`. Rewrite `h'` using `[map_sub, map_mul, map_mul]`. Rewrite using `[IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hG]`. Take the linear combination `h'`.
-/
theorem mkF_eq_of_mem {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {e m : MvPolynomial (Coord n) ℤ} (h : s.den * e - s.num * m ∈ P.ideal) :
    P.mkF e = s.toFun * P.mkF m := by
  have hG := mkF_den_ne_zero s
  have h' := (P.mkF_eq_zero_iff _).mpr h
  rw [map_sub, map_mul, map_mul] at h'
  rw [IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hG]
  linear_combination h'

omit [Fintype ι] in

/- English proof (translation)
The claim follows from `fun k hk ↦ hc k (by simpa [evalCone] using hz.2 _ hk)`.
-/
theorem live_of_ne {P : ArithVariety n} {F : Type*} [CommRing F] {z : Cone n F} (hz : z ∈ P.points F)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)

omit [Fintype ι] in

/- English proof (translation)
Establish `h : ∀ k, ∃ i, z k i ≠ 0` using `fun k ↦ Function.ne_iff.mp (hz.1 k)`. Use `choose c hc using h`. Conclude with `⟨c, hc⟩`.
-/
theorem exists_chart {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
  have h : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c hc using h
  exact ⟨c, hc⟩

omit [DecidableEq ι] in

/- English proof (translation)
Simplify using `only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)`.
-/
theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

/- English proof (translation)
Establish `hmul : s.den * (e * q - p * m) ∈ P.ideal`. Establish `h` using `P.ideal.sub_mem (P.ideal.mul_mem_right q hem) (P.ideal.mul_mem_right m hpq)`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : e * q - p * m ∈ P.ideal` using `(P.isPrime.mem_or_mem hmul).resolve_left s.den_not_mem`.

Establish `h0` using `hz.2 _ hmem`. Simplify using `only [evalCone, eval₂_sub, eval₂_mul] at h0 ⊢`. Conclude with `sub_eq_zero.mp h0`.
-/
theorem eval_cross {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q e m : MvPolynomial (Coord n) ℤ} (hpq : s.den * p - s.num * q ∈ P.ideal)
    (hem : s.den * e - s.num * m ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z q = evalCone z p * evalCone z m := by
  have hmul : s.den * (e * q - p * m) ∈ P.ideal := by
    have h := P.ideal.sub_mem (P.ideal.mul_mem_right q hem) (P.ideal.mul_mem_right m hpq)
    convert h using 1
    ring
  have hmem : e * q - p * m ∈ P.ideal :=
    (P.isPrime.mem_or_mem hmul).resolve_left s.den_not_mem
  have h0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul] at h0 ⊢
  exact sub_eq_zero.mp h0

/- English proof (translation)
Introduce `ι _ _ n P A s`. Establish `bound : ∀ C : ℝ, s.SupNormLE A C → ∀ p q : MvPolynomial (Coord n) ℤ, P.mkF p = s.toFun * P.mkF q → ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ Real.exp C * (‖evalCone z q‖ * A.metric z)`. Introduce `C hC p q hpq z hz`. Take `⟨c, hc⟩` from `exists_chart hz`. Take `⟨d, e, he⟩` from `s.regular c (live_of_ne hz hc)`.

Establish `hcross` using `eval_cross s (den_mul_sub_mem s hpq) he.2 hz`. Establish `hm : 0 < ‖evalCone z (chartMonomial c d)‖` using `norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)`. Establish `hh : 0 < A.metric z` using `A.metric_pos z hz.1`. Establish `hb` using `hC z hz c d e he hc`. Rewrite `hb` using `[div_le_iff₀ (mul_pos hm hh)]`.

Establish `hnorm : ‖evalCone z e‖ * ‖evalCone z q‖ = ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖`. Rewrite using `[← norm_mul, ← norm_mul, hcross]`. Use `le_of_mul_le_mul_right ?_ hm` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `⟨bound, ⟨fun hs p q δp δq _ _ _ hpq z hz ↦ ?_, fun hsm z hz c d e he hc ↦ ?_⟩⟩` and prove the remaining obligations.

Simplify `bound 0 hs p q hpq z hz` using `[Real.exp_zero]`. Take `⟨⟨δ, hδ, hδd⟩, hmem⟩` from `he`. Establish `hm : 0 < ‖evalCone z (chartMonomial c d)‖` using `norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)`. Establish `hh : 0 < A.metric z` using `A.metric_pos z hz.1`. Establish `hsmall` using `hsm e (chartMonomial c d) δ d hδ (isWeightedHomogeneous_chartMonomial c d) (fun k ↦ by rw [hδd k]; ring) (mkF_eq_of_mem s hmem) z hz`.

Rewrite using `[Real.exp_zero, div_le_one (mul_pos hm hh)]`. Conclude with `hsmall`.
-/
theorem proof : SectionSmall.Statement := by
  intro ι _ _ n P A s
  have bound : ∀ C : ℝ, s.SupNormLE A C → ∀ p q : MvPolynomial (Coord n) ℤ,
      P.mkF p = s.toFun * P.mkF q →
      ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ Real.exp C * (‖evalCone z q‖ * A.metric z) := by
    intro C hC p q hpq z hz
    obtain ⟨c, hc⟩ := exists_chart hz
    obtain ⟨d, e, he⟩ := s.regular c (live_of_ne hz hc)
    have hcross := eval_cross s (den_mul_sub_mem s hpq) he.2 hz
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hb := hC z hz c d e he hc
    rw [div_le_iff₀ (mul_pos hm hh)] at hb
    have hnorm : ‖evalCone z e‖ * ‖evalCone z q‖ =
        ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖ := by
      rw [← norm_mul, ← norm_mul, hcross]
    refine le_of_mul_le_mul_right ?_ hm
    calc ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖
        = ‖evalCone z e‖ * ‖evalCone z q‖ := hnorm.symm
      _ ≤ Real.exp C * (‖evalCone z (chartMonomial c d)‖ * A.metric z) * ‖evalCone z q‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = Real.exp C * (‖evalCone z q‖ * A.metric z) * ‖evalCone z (chartMonomial c d)‖ := by ring
  refine ⟨bound, ⟨fun hs p q δp δq _ _ _ hpq z hz ↦ ?_, fun hsm z hz c d e he hc ↦ ?_⟩⟩
  · simpa [Real.exp_zero] using bound 0 hs p q hpq z hz
  · obtain ⟨⟨δ, hδ, hδd⟩, hmem⟩ := he
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hsmall := hsm e (chartMonomial c d) δ d hδ (isWeightedHomogeneous_chartMonomial c d)
      (fun k ↦ by rw [hδd k]; ring) (mkF_eq_of_mem s hmem) z hz
    rw [Real.exp_zero, div_le_one (mul_pos hm hh)]
    exact hsmall

end SectionSmall

end

end GroundTheory.Heights₂.Heights
