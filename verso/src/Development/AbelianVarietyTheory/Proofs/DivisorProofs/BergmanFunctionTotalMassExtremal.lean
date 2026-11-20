import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp.BergProof

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring)` and prove the remaining obligations.
-/
lemma sum_eq_dot {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (w : ι → ℂ) :
    ∑ i, ∑ j, H j i * (w i * (starRingEnd ℂ) (w j)) = star w ⬝ᵥ (H *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring)

/- English proof (translation)
Rewrite using `[bergmanDensity, sum_eq_dot]`.
-/
lemma berg_eq {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) :
    bergmanDensity μ v σ y = (star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y)).re := by
  rw [bergmanDensity, sum_eq_dot]

/- English proof (translation)
Establish `h'` using `Complex.le_def.mp h`. Apply the tactic sequence `apply Complex.ext <;> simp [h'.2.symm]`.
-/
lemma ofReal_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : ((z.re : ℝ) : ℂ) = z := by
  have h' := Complex.le_def.mp h
  apply Complex.ext <;> simp [h'.2.symm]

end GlobalTheory.HSAmp.BergProof

open GlobalTheory.HSAmp.BergProof in

/- English proof (translation)
Introduce `S Y _ ι _ _ μ v hF hG`. Take `⟨hHerm, hl2⟩` from `GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form S Y ι μ v hF`. Establish `hH : ((gram μ v)⁻¹).PosDef` using `hG.inv`. Establish `hu : IsUnit (gram μ v).det` using `(Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit`. Establish `hGH : gram μ v * (gram μ v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hu`.

Establish `hHG : (gram μ v)⁻¹ * gram μ v = 1` using `Matrix.nonsing_inv_mul _ hu`. Establish `hHh : ((gram μ v)⁻¹).IsHermitian` using `hH.isHermitian`. Establish `hnn : ∀ σ y, 0 ≤ star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y)` using `fun σ y => hH.posSemidef.dotProduct_mulVec_nonneg _`. Establish `key : ∀ σ y, (bergmanDensity μ v σ y : ℂ) = star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y)` using `fun σ y => by`. Rewrite using `[berg_eq]`.

Conclude with `ofReal_re_of_nonneg (hnn σ y)`. Establish `hpos : ∀ σ y, 0 ≤ bergmanDensity μ v σ y` using `fun σ y => by`. Rewrite using `[berg_eq]`. Conclude with `(Complex.le_def.mp (hnn σ y)).1`. Establish `hint : ∀ σ, Integrable (fun y => ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ)` using `fun σ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _`.

Use `⟨fun σ => (hint σ).re, ?_, hpos, ?_⟩` and prove the remaining obligations. Use `haveI : Finite S := hF.finite haveI := Fintype.ofFinite S`. Establish `hσ : ∀ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = (∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ).re` using `fun σ => by`. Establish `e1 : ∫ y, bergmanDensity μ v σ y ∂μ σ = RCLike.re (∫ y, ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) ∂μ σ)` using `integral_re (hint σ)`. Rewrite using `[e1, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]`.

Express the relevant statement in the definitionally equal form `Complex.re _ = Complex.re _`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]`. Conclude with `Finset.sum_congr rfl fun j _ => integral_const_mul _ _`.

Establish `hsum : ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j = (Fintype.card ι : ℂ)`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ j, ∑ i, (gram μ v)⁻¹ j i * gram μ v i j = ((gram μ v)⁻¹ * gram μ v) j j` using `fun j => (Matrix.mul_apply).symm`. Simplify using `only [this, hHG, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Rewrite using `[finsum_eq_sum_of_fintype]`.

Simplify using `only [hσ]`. Rewrite using `[← Complex.re_sum]`. Establish `hg : ∀ i j, gram μ v i j = ∑ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ` using `fun i j => by`. Rewrite using `[gram, Matrix.of_apply, finsum_eq_sum_of_fintype]`. Establish `hswap : ∑ σ, ∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ = ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j`.

Simplify using `only [hg, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Rewrite using `[hswap, hsum, Complex.natCast_re]`. Introduce `σ y M hM h set w := v σ y with hw set u := (gram μ v)⁻¹ *ᵥ w with hu'`.

Establish `hB` using `key σ y`. Rewrite `hB` using `[← hw]`. Establish `hdot : star u ⬝ᵥ w = star w ⬝ᵥ ((gram μ v)⁻¹ *ᵥ w)`. Rewrite using `[hu', Matrix.star_mulVec, hHh.eq, ← Matrix.dotProduct_mulVec]`. Establish `hc : cmb v (star u) σ y = bergmanDensity μ v σ y ^ 2`.

Establish `: ∑ i, star u i * v σ y i = (bergmanDensity μ v σ y : ℂ)`. Rewrite using `[hB, ← hdot]`. Both sides reduce to the same expression. Rewrite using `[cmb, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Establish `hl : l2 μ v (star u) = bergmanDensity μ v σ y`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[(hl2 (star u)).2.2, hB, ← hdot]`. Establish `hGu : gram μ v *ᵥ u = w`. Rewrite using `[hu', Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec]`. Use `conv_rhs => rw [← hGu]`.

Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, Complex.conj_conj]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `h2` using `h (star u)`. Rewrite `h2` using `[hc, hl]`. Establish `h0` using `hpos σ y`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem GlobalTheory.HSAmp.berg_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  intro S Y _ ι _ _ μ v hF hG
  obtain ⟨hHerm, hl2⟩ := GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form S Y ι μ v hF
  have hH : ((gram μ v)⁻¹).PosDef := hG.inv
  have hu : IsUnit (gram μ v).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hGH : gram μ v * (gram μ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hHG : (gram μ v)⁻¹ * gram μ v = 1 := Matrix.nonsing_inv_mul _ hu
  have hHh : ((gram μ v)⁻¹).IsHermitian := hH.isHermitian
  have hnn : ∀ σ y, 0 ≤ star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y =>
    hH.posSemidef.dotProduct_mulVec_nonneg _
  have key : ∀ σ y, (bergmanDensity μ v σ y : ℂ) = star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y => by
    rw [berg_eq]; exact ofReal_re_of_nonneg (hnn σ y)
  have hpos : ∀ σ y, 0 ≤ bergmanDensity μ v σ y := fun σ y => by
    rw [berg_eq]; exact (Complex.le_def.mp (hnn σ y)).1
  have hint : ∀ σ, Integrable (fun y => ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun σ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _
  refine ⟨fun σ => (hint σ).re, ?_, hpos, ?_⟩
  · haveI : Finite S := hF.finite
    haveI := Fintype.ofFinite S
    have hσ : ∀ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ =
        (∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ).re := fun σ => by
      have e1 : ∫ y, bergmanDensity μ v σ y ∂μ σ =
          RCLike.re (∫ y, ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) ∂μ σ) :=
        integral_re (hint σ)
      rw [e1, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      change Complex.re _ = Complex.re _
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    have hsum : ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j = (Fintype.card ι : ℂ) := by
      rw [Finset.sum_comm]
      have : ∀ j, ∑ i, (gram μ v)⁻¹ j i * gram μ v i j = ((gram μ v)⁻¹ * gram μ v) j j :=
        fun j => (Matrix.mul_apply).symm
      simp only [this, hHG, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [finsum_eq_sum_of_fintype]
    simp only [hσ]
    rw [← Complex.re_sum]
    have hg : ∀ i j, gram μ v i j = ∑ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := fun i j => by
      rw [gram, Matrix.of_apply, finsum_eq_sum_of_fintype]
    have hswap : ∑ σ, ∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ =
        ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j := by
      simp only [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap, hsum, Complex.natCast_re]
  · intro σ y M hM h
    set w := v σ y with hw
    set u := (gram μ v)⁻¹ *ᵥ w with hu'
    have hB := key σ y
    rw [← hw] at hB
    have hdot : star u ⬝ᵥ w = star w ⬝ᵥ ((gram μ v)⁻¹ *ᵥ w) := by
      rw [hu', Matrix.star_mulVec, hHh.eq, ← Matrix.dotProduct_mulVec]
    have hc : cmb v (star u) σ y = bergmanDensity μ v σ y ^ 2 := by
      have : ∑ i, star u i * v σ y i = (bergmanDensity μ v σ y : ℂ) := by
        rw [hB, ← hdot]; rfl
      rw [cmb, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hl : l2 μ v (star u) = bergmanDensity μ v σ y := by
      apply Complex.ofReal_injective
      rw [(hl2 (star u)).2.2, hB, ← hdot]
      have hGu : gram μ v *ᵥ u = w := by
        rw [hu', Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec]
      conv_rhs => rw [← hGu]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := h (star u)
    rw [hc, hl] at h2
    have h0 := hpos σ y
    nlinarith
