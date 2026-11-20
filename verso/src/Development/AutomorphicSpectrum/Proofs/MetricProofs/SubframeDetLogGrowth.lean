import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

section SlopeTestRemainingChoices

open scoped ComplexOrder MatrixOrder

variable {g k : ℕ}

/- English proof (translation)
Establish `hH : (A.map Complex.ofReal).IsHermitian` using `h.isHermitian.map _ (fun x => by simp [Complex.conj_ofReal])`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => ?_)` and prove the remaining obligations. Establish `hu` using `h.dotProduct_mulVec_nonneg (fun i => (x i).re)`. Establish `hv` using `h.dotProduct_mulVec_nonneg (fun i => (x i).im)`. Simplify using `only [dotProduct, mulVec, Pi.star_apply, star_trivial] at hu hv`.

Establish `key : (star x ⬝ᵥ (A.map Complex.ofReal) *ᵥ x).re = ∑ i, ((x i).re * ∑ j, A i j * (x j).re + (x i).im * ∑ j, A i j * (x j).im)`. Simplify using `only [dotProduct, mulVec, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.re_sum, Complex.im_sum, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]`. Expand and normalize the polynomial expressions, which then agree.

Establish `him` using `hH.im_star_dotProduct_mulVec_self x`. Rewrite `him` using `[RCLike.im_to_complex]`. Rewrite using `[Complex.nonneg_iff]`. Use `⟨?_, him.symm⟩` and prove the remaining obligations. Rewrite using `[key, Finset.sum_add_distrib]`.

Conclude with `add_nonneg hu hv`.
-/
theorem subframe_map_posSemidef {A : Matrix (Fin g) (Fin g) ℝ} (h : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  have hH : (A.map Complex.ofReal).IsHermitian :=
    h.isHermitian.map _ (fun x => by simp [Complex.conj_ofReal])
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => ?_)
  have hu := h.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hv := h.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial] at hu hv
  have key : (star x ⬝ᵥ (A.map Complex.ofReal) *ᵥ x).re =
      ∑ i, ((x i).re * ∑ j, A i j * (x j).re + (x i).im * ∑ j, A i j * (x j).im) := by
    simp only [dotProduct, mulVec, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.re_sum, Complex.im_sum,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [RCLike.im_to_complex] at him
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  rw [key, Finset.sum_add_distrib]
  exact add_nonneg hu hv

/- English proof (translation)
Establish `hmap : ∀ {P Q : Matrix (Fin g) (Fin g) ℝ}, P ≤ Q → P.map Complex.ofReal ≤ Q.map Complex.ofReal`. Introduce `P Q hPQ`. Rewrite `hPQ`, the goal using `[Matrix.le_iff]`. Use `subframe_map_posSemidef hPQ` as an intermediate fact. Rewrite `this` using `[Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b)]`. Then use the resulting hypothesis.

Establish `hone : ∀ t : ℝ, (t • (1 : Matrix (Fin g) (Fin g) ℝ)).map Complex.ofReal = t • (1 : Matrix (Fin g) (Fin g) ℂ)`. Introduce `t`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Complex.real_smul]`. Establish `hc1 : (c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosDef` using `Matrix.PosDef.one.smul hc`.

Establish `hle1 : c • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y` using `Matrix.le_iff.mpr h1`. Establish `hle2 : Y ≤ D • (1 : Matrix (Fin g) (Fin g) ℝ)` using `Matrix.le_iff.mpr h2`. Establish `hY : Y.PosDef` using `GlobalTheory.posDef_of_le hc1 hle1`. Establish `hlo : D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y⁻¹` using `GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hY hD hle2`. Establish `hhi : Y⁻¹ ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ)`.

Use `GlobalTheory.inv_le_inv_of_posDef_of_le hc1 hle1` as an intermediate fact. Rewrite `this` using `[GlobalTheory.inv_real_smul_of_posDef Matrix.PosDef.one hc.ne', inv_one]`. Then use the resulting hypothesis. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hmap hlo` as an intermediate fact. Rewrite `this` using `[hone]`. Then use the resulting hypothesis.

Use `hmap hhi` as an intermediate fact. Rewrite `this` using `[hone]`. Then use the resulting hypothesis.
-/
theorem subframe_inv_bounds (Y : Matrix (Fin g) (Fin g) ℝ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (h1 : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef)
    (h2 : (D • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) :
    D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ (Y⁻¹).map Complex.ofReal ∧
      (Y⁻¹).map Complex.ofReal ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  have hmap : ∀ {P Q : Matrix (Fin g) (Fin g) ℝ}, P ≤ Q →
      P.map Complex.ofReal ≤ Q.map Complex.ofReal := by
    intro P Q hPQ
    rw [Matrix.le_iff] at hPQ ⊢
    have := subframe_map_posSemidef hPQ
    rwa [Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b)] at this
  have hone : ∀ t : ℝ, (t • (1 : Matrix (Fin g) (Fin g) ℝ)).map Complex.ofReal =
      t • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t; ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Complex.real_smul]
  have hc1 : (c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have hle1 : c • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y := Matrix.le_iff.mpr h1
  have hle2 : Y ≤ D • (1 : Matrix (Fin g) (Fin g) ℝ) := Matrix.le_iff.mpr h2
  have hY : Y.PosDef := GlobalTheory.posDef_of_le hc1 hle1
  have hlo : D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y⁻¹ :=
    GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hY hD hle2
  have hhi : Y⁻¹ ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) := by
    have := GlobalTheory.inv_le_inv_of_posDef_of_le hc1 hle1
    rwa [GlobalTheory.inv_real_smul_of_posDef Matrix.PosDef.one hc.ne', inv_one] at this
  refine ⟨?_, ?_⟩
  · have := hmap hlo
    rwa [hone] at this
  · have := hmap hhi
    rwa [hone] at this

/- English proof (translation)
Establish `hA : A.PosSemidef` using `GlobalTheory.posSemidef_of_le (Matrix.PosSemidef.one.smul ha) h1`. Establish `hPP : (Pᴴ * P).PosSemidef` using `Matrix.posSemidef_conjTranspose_mul_self P`. Establish `hsm : ∀ t : ℝ, Pᴴ * (t • (1 : Matrix (Fin g) (Fin g) ℂ)) * P = t • (Pᴴ * P)`. Introduce `t`. Rewrite using `[Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`.

Establish `hlo : a • (Pᴴ * P) ≤ Pᴴ * A * P`. Use `GlobalTheory.conjTranspose_mul_mul_le_of_le h1 P` as an intermediate fact. Rewrite `this` using `[hsm]`. Then use the resulting hypothesis. Establish `hhi : Pᴴ * A * P ≤ b • (Pᴴ * P)`. Use `GlobalTheory.conjTranspose_mul_mul_le_of_le h2 P` as an intermediate fact.

Rewrite `this` using `[hsm]`. Then use the resulting hypothesis. Establish `hdetsm : ∀ t : ℝ, ((t • (Pᴴ * P)).det).re = t ^ k * ((Pᴴ * P).det).re`. Introduce `t`. Establish `he : t • (Pᴴ * P) = (t : ℂ) • (Pᴴ * P)`. Use extensionality with `i j`.

Simplify using `[Complex.real_smul]`. Rewrite using `[he, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.pow_mul_re_det_le_of_smul_le hPP ha hlo` as an intermediate fact. Simplify `this` using `[Fintype.card_fin]`.

Use `GlobalTheory.re_det_le_re_det_of_posSemidef_of_le (hA.conjTranspose_mul_mul_same P) hhi` as an intermediate fact. Rewrite `this` using `[RCLike.re_to_complex, RCLike.re_to_complex, hdetsm]`. Conclude with `this`.
-/
theorem subframe_det_bounds (P : Matrix (Fin g) (Fin k) ℂ) (A : Matrix (Fin g) (Fin g) ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (h1 : a • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ A)
    (h2 : A ≤ b • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    a ^ k * (Pᴴ * P).det.re ≤ (Pᴴ * A * P).det.re ∧
      (Pᴴ * A * P).det.re ≤ b ^ k * (Pᴴ * P).det.re := by
  have hA : A.PosSemidef := GlobalTheory.posSemidef_of_le (Matrix.PosSemidef.one.smul ha) h1
  have hPP : (Pᴴ * P).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self P
  have hsm : ∀ t : ℝ, Pᴴ * (t • (1 : Matrix (Fin g) (Fin g) ℂ)) * P = t • (Pᴴ * P) := by
    intro t; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hlo : a • (Pᴴ * P) ≤ Pᴴ * A * P := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h1 P
    rwa [hsm] at this
  have hhi : Pᴴ * A * P ≤ b • (Pᴴ * P) := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h2 P
    rwa [hsm] at this
  have hdetsm : ∀ t : ℝ, ((t • (Pᴴ * P)).det).re = t ^ k * ((Pᴴ * P).det).re := by
    intro t
    have he : t • (Pᴴ * P) = (t : ℂ) • (Pᴴ * P) := by
      ext i j; simp [Complex.real_smul]
    rw [he, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  refine ⟨?_, ?_⟩
  · have := GlobalTheory.pow_mul_re_det_le_of_smul_le hPP ha hlo
    simpa [Fintype.card_fin] using this
  · have := GlobalTheory.re_det_le_re_det_of_posSemidef_of_le (hA.conjTranspose_mul_mul_same P) hhi
    rw [RCLike.re_to_complex, RCLike.re_to_complex, hdetsm] at this
    exact this

/- English proof (translation)
Establish `hr : (F.map star).rank = k`. Establish `he : F.map star = (Fᴴ)ᵀ`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Rewrite using `[he, Matrix.rank_transpose, Matrix.rank_conjTranspose, h]`.

Establish `hr' : Module.finrank ℂ (LinearMap.range (F.map star).mulVecLin) = k` using `hr`. Establish `hsum` using `LinearMap.finrank_range_add_finrank_ker (F.map star).mulVecLin`. Rewrite `hsum` using `[Module.finrank_fin_fun, hr']`. Establish `hker0 : Module.finrank ℂ (LinearMap.ker (F.map star).mulVecLin) = 0` using `by omega`. Establish `hbot : LinearMap.ker (F.map star).mulVecLin = ⊥` using `Submodule.finrank_eq_zero.mp hker0`.

Establish `hinj : Function.Injective (F.map star).mulVec`. Introduce `v w hvw`. Establish `h0 : (F.map star).mulVec (v - w) = 0`. Rewrite using `[Matrix.mulVec_sub, hvw, sub_self]`. Use `(Matrix.ker_mulVecLin_eq_bot_iff.mp hbot) (v - w) h0` as an intermediate fact.

Conclude with `sub_eq_zero.mp this`. Conclude with `Matrix.PosDef.conjTranspose_mul_self _ hinj`.
-/
theorem subframe_gram_posDef (F : Matrix (Fin g) (Fin k) ℂ) (h : F.rank = k) :
    ((F.map star)ᴴ * F.map star).PosDef := by
  have hr : (F.map star).rank = k := by
    have he : F.map star = (Fᴴ)ᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he, Matrix.rank_transpose, Matrix.rank_conjTranspose, h]
  have hr' : Module.finrank ℂ (LinearMap.range (F.map star).mulVecLin) = k := hr
  have hsum := LinearMap.finrank_range_add_finrank_ker (F.map star).mulVecLin
  rw [Module.finrank_fin_fun, hr'] at hsum
  have hker0 : Module.finrank ℂ (LinearMap.ker (F.map star).mulVecLin) = 0 := by omega
  have hbot : LinearMap.ker (F.map star).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hinj : Function.Injective (F.map star).mulVec := by
    intro v w hvw
    have h0 : (F.map star).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have := (Matrix.ker_mulVecLin_eq_bot_iff.mp hbot) (v - w) h0
    exact sub_eq_zero.mp this
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

/- English proof (translation)
Conclude with `Complex.continuous_re.comp ((continuous_id.matrix_transpose.matrix_mul (continuous_id.matrix_map continuous_star)).matrix_det)`.
-/
theorem subframe_continuous_det :
    Continuous fun M : Matrix (Fin g) (Fin k) ℂ => ((Mᵀ * M.map star).det).re := by
  exact Complex.continuous_re.comp
    ((continuous_id.matrix_transpose.matrix_mul (continuous_id.matrix_map continuous_star)).matrix_det)

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `g k X _ K hK F hF hrank c C hc`. Distinguish the cases in `hne : K.Nonempty`. Use `swap`. Conclude with `⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩`. Establish `hT : ∀ x, ((F x).map star)ᴴ = (F x)ᵀ`.

Introduce `x`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `hGc : ContinuousOn (fun x => (((F x)ᵀ * (F x).map star).det).re) K` using `subframe_continuous_det.comp_continuousOn hF`. Take `⟨M, hM⟩` from `hK.exists_bound_of_continuousOn hGc`.

Take `⟨x₀, hx₀K, hx₀⟩` from `hK.exists_isMinOn hne hGc`. Establish `hGpos : ∀ x ∈ K, 0 < (((F x)ᵀ * (F x).map star).det).re`. Introduce `x hx`. Establish `hpd` using `subframe_gram_posDef (F x) (hrank x hx)`. Rewrite `hpd` using `[hT]`.

Use `GlobalTheory.re_det_pos_of_posDef hpd` as an intermediate fact. Simplify using `using this`. Take `⟨m, hm⟩ : ∃ m, m = (((F x₀)ᵀ * (F x₀).map star).det).re` from `⟨_, rfl⟩`. Establish `hmpos : 0 < m` using `by rw [hm]; exact hGpos x₀ hx₀K`. Establish `hA0 : 0 ≤ c⁻¹ ^ k * |M|` using `mul_nonneg (pow_nonneg (inv_nonneg.2 hc.le) k) (abs_nonneg M)`.

Establish `hB0 : 0 ≤ |C| ^ k / m` using `div_nonneg (pow_nonneg (abs_nonneg C) k) hmpos.le`. Use `⟨c⁻¹ ^ k * |M| + |C| ^ k / m + 1, by linarith, ?_⟩` and prove the remaining obligations. Introduce `x hx Y r hr h1 h2 d`. Establish `hd : d = (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re` using `rfl`. Break down `Nat.eq_zero_or_pos g with hg0 | hgpos` into its components or cases.

Substitute `hg0` using the available equality. Establish `hk : k = 0`. Use `Matrix.rank_le_height (F x)` as an intermediate fact. Rewrite `this` using `[hrank x hx]`. Use linear arithmetic over natural numbers and integers.

Substitute `hk` using the available equality. Establish `hd1 : d = 1`. Rewrite using `[hd, Matrix.det_isEmpty, Complex.one_re]`. Rewrite using `[hd1]`. Simplify using `only [pow_zero, one_mul, mul_one] at hA0 hB0 ⊢`.

Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> linarith`. Establish `hdiag` using `(h1.add h2).diag_nonneg (i := ⟨0, hgpos⟩)`. Establish `hcr : c ≤ C * r`. Simplify using `[Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq] at hdiag`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hCr : 0 < C * r` using `lt_of_lt_of_le hc hcr`. Establish `hr0 : 0 < r` using `by linarith`. Establish `hC : 0 < C` using `by nlinarith`. Establish `hinv` using `subframe_inv_bounds Y hc hCr h1 h2`. Establish `hb` using `subframe_det_bounds ((F x).map star) ((Y⁻¹).map Complex.ofReal) (inv_nonneg.2 hCr.le) hinv.1 hinv.2`.

Rewrite `hb` using `[hT]`. Take `⟨hlo, hhi⟩` from `hb`. Establish `hGx_le : (((F x)ᵀ * (F x).map star).det).re ≤ |M|`. Use `hM x hx` as an intermediate fact. Simplify using `only [Real.norm_eq_abs] at this`.

Conclude with `le_trans (le_abs_self _) (le_trans this (le_abs_self M))`. Establish `hGx_ge : m ≤ (((F x)ᵀ * (F x).map star).det).re`. Use `isMinOn_iff.mp hx₀ x hx` as an intermediate fact. Rewrite using `[hm]`. Conclude with `this`.

Rewrite using `[hd]`. Generalize the expression as in `(((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re = D at hlo hhi ⊢`. Generalize the expression as in `(((F x)ᵀ * (F x).map star).det).re = Gx at hlo hhi hGx_le hGx_ge`. Establish `hpk : 0 < (C * r)⁻¹ ^ k` using `pow_pos (inv_pos.2 hCr) k`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h3 : c⁻¹ ^ k * Gx ≤ c⁻¹ ^ k * |M|` using `mul_le_mul_of_nonneg_left hGx_le (pow_nonneg (inv_nonneg.2 hc.le) k)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDlo : (C * r)⁻¹ ^ k * m ≤ D` using `le_trans (mul_le_mul_of_nonneg_left hGx_ge hpk.le) hlo`. Establish `hone : |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) = 1`. Rewrite using `[abs_of_pos hC, inv_pow, mul_pow]`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul _ hDlo (mul_nonneg hpk.le hmpos.le)` to reduce the goal to its premises. Conclude with `mul_nonneg (by linarith) (pow_nonneg hr0.le k)`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0.le k)`.
-/
theorem subframe_det_log_growth : ∀ (g k : ℕ) (X : Type) [TopologicalSpace X] (K : Set X), IsCompact K → ∀ (F : X → Matrix (Fin g) (Fin k) ℂ), ContinuousOn F K → (∀ x ∈ K, (F x).rank = k) → ∀ c C : ℝ, 0 < c → ∃ C' : ℝ, 0 < C' ∧ ∀ x ∈ K, ∀ (Y : Matrix (Fin g) (Fin g) ℝ) (r : ℝ), 1 ≤ r → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ((C * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → let d := (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re; d ≤ C' ∧ 1 ≤ C' * r ^ k * d := by
  intro g k X _ K hK F hF hrank c C hc
  by_cases hne : K.Nonempty
  swap
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hT : ∀ x, ((F x).map star)ᴴ = (F x)ᵀ := by
    intro x; ext i j; simp [Matrix.conjTranspose_apply]
  have hGc : ContinuousOn (fun x => (((F x)ᵀ * (F x).map star).det).re) K :=
    subframe_continuous_det.comp_continuousOn hF
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGc
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hGc
  have hGpos : ∀ x ∈ K, 0 < (((F x)ᵀ * (F x).map star).det).re := by
    intro x hx
    have hpd := subframe_gram_posDef (F x) (hrank x hx)
    rw [hT] at hpd
    have := GlobalTheory.re_det_pos_of_posDef hpd
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, m = (((F x₀)ᵀ * (F x₀).map star).det).re := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact hGpos x₀ hx₀K
  have hA0 : 0 ≤ c⁻¹ ^ k * |M| := mul_nonneg (pow_nonneg (inv_nonneg.2 hc.le) k) (abs_nonneg M)
  have hB0 : 0 ≤ |C| ^ k / m := div_nonneg (pow_nonneg (abs_nonneg C) k) hmpos.le
  refine ⟨c⁻¹ ^ k * |M| + |C| ^ k / m + 1, by linarith, ?_⟩
  intro x hx Y r hr h1 h2 d
  have hd : d = (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re := rfl
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · subst hg0
    have hk : k = 0 := by
      have := Matrix.rank_le_height (F x)
      rw [hrank x hx] at this
      omega
    subst hk
    have hd1 : d = 1 := by
      rw [hd, Matrix.det_isEmpty, Complex.one_re]
    rw [hd1]
    simp only [pow_zero, one_mul, mul_one] at hA0 hB0 ⊢
    refine ⟨?_, ?_⟩ <;> linarith
  · have hdiag := (h1.add h2).diag_nonneg (i := ⟨0, hgpos⟩)
    have hcr : c ≤ C * r := by
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq] at hdiag
      linarith
    have hCr : 0 < C * r := lt_of_lt_of_le hc hcr
    have hr0 : 0 < r := by linarith
    have hC : 0 < C := by nlinarith
    have hinv := subframe_inv_bounds Y hc hCr h1 h2
    have hb := subframe_det_bounds ((F x).map star) ((Y⁻¹).map Complex.ofReal)
      (inv_nonneg.2 hCr.le) hinv.1 hinv.2
    rw [hT] at hb
    obtain ⟨hlo, hhi⟩ := hb
    have hGx_le : (((F x)ᵀ * (F x).map star).det).re ≤ |M| := by
      have := hM x hx
      simp only [Real.norm_eq_abs] at this
      exact le_trans (le_abs_self _) (le_trans this (le_abs_self M))
    have hGx_ge : m ≤ (((F x)ᵀ * (F x).map star).det).re := by
      have := isMinOn_iff.mp hx₀ x hx
      rw [hm]; exact this
    rw [hd]
    generalize (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re = D at hlo hhi ⊢
    generalize (((F x)ᵀ * (F x).map star).det).re = Gx at hlo hhi hGx_le hGx_ge
    have hpk : 0 < (C * r)⁻¹ ^ k := pow_pos (inv_pos.2 hCr) k
    refine ⟨?_, ?_⟩
    · have h3 : c⁻¹ ^ k * Gx ≤ c⁻¹ ^ k * |M| :=
        mul_le_mul_of_nonneg_left hGx_le (pow_nonneg (inv_nonneg.2 hc.le) k)
      linarith
    · have hDlo : (C * r)⁻¹ ^ k * m ≤ D := le_trans (mul_le_mul_of_nonneg_left hGx_ge hpk.le) hlo
      have hone : |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) = 1 := by
        rw [abs_of_pos hC, inv_pow, mul_pow]
        field_simp
      calc (1 : ℝ) = |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) := hone.symm
        _ ≤ (c⁻¹ ^ k * |M| + |C| ^ k / m + 1) * r ^ k * D := by
          apply mul_le_mul _ hDlo (mul_nonneg hpk.le hmpos.le)
          · exact mul_nonneg (by linarith) (pow_nonneg hr0.le k)
          · exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0.le k)

end GlobalTheory.CompanionTheory.Ar.Flat
