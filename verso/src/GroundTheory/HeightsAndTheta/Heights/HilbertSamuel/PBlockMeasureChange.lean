import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMeasureChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory Matrix
  SupBoundCount

noncomputable section

namespace BlockMeasureChange

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Take `⟨C, hC⟩` from `hS D K ι Ω d`. Use `⟨max C 1, le_max_right _ _, fun n hn F hF z hz => (hC n hn F hF z hz).trans ?_⟩` and prove the remaining obligations. Establish `h0 : 0 ≤ blockL2Norm d n F` using `Real.sqrt_nonneg _`. Establish `h1 : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2)` using `by positivity`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h0`.
-/
theorem sup_one_le (hS : SupBoundBlock.Statement) (d : HSMBlockDatum D K ι Ω) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2)) * blockL2Norm d n F := by
  obtain ⟨C, hC⟩ := hS D K ι Ω d
  refine ⟨max C 1, le_max_right _ _, fun n hn F hF z hz => (hC n hn F hF z hz).trans ?_⟩
  have h0 : 0 ≤ blockL2Norm d n F := Real.sqrt_nonneg _
  have h1 : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h0

/- English proof (translation)
Establish `h` using `norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := c) (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hg0 x)]; exact hgc x)`. Rewrite `h` using `[probReal_univ, mul_one, Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans h`.
-/
theorem integral_le_of_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ}
    {c : ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgc : ∀ x, g x ≤ c) : ∫ x, g x ∂μ ≤ c := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := c)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hg0 x)]; exact hgc x)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/- English proof (translation)
Rewrite using `[gram_quad d n f hf a]`. Establish `hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n)` using `fun w t => div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)`. Use `integral_nonneg (μ := d.dV) (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => hp _ _` as an intermediate fact. Use `integral_nonneg (μ := d.dV) (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n)) fun x => hp _ _` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf a]
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => hp _ _
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n))
    fun x => hp _ _
  positivity

/- English proof (translation)
Establish `hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n)` using `fun k => by rw [hk]; exact hf k`. Use `d'.vol.1` as an intermediate fact. Establish `hQ` using `quad_nonneg d n f hf a`. Use `set Q := a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)`. Establish `hpt : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) ≤ c ^ 2 * Q`.

Introduce `z hz`. Establish `h1` using `sup_real d n f hf hc hsup a hz`. Establish `h0 : 0 ≤ ‖comb f a z‖ / d.A.h z ^ n` using `div_nonneg (norm_nonneg _) (pow_pos (d.A.pos z hz.1) n).le`. Establish `h2` using `pow_le_pow_left₀ h0 h1 2`. Rewrite `h2` using `[div_pow, ← pow_mul', mul_pow, Real.sq_sqrt hQ]`. Then use the resulting hypothesis.

Establish `hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n)` using `fun w t => div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)`. Establish `hmem : ∀ x, blockPt d' x ∈ mcPts (mCoordIdeal d.y)` using `fun x => hy ▸ blockPt_mem d' x`. Rewrite using `[gram_quad d' n f hf' a, hA]`. Establish `i1` using `integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (hmem x)`. Establish `i2` using `integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (conjPt_mem_mcPts (hmem x))`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem quad_le (d d' : HSMBlockDatum D K ι Ω) (hy : d'.y = d.y) (hk : d'.k₀ = d.k₀) (hA : d'.A = d.A) (n : ℕ)
    {r : ℕ} (f : Fin r → MRing ι) (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) (a : Fin r → ℝ) :
    a ⬝ᵥ (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) ≤
      c ^ 2 * (a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)) := by
  have hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
  have := d'.vol.1
  have hQ := quad_nonneg d n f hf a
  set Q := a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)
  have hpt : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) ≤ c ^ 2 * Q := by
    intro z hz
    have h1 := sup_real d n f hf hc hsup a hz
    have h0 : 0 ≤ ‖comb f a z‖ / d.A.h z ^ n :=
      div_nonneg (norm_nonneg _) (pow_pos (d.A.pos z hz.1) n).le
    have h2 := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, ← pow_mul', mul_pow, Real.sq_sqrt hQ] at h2
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have hmem : ∀ x, blockPt d' x ∈ mcPts (mCoordIdeal d.y) := fun x => hy ▸ blockPt_mem d' x
  rw [gram_quad d' n f hf' a, hA]
  have i1 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (hmem x)
  have i2 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (conjPt_mem_mcPts (hmem x))
  linarith

/- English proof (translation)
Establish `hH : (c • G - G').IsHermitian`. Use `Matrix.IsHermitian.ext fun i j => ?_` and prove the remaining obligations. Establish `e1` using `hG.apply i j`. Establish `e2` using `hG'.1.apply i j`. Simplify using `only [star_trivial] at e1 e2 ⊢`.

Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, e1, e2]`. Establish `hpsd : (c • G - G').PosSemidef`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun a => ?_` and prove the remaining obligations. Rewrite using `[star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Combine the linear relations using `[h a]`.

Use `GroundTheory.Heights₂.Heights.MCDet.re_det_mono hG' (by simpa using hpsd)` as an intermediate fact. Simplify `this` using `[det_smul]`.
-/
theorem det_le {r : ℕ} {G G' : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) (hG' : G'.PosSemidef) {c : ℝ}
    (h : ∀ a, a ⬝ᵥ (G' *ᵥ a) ≤ c * (a ⬝ᵥ (G *ᵥ a))) : G'.det ≤ c ^ r * G.det := by
  have hH : (c • G - G').IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    have e1 := hG.apply i j
    have e2 := hG'.1.apply i j
    simp only [star_trivial] at e1 e2 ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, e1, e2]
  have hpsd : (c • G - G').PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun a => ?_
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith [h a]
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hG' (by simpa using hpsd)
  simpa [det_smul] using this

end BlockMeasureChange

open BlockMeasureChange in

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ d d' hy hk hA`. Take `⟨C, hC, hsup⟩` from `sup_one_le hS d`. Take `⟨C', hC', hsup'⟩` from `sup_one_le hS d'`. Use `set L := max C C' with hL`. Establish `hL1 : 1 ≤ L` using `hC.trans (le_max_left _ _)`.

Establish `key : ∀ n : ℕ, 1 ≤ n → |blockChi d' n - blockChi d n| ≤ (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n))`. Introduce `n hn`. Establish `hex` using `exists_isSecBasisM d.y d.k₀ n`. Establish `hb` using `hex.choose_spec`. Use `choose f hf hfe using hb.1`.

Establish `hbf : hex.choose.2 = fun j => map (Int.castRingHom ℚ) (f j)` using `funext hfe`. Establish `hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n)` using `fun k => by rw [hk]; exact hf k`. Establish `hli : LinearIndependent ℤ fun k => aeval d.y (f k)`. Use `hb.2.1` as an intermediate fact. Simplify using `only [hbf, aeval_map_int] at this`.

Conclude with `this`. Establish `hli' : LinearIndependent ℤ fun k => aeval d'.y (f k)` using `by rw [hy]; exact hli`. Establish `hsame : ∀ (y' : (Σ k, ι k) → Ω) (k' : K), y' = d.y → k' = d.k₀ → ∀ h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y' k' n p.2, h.choose = hex.choose`. Introduce and unpack `_ _ rfl rfl h`. Both sides reduce to the same expression.

Establish `hex' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d'.y d'.k₀ n p.2`. Rewrite using `[hy, hk]`. Conclude with `hex`. Establish `e1 : blockChi d n = -(1 / 2) * Real.log (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).det`. Rewrite using `[blockChi, dif_pos hex, hbf]`.

Establish `e2 : blockChi d' n = -(1 / 2) * Real.log (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))).det`. Rewrite using `[blockChi, dif_pos hex', hsame _ _ hy hk hex', hbf]`. Use `set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))`. Use `set G' := blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))`. Establish `hnR : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Use `set s := (n : ℝ) ^ ((D : ℝ) / 2) with hs`. Establish `hs1 : 1 ≤ s` using `Real.one_le_rpow hnR (by positivity)`. Establish `hs2 : s ^ 2 = (n : ℝ) ^ D`. Rewrite using `[hs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlogs : Real.log s = (D / 2) * Real.log n`. Rewrite using `[hs, Real.log_rpow (by positivity)]`. Use `set c := C * s`. Use `set c' := C' * s`.

Establish `hc : 1 ≤ c` using `one_le_mul_of_one_le_of_one_le hC hs1`. Establish `hc' : 1 ≤ c'` using `one_le_mul_of_one_le_of_one_le hC' hs1`. Establish `hG : G.PosDef` using `gram_posDef d n f hf hli (by linarith) (hsup n hn)`. Establish `hG' : G'.PosDef` using `gram_posDef d' n f hf' hli' (by linarith) (hsup' n hn)`. Establish `q1` using `quad_le d d' hy hk hA n f hf (by linarith) (hsup n hn)`.

Establish `q2` using `quad_le d' d hy.symm hk.symm hA.symm n f hf' (by linarith) (hsup' n hn)`. Establish `d1` using `det_le hG.isHermitian hG'.posSemidef q1`. Establish `d2` using `det_le hG'.isHermitian hG.posSemidef q2`. Establish `hr` using `SupBoundCount.rank_le d n f hf hli (by linarith) (hsup n hn)`. Establish `p1` using `hG.det_pos`.

Establish `p2` using `hG'.det_pos`. Establish `l1 : Real.log G'.det ≤ hex.choose.1 * Real.log (c ^ 2) + Real.log G.det`. Rewrite using `[← Real.log_pow, ← Real.log_mul (by positivity) p1.ne']`. Conclude with `Real.log_le_log p2 d1`. Establish `l2 : Real.log G.det ≤ hex.choose.1 * Real.log (c' ^ 2) + Real.log G'.det`.

Rewrite using `[← Real.log_pow, ← Real.log_mul (by positivity) p2.ne']`. Conclude with `Real.log_le_log p1 d2`. Establish `lc : Real.log c ≤ Real.log L + D * Real.log n`. Establish `hln : 0 ≤ Real.log n` using `Real.log_nonneg hnR`. Rewrite using `[Real.log_mul (by linarith) (by linarith), hlogs]`.

Use `Real.log_le_log (by linarith) (le_max_left C C')` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `lc' : Real.log c' ≤ Real.log L + D * Real.log n`. Establish `hln : 0 ≤ Real.log n` using `Real.log_nonneg hnR`. Rewrite using `[Real.log_mul (by linarith) (by linarith), hlogs]`.

Use `Real.log_le_log (by linarith) (le_max_right C C')` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hlc : 0 ≤ Real.log c` using `Real.log_nonneg hc`. Establish `hlc' : 0 ≤ Real.log c'` using `Real.log_nonneg hc'`. Establish `hr0 : (0 : ℝ) ≤ (hex.choose.1 : ℝ)` using `Nat.cast_nonneg _`.

Establish `hrb : (hex.choose.1 : ℝ) ≤ 2 * L ^ 2 * (n : ℝ) ^ D`. Establish `: c ^ 2 ≤ L ^ 2 * (n : ℝ) ^ D`. Rewrite using `[mul_pow, hs2]`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) 2) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `l1`, `l2` using `[Real.log_pow]`. Move the coercions through the operations in `at l1 l2`. Establish `hdiff : |blockChi d' n - blockChi d n| ≤ hex.choose.1 * (Real.log L + D * Real.log n)`. Establish `m1` using `mul_le_mul_of_nonneg_left lc hr0`. Establish `m2` using `mul_le_mul_of_nonneg_left lc' hr0`.

Rewrite using `[e1, e2, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hln : 0 ≤ Real.log n` using `Real.log_nonneg hnR`. Establish `hlL : 0 ≤ Real.log L` using `Real.log_nonneg hL1`. Establish `hnD : 0 ≤ (n : ℝ) ^ D` using `by positivity`.

Use `hdiff.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `: Real.log L + D * Real.log n ≤ (Real.log L + D) * (1 + Real.log n)`. Establish `h3 : 0 ≤ Real.log L * Real.log n` using `mul_nonneg hlL hln`. Establish `h4 : (0 : ℝ) ≤ D` using `Nat.cast_nonneg _`.

Establish `e : (Real.log L + D) * (1 + Real.log n) = Real.log L + D * Real.log n + (D + Real.log L * Real.log n)` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hO : (fun n : ℕ => blockChi d' n - blockChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n)`.

Use `IsBigO.of_bound (2 * L ^ 2 * (Real.log L + D)) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs]`. Use `(key n hn).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Establish `hnR : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`.

Rewrite using `[abs_of_nonneg (mul_nonneg (by positivity) (by linarith [Real.log_nonneg hnR]))]`. Establish `hlog : (fun n : ℕ => 1 + Real.log n) =o[atTop] fun n : ℕ => (n : ℝ)`. Establish `h1` using `(isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop`. Establish `h2` using `Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop`. Conclude with `h1.add h2`.

Establish `ho : (fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n)) =o[atTop] pw D`. Use `(isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO hlog` as an intermediate fact. Use `this.congr_right fun n => ?_` and prove the remaining obligations. Simplify using `[pw, pow_succ]`. Conclude with `hO.trans_isLittleO ho`.
-/
theorem BlockMeasureChange.proof (hS : SupBoundBlock.Statement) : BlockMeasureChange.Statement := by
  intro D K _ _ ι _ Ω _ _ d d' hy hk hA
  obtain ⟨C, hC, hsup⟩ := sup_one_le hS d
  obtain ⟨C', hC', hsup'⟩ := sup_one_le hS d'
  set L := max C C' with hL
  have hL1 : 1 ≤ L := hC.trans (le_max_left _ _)

  have key : ∀ n : ℕ, 1 ≤ n → |blockChi d' n - blockChi d n| ≤
      (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
    intro n hn
    have hex := exists_isSecBasisM d.y d.k₀ n
    have hb := hex.choose_spec
    choose f hf hfe using hb.1
    have hbf : hex.choose.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfe
    have hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
    have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
      have := hb.2.1
      simp only [hbf, aeval_map_int] at this
      exact this
    have hli' : LinearIndependent ℤ fun k => aeval d'.y (f k) := by rw [hy]; exact hli
    have hsame : ∀ (y' : (Σ k, ι k) → Ω) (k' : K), y' = d.y → k' = d.k₀ →
        ∀ h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y' k' n p.2,
          h.choose = hex.choose := by
      rintro _ _ rfl rfl h; rfl
    have hex' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d'.y d'.k₀ n p.2 := by
      rw [hy, hk]; exact hex
    have e1 : blockChi d n = -(1 / 2) *
        Real.log (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dif_pos hex, hbf]
    have e2 : blockChi d' n = -(1 / 2) *
        Real.log (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dif_pos hex', hsame _ _ hy hk hex', hbf]
    set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))
    set G' := blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s := (n : ℝ) ^ ((D : ℝ) / 2) with hs
    have hs1 : 1 ≤ s := Real.one_le_rpow hnR (by positivity)
    have hs2 : s ^ 2 = (n : ℝ) ^ D := by
      rw [hs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1
      ring
    have hlogs : Real.log s = (D / 2) * Real.log n := by
      rw [hs, Real.log_rpow (by positivity)]
    set c := C * s
    set c' := C' * s
    have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le hC hs1
    have hc' : 1 ≤ c' := one_le_mul_of_one_le_of_one_le hC' hs1
    have hG : G.PosDef := gram_posDef d n f hf hli (by linarith) (hsup n hn)
    have hG' : G'.PosDef := gram_posDef d' n f hf' hli' (by linarith) (hsup' n hn)
    have q1 := quad_le d d' hy hk hA n f hf (by linarith) (hsup n hn)
    have q2 := quad_le d' d hy.symm hk.symm hA.symm n f hf' (by linarith) (hsup' n hn)
    have d1 := det_le hG.isHermitian hG'.posSemidef q1
    have d2 := det_le hG'.isHermitian hG.posSemidef q2
    have hr := SupBoundCount.rank_le d n f hf hli (by linarith) (hsup n hn)
    have p1 := hG.det_pos
    have p2 := hG'.det_pos
    have l1 : Real.log G'.det ≤ hex.choose.1 * Real.log (c ^ 2) + Real.log G.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p1.ne']
      exact Real.log_le_log p2 d1
    have l2 : Real.log G.det ≤ hex.choose.1 * Real.log (c' ^ 2) + Real.log G'.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p2.ne']
      exact Real.log_le_log p1 d2
    have lc : Real.log c ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_left C C')
      nlinarith
    have lc' : Real.log c' ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_right C C')
      nlinarith
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hlc' : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hr0 : (0 : ℝ) ≤ (hex.choose.1 : ℝ) := Nat.cast_nonneg _
    have hrb : (hex.choose.1 : ℝ) ≤ 2 * L ^ 2 * (n : ℝ) ^ D := by
      have : c ^ 2 ≤ L ^ 2 * (n : ℝ) ^ D := by
        rw [mul_pow, hs2]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) 2) (by positivity)
      linarith
    rw [Real.log_pow] at l1 l2
    push_cast at l1 l2
    have hdiff : |blockChi d' n - blockChi d n| ≤ hex.choose.1 * (Real.log L + D * Real.log n) := by
      have m1 := mul_le_mul_of_nonneg_left lc hr0
      have m2 := mul_le_mul_of_nonneg_left lc' hr0
      rw [e1, e2, abs_le]
      constructor <;> linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hnD : 0 ≤ (n : ℝ) ^ D := by positivity
    refine hdiff.trans ?_
    calc (hex.choose.1 : ℝ) * (Real.log L + D * Real.log n)
        ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n) :=
          mul_le_mul_of_nonneg_right hrb (by positivity)
      _ ≤ (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
          have : Real.log L + D * Real.log n ≤ (Real.log L + D) * (1 + Real.log n) := by
            have h3 : 0 ≤ Real.log L * Real.log n := mul_nonneg hlL hln
            have h4 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
            have e : (Real.log L + D) * (1 + Real.log n) =
                Real.log L + D * Real.log n + (D + Real.log L * Real.log n) := by ring
            rw [e]
            linarith
          calc (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n)
              ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * ((Real.log L + D) * (1 + Real.log n)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring

  have hO : (fun n : ℕ => blockChi d' n - blockChi d n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n) := by
    refine IsBigO.of_bound (2 * L ^ 2 * (Real.log L + D)) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (key n hn).trans (le_of_eq ?_)
    congr 1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith [Real.log_nonneg hnR]))]
  have hlog : (fun n : ℕ => 1 + Real.log n) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have h1 := (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
    have h2 := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
    exact h1.add h2
  have ho : (fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n)) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO hlog
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact hO.trans_isLittleO ho

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
