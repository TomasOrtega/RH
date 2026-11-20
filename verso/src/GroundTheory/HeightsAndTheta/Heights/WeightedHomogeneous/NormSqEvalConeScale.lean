import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace ChartMetric

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : (fun z : Cone n ℂ ↦ evalCone z (C a)) = fun _ ↦ (a : ℂ)`. Use function extensionality and compare the values at `z`. Unfold `evalCone`.

Rewrite using `[eval₂_C]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `contDiff_const`. Consider the case `add p q hp hq`.

Establish `h : (fun z : Cone n ℂ ↦ evalCone z (p + q)) = fun z ↦ evalCone z p + evalCone z q`. Use function extensionality and compare the values at `z`. Simplify using `[evalCone, eval₂_add]`. Rewrite using `[h]`. Conclude with `hp.add hq`.

Consider the case `mul_X p v hp`. Establish `h : (fun z : Cone n ℂ ↦ evalCone z (p * X v)) = fun z ↦ evalCone z p * z v.1 v.2`. Use function extensionality and compare the values at `z`. Simplify using `[evalCone, eval₂_mul, eval₂_X]`. Establish `hv : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ z v.1 v.2)` using `((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n v.1 + 1) ↦ ℂ) v.2).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) v.1)).contDiff`.

Rewrite using `[h]`. Conclude with `hp.mul hv`.
-/
theorem contDiff_evalCone {ι : Type} [Fintype ι] {n : ι → ℕ} (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (C a)) = fun _ ↦ (a : ℂ) := by
      funext z; unfold evalCone; rw [eval₂_C]; simp
    rw [h]; exact contDiff_const
  | add p q hp hq =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (p + q)) = fun z ↦ evalCone z p + evalCone z q := by
      funext z; simp [evalCone, eval₂_add]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun z : Cone n ℂ ↦ evalCone z (p * X v)) = fun z ↦ evalCone z p * z v.1 v.2 := by
      funext z; simp [evalCone, eval₂_mul, eval₂_X]
    have hv : ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ z v.1 v.2) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n v.1 + 1) ↦ ℂ) v.2).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun k ↦ Fin (n k + 1) → ℂ) v.1)).contDiff
    rw [h]; exact hp.mul hv

/- English proof (translation)
Establish `h : evalCone (fun k i ↦ t k * z k i) f = (∏ k, t k ^ δ k) * evalCone z f` using `eval₂_scale_of_isWeightedHomogeneous t (fun v ↦ z v.1 v.2) hf`. Rewrite using `[h, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_pow, ← pow_mul, ← zpow_natCast]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_evalCone_scale {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    ‖evalCone (fun k i ↦ t k * z k i) f‖ ^ 2 = (∏ k, ‖t k‖ ^ (2 * (δ k : ℤ))) * ‖evalCone z f‖ ^ 2 := by
  have h : evalCone (fun k i ↦ t k * z k i) f = (∏ k, t k ^ δ k) * evalCone z f :=
    eval₂_scale_of_isWeightedHomogeneous t (fun v ↦ z v.1 v.2) hf
  rw [h, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [norm_pow, ← pow_mul, ← zpow_natCast]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ ↦ norm_sq_evalCone_scale t z (isWeightedHomogeneous_chartMonomial c d)`.
-/
theorem chartSum_scale {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (t : ι → ℂ) (z : Cone n ℂ) (d : ι → ℕ) :
    ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (fun k i ↦ t k * z k i) (chartMonomial c d)‖ ^ 2 =
      (∏ k, ‖t k‖ ^ (2 * (d k : ℤ))) * ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦
    norm_sq_evalCone_scale t z (isWeightedHomogeneous_chartMonomial c d)

/- English proof (translation)
Use `choose c hc using fun k ↦ Function.ne_iff.mp (hz k)`. Establish `h0 : evalCone z (chartMonomial c d) ≠ 0`. Rewrite using `[evalCone_chartMonomial]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)`. Conclude with `lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h0) 2) (Finset.single_le_sum (f := fun c ↦ ‖evalCone z (chartMonomial c d)‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ c))`.
-/
theorem chartSum_pos {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {z : Cone n ℂ}
    (hz : BlockNonzero z) (d : ι → ℕ) :
    0 < ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
  choose c hc using fun k ↦ Function.ne_iff.mp (hz k)
  have h0 : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h0) 2)
    (Finset.single_le_sum (f := fun c ↦ ‖evalCone z (chartMonomial c d)‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ c))

/- English proof (translation)
Establish `ht' : ∀ k, ‖t k‖ ≠ 0` using `fun k ↦ norm_ne_zero_iff.mpr (ht k)`. Unfold `AddBlockData.den`. Rewrite using `[mul_add, Finset.mul_sum, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Take `⟨e, he, hed⟩` from `hg.homog c j`. Rewrite using `[norm_sq_evalCone_scale t z he]`. Simplify using `only [hed]`.

Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_sq_evalCone_scale t z (hG.homog i)]`. Establish `hl : ∀ k, l2Norm (fun j ↦ t k * z k j) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) = ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) * l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k))` using `fun k ↦ by rw [vectorL2Norm_const_mul, mul_zpow]`. Simplify using `only [hl, Finset.prod_mul_distrib]`. Establish `hs : (∏ k, ‖t k‖ ^ (2 * (δ i k : ℤ))) * ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) = ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k))`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (ht' k)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem den_scale {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
    (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ) (t : ι → ℂ) (ht : ∀ k, t k ≠ 0) (z : Cone n ℂ) :
    D.den d g G δ (fun k i ↦ t k * z k i) =
      (∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k))) * D.den d g G δ z := by
  have ht' : ∀ k, ‖t k‖ ≠ 0 := fun k ↦ norm_ne_zero_iff.mpr (ht k)
  unfold AddBlockData.den
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    obtain ⟨e, he, hed⟩ := hg.homog c j
    rw [norm_sq_evalCone_scale t z he]
    simp only [hed]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_sq_evalCone_scale t z (hG.homog i)]
    have hl : ∀ k, l2Norm (fun j ↦ t k * z k j) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) =
        ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) * l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) :=
      fun k ↦ by rw [vectorL2Norm_const_mul, mul_zpow]
    simp only [hl, Finset.prod_mul_distrib]
    have hs : (∏ k, ‖t k‖ ^ (2 * (δ i k : ℤ))) * ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) =
        ∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_add₀ (ht' k)]
      congr 1
      ring
    rw [← hs]
    ring

/- English proof (translation)
Establish `e : B * S / (B * A ^ 2 * Den) = S / Den / A ^ 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, Real.sqrt_div' _ (sq_nonneg A), Real.sqrt_sq hA.le]`. Clear the denominators using the available nonvanishing facts.
-/
theorem scale_alg (A B h s L S Den : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < Den) :
    A * h * (s * L) * Real.sqrt (B * S / (B * A ^ 2 * Den)) = s * (h * L * Real.sqrt (S / Den)) := by
  have e : B * S / (B * A ^ 2 * Den) = S / Den / A ^ 2 := by
    field_simp
  rw [e, Real.sqrt_div' _ (sq_nonneg A), Real.sqrt_sq hA.le]
  field_simp

/- English proof (translation)
Introduce `ι _ _ n P D N hN d g hg r G δ hG`. Establish `hDen'` using `hDen ι n P D d g hg r G δ hG`. Establish `hold : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ))` using `contDiff_pi.2 fun k ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) (some k)).contDiff`. Establish `hmaps : Set.MapsTo (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ)) {w | BlockNonzero w} {z | BlockNonzero z}` using `fun w hw k ↦ hw (some k)`. Use `⟨⟨HermLine.mk (n := D.extSizes) AddBlockData.newDeg (D.plusMetric N d g G δ) ?pos ?smul ?smooth, rfl, fun w _ ↦ rfl, ?conj⟩, ?pts⟩` and prove the remaining obligations.

Use `case pos =>`. Introduce `w hw`. Establish `hz : BlockNonzero (D.basePart₂ w)` using `fun k ↦ hw (some k)`. Unfold `AddBlockData.plusMetric`. Conclude with `mul_pos (mul_pos (N.metric_pos _ hz) (vectorL2Norm_pos (hw none))) (Real.sqrt_pos.mpr (div_pos (chartSum_pos hz d) (hDen'.1 _ hz)))`.

Use `case smul =>`. Introduce `t w ht hw`. Establish `hz : BlockNonzero (D.basePart₂ w)` using `fun k ↦ hw (some k)`. Establish `ht' : ∀ k, t (some k) ≠ 0` using `fun k ↦ ht (some k)`. Establish `hpos : ∀ k, 0 < ‖t (some k)‖` using `fun k ↦ norm_pos_iff.mpr (ht' k)`.

Establish `hdeg : ∏ o, ‖t o‖ ^ AddBlockData.newDeg o = ‖t none‖`. Rewrite using `[Fintype.prod_option]`. Simplify using `[AddBlockData.newDeg]`. Establish `hm` using `N.metric_smul (fun k ↦ t (some k)) (D.basePart₂ w) ht' hz`. Establish `hs` using `chartSum_scale (fun k ↦ t (some k)) (D.basePart₂ w) d`.

Establish `hd` using `den_scale D hg hG (fun k ↦ t (some k)) ht' (D.basePart₂ w)`. Use `beta_reduce at hm hs hd`. Establish `hC : ∏ k, ‖t (some k)‖ ^ (2 * ((d k : ℤ) + D.deg k)) = (∏ k, ‖t (some k)‖ ^ (2 * (d k : ℤ))) * (∏ k, ‖t (some k)‖ ^ D.deg k) ^ 2`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hpos k).ne']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show D.plusMetric N d g G δ (fun o i ↦ t o * w o i) = (∏ o, ‖t o‖ ^ AddBlockData.newDeg o) * D.plusMetric N d g G δ w`.

Establish `eold : D.basePart₂ (fun o i ↦ t o * w o i) = fun k i ↦ t (some k) * D.basePart₂ w k i` using `rfl`. Establish `enew : D.newPart (fun o i ↦ t o * w o i) = fun i ↦ t none * D.newPart w i` using `rfl`. Unfold `AddBlockData.plusMetric`. Rewrite using `[eold, enew, hdeg, hm, vectorL2Norm_const_mul, hs, hd, hC, hN]`. Conclude with `scale_alg _ _ _ _ _ _ _ (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _) (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _) (hDen'.1 _ hz)`.

Use `case smooth =>`. Establish `h1 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ N.metric (D.basePart₂ w)) {w | BlockNonzero w}` using `N.metric_smooth.comp hold.contDiffOn hmaps`. Establish `h2 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ l2Norm (D.newPart w)) {w | BlockNonzero w}` using `contDiffOn_l2Norm_block (n := D.extSizes) none`. Establish `hS : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2)` using `ContDiff.sum fun c _ ↦ (contDiff_norm_sq ℝ).comp ((contDiff_evalCone _).comp hold)`. Establish `hDn : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ D.den d g G δ (D.basePart₂ w)) {w | BlockNonzero w}` using `hDen'.2.comp hold.contDiffOn hmaps`.

Establish `h3` using `(hS.contDiffOn.div hDn fun w hw ↦ (hDen'.1 _ (hmaps hw)).ne').sqrt fun w hw ↦ (div_pos (chartSum_pos (hmaps hw) d) (hDen'.1 _ (hmaps hw))).ne'`. Conclude with `(h1.mul h2).mul h3`. Use `case conj =>`. Introduce `hNc w hw`. Establish `hz : BlockNonzero (D.basePart₂ w)` using `fun k ↦ hw (some k)`.

Establish `hN' : N.metric (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = N.metric (D.basePart₂ w)` using `hNc _ hz`. Establish `hev : ∀ f : MvPolynomial (Coord n) ℤ, evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) f = starRingEnd ℂ (evalCone (D.basePart₂ w) f)` using `fun f ↦ evalCone_map (starRingEnd ℂ) (D.basePart₂ w) f`. Establish `hS : ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) (chartMonomial c d)‖ ^ 2 = ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2`. Simplify using `only [hev, Complex.norm_conj]`. Establish `hD : D.den d g G δ (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = D.den d g G δ (D.basePart₂ w)`.

Unfold `AddBlockData.den`. Simplify using `only [hev, Complex.norm_conj, vectorL2Norm_conj]`. Establish `eold : D.basePart₂ (fun o i ↦ starRingEnd ℂ (w o i)) = fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)` using `rfl`. Establish `enew : D.newPart (fun o i ↦ starRingEnd ℂ (w o i)) = fun i ↦ starRingEnd ℂ (D.newPart w i)` using `rfl`. Use `show D.plusMetric N d g G δ (fun o i ↦ starRingEnd ℂ (w o i)) = D.plusMetric N d g G δ w`.

Unfold `AddBlockData.plusMetric`. Rewrite using `[eold, enew, vectorL2Norm_conj, hN', hS, hD]`. Use `case pts =>`. Introduce `w hw c la hm hz'`. Take `⟨hzP, -⟩` from `(hPts ι n P D d g hg).2 w hw`.

Establish `hG0 : ∀ i, evalCone (D.basePart₂ w) (G i) = 0` using `fun i ↦ hzP.2 _ (by rw [← hG.span_eq]; exact Ideal.subset_span ⟨i, rfl⟩)`. Establish `hcr : ∀ c' j, evalCone (D.basePart₂ w) (chartMonomial c' d) * evalCone (D.basePart₂ w) (g c j) = evalCone (D.basePart₂ w) (chartMonomial c d) * evalCone (D.basePart₂ w) (g c' j)`. Introduce `c' j`. Establish `h` using `hzP.2 _ (hCross ι n P D d g hg c c' j)`. Unfold `evalCone at h ⊢`.

Rewrite `h` using `[eval₂_sub, eval₂_mul, eval₂_mul, sub_eq_zero]`. Conclude with `h`. Establish `hla : ∀ c' j, D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c' d) = la * evalCone (D.basePart₂ w) (g c' j)`. Introduce `c' j`. Rewrite using `[hz' j, div_mul_eq_mul_div, div_eq_iff hm, mul_assoc, mul_comm (evalCone _ (g c j)), hcr c' j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hl2 : l2Norm (D.newPart w) ^ 2 = ∑ j, ‖D.newPart w j‖ ^ 2` using `Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)`. Establish `hden : D.den d g G δ (D.basePart₂ w) = ∑ c', ∑ j, ‖evalCone (D.basePart₂ w) (g c' j)‖ ^ 2`. Simplify using `[AddBlockData.den, hG0]`. Establish `key : l2Norm (D.newPart w) ^ 2 * ∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2 = ‖la‖ ^ 2 * D.den d g G δ (D.basePart₂ w)`.

Rewrite using `[hl2, hden, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c' _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Establish `e` using `congrArg (fun x : ℂ ↦ ‖x‖ ^ 2) (hla c' j)`.

Simplify using `only [norm_mul, mul_pow] at e`. Conclude with `e`. Establish `hDpos : 0 < D.den d g G δ (D.basePart₂ w)` using `hDen'.1 _ hzP.1`. Establish `hL : 0 ≤ l2Norm (D.newPart w)` using `Real.sqrt_nonneg _`. Establish `e : l2Norm (D.newPart w) * Real.sqrt ((∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2) / D.den d g G δ (D.basePart₂ w)) = ‖la‖`.

Rewrite using `[← Real.sqrt_sq hL, ← Real.sqrt_mul (sq_nonneg _), ← mul_div_assoc, key, mul_div_assoc, div_self hDpos.ne', mul_one, Real.sqrt_sq (norm_nonneg _)]`. Unfold `AddBlockData.plusMetric`. Rewrite using `[mul_assoc, e, mul_comm]`.
-/
theorem proof (hDen : ChartDenominatorAlt.Statement) (hPts : ConePoints.Statement) (hCross : ChartCrossRatio.Statement) :
    ChartMetric.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG
  have hDen' := hDen ι n P D d g hg r G δ hG
  have hold : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ)) :=
    contDiff_pi.2 fun k ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun o ↦ Fin (D.extSizes o + 1) → ℂ) (some k)).contDiff
  have hmaps : Set.MapsTo (fun w : Cone D.extSizes ℂ ↦ (D.basePart₂ w : Cone n ℂ))
      {w | BlockNonzero w} {z | BlockNonzero z} := fun w hw k ↦ hw (some k)
  refine ⟨⟨HermLine.mk (n := D.extSizes) AddBlockData.newDeg (D.plusMetric N d g G δ) ?pos ?smul ?smooth, rfl, fun w _ ↦ rfl, ?conj⟩, ?pts⟩
  case pos =>
    intro w hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    unfold AddBlockData.plusMetric
    exact mul_pos (mul_pos (N.metric_pos _ hz) (vectorL2Norm_pos (hw none)))
      (Real.sqrt_pos.mpr (div_pos (chartSum_pos hz d) (hDen'.1 _ hz)))
  case smul =>
    intro t w ht hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    have ht' : ∀ k, t (some k) ≠ 0 := fun k ↦ ht (some k)
    have hpos : ∀ k, 0 < ‖t (some k)‖ := fun k ↦ norm_pos_iff.mpr (ht' k)
    have hdeg : ∏ o, ‖t o‖ ^ AddBlockData.newDeg o = ‖t none‖ := by
      rw [Fintype.prod_option]
      simp [AddBlockData.newDeg]
    have hm := N.metric_smul (fun k ↦ t (some k)) (D.basePart₂ w) ht' hz
    have hs := chartSum_scale (fun k ↦ t (some k)) (D.basePart₂ w) d
    have hd := den_scale D hg hG (fun k ↦ t (some k)) ht' (D.basePart₂ w)
    beta_reduce at hm hs hd
    have hC : ∏ k, ‖t (some k)‖ ^ (2 * ((d k : ℤ) + D.deg k)) =
        (∏ k, ‖t (some k)‖ ^ (2 * (d k : ℤ))) * (∏ k, ‖t (some k)‖ ^ D.deg k) ^ 2 := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hpos k).ne']
      congr 1
      push_cast
      ring
    show D.plusMetric N d g G δ (fun o i ↦ t o * w o i) =
      (∏ o, ‖t o‖ ^ AddBlockData.newDeg o) * D.plusMetric N d g G δ w
    have eold : D.basePart₂ (fun o i ↦ t o * w o i) = fun k i ↦ t (some k) * D.basePart₂ w k i := rfl
    have enew : D.newPart (fun o i ↦ t o * w o i) = fun i ↦ t none * D.newPart w i := rfl
    unfold AddBlockData.plusMetric
    rw [eold, enew, hdeg, hm, vectorL2Norm_const_mul, hs, hd, hC, hN]
    exact scale_alg _ _ _ _ _ _ _ (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _)
      (Finset.prod_pos fun k _ ↦ zpow_pos (hpos k) _) (hDen'.1 _ hz)
  case smooth =>
    have h1 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ N.metric (D.basePart₂ w)) {w | BlockNonzero w} :=
      N.metric_smooth.comp hold.contDiffOn hmaps
    have h2 : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ l2Norm (D.newPart w)) {w | BlockNonzero w} :=
      contDiffOn_l2Norm_block (n := D.extSizes) none
    have hS : ContDiff ℝ ∞ (fun w : Cone D.extSizes ℂ ↦
        ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2) :=
      ContDiff.sum fun c _ ↦ (contDiff_norm_sq ℝ).comp ((contDiff_evalCone _).comp hold)
    have hDn : ContDiffOn ℝ ∞ (fun w : Cone D.extSizes ℂ ↦ D.den d g G δ (D.basePart₂ w)) {w | BlockNonzero w} :=
      hDen'.2.comp hold.contDiffOn hmaps
    have h3 := (hS.contDiffOn.div hDn fun w hw ↦ (hDen'.1 _ (hmaps hw)).ne').sqrt fun w hw ↦
      (div_pos (chartSum_pos (hmaps hw) d) (hDen'.1 _ (hmaps hw))).ne'
    exact (h1.mul h2).mul h3
  case conj =>
    intro hNc w hw
    have hz : BlockNonzero (D.basePart₂ w) := fun k ↦ hw (some k)
    have hN' : N.metric (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = N.metric (D.basePart₂ w) := hNc _ hz
    have hev : ∀ f : MvPolynomial (Coord n) ℤ, evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) f =
        starRingEnd ℂ (evalCone (D.basePart₂ w) f) :=
      fun f ↦ evalCone_map (starRingEnd ℂ) (D.basePart₂ w) f
    have hS : ∑ c : (k : ι) → Fin (n k + 1),
        ‖evalCone (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) (chartMonomial c d)‖ ^ 2 =
        ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone (D.basePart₂ w) (chartMonomial c d)‖ ^ 2 := by
      simp only [hev, Complex.norm_conj]
    have hD : D.den d g G δ (fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i)) = D.den d g G δ (D.basePart₂ w) := by
      unfold AddBlockData.den
      simp only [hev, Complex.norm_conj, vectorL2Norm_conj]
    have eold : D.basePart₂ (fun o i ↦ starRingEnd ℂ (w o i)) = fun k i ↦ starRingEnd ℂ (D.basePart₂ w k i) := rfl
    have enew : D.newPart (fun o i ↦ starRingEnd ℂ (w o i)) = fun i ↦ starRingEnd ℂ (D.newPart w i) := rfl
    show D.plusMetric N d g G δ (fun o i ↦ starRingEnd ℂ (w o i)) = D.plusMetric N d g G δ w
    unfold AddBlockData.plusMetric
    rw [eold, enew, vectorL2Norm_conj, hN', hS, hD]
  case pts =>
    intro w hw c la hm hz'
    obtain ⟨hzP, -⟩ := (hPts ι n P D d g hg).2 w hw
    have hG0 : ∀ i, evalCone (D.basePart₂ w) (G i) = 0 := fun i ↦
      hzP.2 _ (by rw [← hG.span_eq]; exact Ideal.subset_span ⟨i, rfl⟩)
    have hcr : ∀ c' j, evalCone (D.basePart₂ w) (chartMonomial c' d) * evalCone (D.basePart₂ w) (g c j) =
        evalCone (D.basePart₂ w) (chartMonomial c d) * evalCone (D.basePart₂ w) (g c' j) := by
      intro c' j
      have h := hzP.2 _ (hCross ι n P D d g hg c c' j)
      unfold evalCone at h ⊢
      rw [eval₂_sub, eval₂_mul, eval₂_mul, sub_eq_zero] at h
      exact h
    have hla : ∀ c' j, D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c' d) =
        la * evalCone (D.basePart₂ w) (g c' j) := by
      intro c' j
      rw [hz' j, div_mul_eq_mul_div, div_eq_iff hm, mul_assoc, mul_comm (evalCone _ (g c j)), hcr c' j]
      ring
    have hl2 : l2Norm (D.newPart w) ^ 2 = ∑ j, ‖D.newPart w j‖ ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    have hden : D.den d g G δ (D.basePart₂ w) = ∑ c', ∑ j, ‖evalCone (D.basePart₂ w) (g c' j)‖ ^ 2 := by
      simp [AddBlockData.den, hG0]
    have key : l2Norm (D.newPart w) ^ 2 * ∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2 =
        ‖la‖ ^ 2 * D.den d g G δ (D.basePart₂ w) := by
      rw [hl2, hden, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ ↦ ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have e := congrArg (fun x : ℂ ↦ ‖x‖ ^ 2) (hla c' j)
      simp only [norm_mul, mul_pow] at e
      exact e
    have hDpos : 0 < D.den d g G δ (D.basePart₂ w) := hDen'.1 _ hzP.1
    have hL : 0 ≤ l2Norm (D.newPart w) := Real.sqrt_nonneg _
    have e : l2Norm (D.newPart w) *
        Real.sqrt ((∑ c', ‖evalCone (D.basePart₂ w) (chartMonomial c' d)‖ ^ 2) / D.den d g G δ (D.basePart₂ w)) =
        ‖la‖ := by
      rw [← Real.sqrt_sq hL, ← Real.sqrt_mul (sq_nonneg _), ← mul_div_assoc, key, mul_div_assoc,
        div_self hDpos.ne', mul_one, Real.sqrt_sq (norm_nonneg _)]
    unfold AddBlockData.plusMetric
    rw [mul_assoc, e, mul_comm]

end ChartMetric

end

end GroundTheory.Heights₂.Heights
