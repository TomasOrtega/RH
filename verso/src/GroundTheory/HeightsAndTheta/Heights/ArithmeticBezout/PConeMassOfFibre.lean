import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibreAverage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

def coordPlaneSubst (m k : ℕ) : Fin (m + k) → MvPolynomial (Fin m) ℂ :=
  Fin.append (fun i => X i) (fun _ => 0)

def coordPlaneIdeal (m k : ℕ) : Ideal (MvPolynomial (Fin (m + k)) ℂ) :=
  RingHom.ker (aeval (coordPlaneSubst m k))

/- English proof (translation)
Establish `hg : ∀ i, (coordPlaneSubst m k i).IsHomogeneous 1`. Introduce `i`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `only [coordPlaneSubst, Fin.append_left]`. Conclude with `isHomogeneous_X ℂ i`.

Simplify using `only [coordPlaneSubst, Fin.append_right]`. Conclude with `isHomogeneous_zero _ _ _`. Establish `hterm : ∀ e, homogeneousComponent d (aeval (coordPlaneSubst m k) (homogeneousComponent e f)) = if e = d then aeval (coordPlaneSubst m k) (homogeneousComponent e f) else 0`. Introduce `e`. Establish `he` using `(homogeneousComponent_isHomogeneous e f).aeval _ hg`.

Rewrite `he` using `[one_mul]`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 he)]`. Conclude with `if_congr eq_comm rfl rfl`. Use `conv_lhs => rw [← sum_homogeneousComponent f]`. Rewrite using `[map_sum, map_sum]`.

Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hd`. Both sides reduce to the same expression. Rewrite `hd` using `[Finset.mem_range, not_lt]`.

Rewrite using `[homogeneousComponent_eq_zero _ _ (by omega), map_zero]`.
-/
theorem homogeneousComponent_aeval_coordPlaneSubst (m k d : ℕ) (f : MvPolynomial (Fin (m + k)) ℂ) :
    homogeneousComponent d (aeval (coordPlaneSubst m k) f) =
      aeval (coordPlaneSubst m k) (homogeneousComponent d f) := by
  have hg : ∀ i, (coordPlaneSubst m k i).IsHomogeneous 1 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [coordPlaneSubst, Fin.append_left]
      exact isHomogeneous_X ℂ i
    · simp only [coordPlaneSubst, Fin.append_right]
      exact isHomogeneous_zero _ _ _
  have hterm : ∀ e, homogeneousComponent d (aeval (coordPlaneSubst m k) (homogeneousComponent e f)) =
      if e = d then aeval (coordPlaneSubst m k) (homogeneousComponent e f) else 0 := by
    intro e
    have he := (homogeneousComponent_isHomogeneous e f).aeval _ hg
    rw [one_mul] at he
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 he)]
    exact if_congr eq_comm rfl rfl
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [Finset.mem_range, not_lt] at hd
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

/- English proof (translation)
The claim follows from `RingHom.ker_isPrime _ isHomog f hf d := by rw [coordPlaneIdeal, RingHom.mem_ker] at hf ⊢ rw [← homogeneousComponent_aeval_coordPlaneSubst, hf, map_zero] isRelevant := ⟨Fin.castAdd k ⟨0, hm⟩, by rw [coordPlaneIdeal, RingHom.mem_ker, aeval_X, coordPlaneSubst, Fin.append_left] exact …`.
-/
theorem isProjPrime_coordPlaneIdeal {m : ℕ} (hm : 0 < m) (k : ℕ) :
    IsProjPrime (coordPlaneIdeal m k) where
  isPrime := RingHom.ker_isPrime _
  isHomog f hf d := by
    rw [coordPlaneIdeal, RingHom.mem_ker] at hf ⊢
    rw [← homogeneousComponent_aeval_coordPlaneSubst, hf, map_zero]
  isRelevant := ⟨Fin.castAdd k ⟨0, hm⟩, by
    rw [coordPlaneIdeal, RingHom.mem_ker, aeval_X, coordPlaneSubst, Fin.append_left]
    exact X_ne_zero _⟩

/- English proof (translation)
Simplify using `[HermNorm.pointOf, HermNorm.std]`.
-/
theorem pointOf_std {n : ℕ} (y : EuclideanSpace ℂ (Fin n)) :
    (HermNorm.std n).pointOf y = fun i => y i := by
  simp [HermNorm.pointOf, HermNorm.std]

/- English proof (translation)
Simplify using `only [coneSet, Set.mem_ofPred_eq, pointOf_std]`. Prove the components needed by the constructor for the conclusion. Introduce `hy j hj`. Take `⟨i, rfl⟩ : ∃ i : Fin k, j = Fin.natAdd m i` from `⟨⟨j - m, by omega⟩, by ext; simp; omega⟩`. Establish `hX : (X (Fin.natAdd m i) : MvPolynomial (Fin (m + k)) ℂ) ∈ coordPlaneIdeal m k`.

Rewrite using `[coordPlaneIdeal, RingHom.mem_ker, aeval_X, coordPlaneSubst, Fin.append_right]`. Simplify using `using hy _ hX`. Introduce `hy q hq`. Rewrite `hq` using `[coordPlaneIdeal, RingHom.mem_ker]`. Use `set x : Fin m → ℂ := fun i => y (Fin.castAdd k i)`.

Establish `hyx : (fun i => y i) = fun j => eval x (coordPlaneSubst m k j)`. Use function extensionality and compare the values at `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify using `[coordPlaneSubst, x]`. Simplify using `[coordPlaneSubst, hy (Fin.natAdd m i) (by simp)]`.

Establish `hev : eval (fun j => eval x (coordPlaneSubst m k j)) q = eval x (aeval (coordPlaneSubst m k) q)`. Rewrite using `[← coe_aeval_eq_eval, ← coe_aeval_eq_eval, aeval_eq_bind₁]`. Conclude with `(aeval_bind₁ x (coordPlaneSubst m k) q).symm`. Rewrite using `[hyx, hev, hq, map_zero]`.
-/
theorem mem_coneSet_coordPlaneIdeal {m k : ℕ} (y : EuclideanSpace ℂ (Fin (m + k))) :
    y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k) ↔
      ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0 := by
  simp only [coneSet, Set.mem_ofPred_eq, pointOf_std]
  constructor
  · intro hy j hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin k, j = Fin.natAdd m i :=
      ⟨⟨j - m, by omega⟩, by ext; simp; omega⟩
    have hX : (X (Fin.natAdd m i) : MvPolynomial (Fin (m + k)) ℂ) ∈ coordPlaneIdeal m k := by
      rw [coordPlaneIdeal, RingHom.mem_ker, aeval_X, coordPlaneSubst, Fin.append_right]
    simpa using hy _ hX
  · intro hy q hq
    rw [coordPlaneIdeal, RingHom.mem_ker] at hq
    set x : Fin m → ℂ := fun i => y (Fin.castAdd k i)
    have hyx : (fun i => y i) = fun j => eval x (coordPlaneSubst m k j) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [coordPlaneSubst, x]
      · simp [coordPlaneSubst, hy (Fin.natAdd m i) (by simp)]
    have hev : eval (fun j => eval x (coordPlaneSubst m k j)) q =
        eval x (aeval (coordPlaneSubst m k) q) := by
      rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval, aeval_eq_bind₁]
      exact (aeval_bind₁ x (coordPlaneSubst m k) q).symm
    rw [hyx, hev, hq, map_zero]

/- English proof (translation)
Use extensionality with `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Simplify using `[zeroExt]`. Simplify using `[zeroExt, hy (Fin.natAdd m i) (by simp)]`.
-/
theorem eq_zeroExt_of {m k : ℕ} {y : EuclideanSpace ℂ (Fin (m + k))}
    (hy : ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0) :
    y = zeroExt m k (WithLp.toLp 2 fun i => y (Fin.castAdd k i)) := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [zeroExt]
  · simp [zeroExt, hy (Fin.natAdd m i) (by simp)]

/- English proof (translation)
Use `revert hj`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Introduce `hi`. Simplify using `at hi`. Use linear arithmetic over natural numbers and integers.

Introduce `_`. Simplify using `[zeroExt]`.
-/
theorem zeroExt_apply_of_le {m k : ℕ} (x : EuclideanSpace ℂ (Fin m)) (j : Fin (m + k))
    (hj : m ≤ (j : ℕ)) : zeroExt m k x j = 0 := by
  revert hj
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · intro hi
    simp at hi
    omega
  · intro _
    simp [zeroExt]

def coordPlaneBlock {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => π i (Fin.castAdd k j)

/- English proof (translation)
Use extensionality with `i`. Simplify using `[linProj, zeroExt, Fin.sum_univ_add, coordPlaneBlock, Matrix.mulVec, dotProduct]`.
-/
theorem linProj_zeroExt {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) (x : EuclideanSpace ℂ (Fin m)) :
    linProj π (zeroExt m k x) = WithLp.toLp 2 ((coordPlaneBlock π).mulVec fun i => x i) := by
  ext i
  simp [linProj, zeroExt, Fin.sum_univ_add, coordPlaneBlock, Matrix.mulVec, dotProduct]

/- English proof (translation)
Establish `hB : IsUnit (coordPlaneBlock π).det` using `Ne.isUnit hπ`. Use `set x₀ : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 ((coordPlaneBlock π)⁻¹.mulVec fun i => w i)`. Establish `hfib : {y | y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k) ∧ linProj π y = w} = {zeroExt m k x₀}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff, mem_coneSet_coordPlaneIdeal]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hπy⟩`. Rewrite `hπy`, the goal using `[eq_zeroExt_of hy]`. Use `congr 1`. Rewrite `hπy` using `[linProj_zeroExt]`.

Establish `h2` using `congrArg (fun v : EuclideanSpace ℂ (Fin m) => (coordPlaneBlock π)⁻¹.mulVec fun i => v i) hπy`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec] at h2`. Use extensionality with `i`. Simplify using `only [x₀]`. Rewrite using `[← h2]`.

Introduce and unpack `rfl`. Use `⟨zeroExt_apply_of_le x₀, ?_⟩` and prove the remaining obligations. Rewrite using `[linProj_zeroExt]`. Use extensionality with `i`. Simplify using `[x₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB]`.

Rewrite using `[fibreCount, hfib, Set.encard_singleton]`.
-/
theorem fibreCount_coordPlaneIdeal {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ)
    (hπ : (coordPlaneBlock π).det ≠ 0) (w : EuclideanSpace ℂ (Fin m)) :
    fibreCount (HermNorm.std (m + k)) (coordPlaneIdeal m k) π w = 1 := by
  have hB : IsUnit (coordPlaneBlock π).det := Ne.isUnit hπ
  set x₀ : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 ((coordPlaneBlock π)⁻¹.mulVec fun i => w i)
  have hfib : {y | y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k) ∧ linProj π y = w} =
      {zeroExt m k x₀} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, mem_coneSet_coordPlaneIdeal]
    constructor
    · rintro ⟨hy, hπy⟩
      rw [eq_zeroExt_of hy] at hπy ⊢
      congr 1
      rw [linProj_zeroExt] at hπy
      have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin m) => (coordPlaneBlock π)⁻¹.mulVec fun i => v i) hπy
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec] at h2
      ext i
      simp only [x₀]
      rw [← h2]
    · rintro rfl
      refine ⟨zeroExt_apply_of_le x₀, ?_⟩
      rw [linProj_zeroExt]
      ext i
      simp [x₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB]
  rw [fibreCount, hfib, Set.encard_singleton]

def coordPlaneDetPoly (m k : ℕ) : MvPolynomial (Fin m × Fin (m + k)) ℂ :=
  (Matrix.of fun i j : Fin m => (X (i, Fin.castAdd k j) : MvPolynomial (Fin m × Fin (m + k)) ℂ)).det

/- English proof (translation)
Rewrite using `[coordPlaneDetPoly, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[coordPlaneBlock, RingHom.mapMatrix_apply, Function.curry]`.
-/
theorem eval_coordPlaneDetPoly {m k : ℕ} (u : Fin m × Fin (m + k) → ℂ) :
    eval u (coordPlaneDetPoly m k) = (coordPlaneBlock (Function.curry u)).det := by
  rw [coordPlaneDetPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [coordPlaneBlock, RingHom.mapMatrix_apply, Function.curry]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `eval_coordPlaneDetPoly (m := m) (k := k) (fun ij => if ij.2 = Fin.castAdd k ij.1 then 1 else 0)`. Establish `hone : coordPlaneBlock (Function.curry fun ij : Fin m × Fin (m + k) => if ij.2 = Fin.castAdd k ij.1 then (1 : ℂ) else 0) = 1`. Use extensionality with `i j`. Simplify using `[coordPlaneBlock, Function.curry, Matrix.one_apply, eq_comm]`.

Rewrite `h1` using `[h0, map_zero, hone, Matrix.det_one]`. Conclude with `zero_ne_one h1`.
-/
theorem coordPlaneDetPoly_ne_zero (m k : ℕ) : coordPlaneDetPoly m k ≠ 0 := by
  intro h0
  have h1 := eval_coordPlaneDetPoly (m := m) (k := k)
    (fun ij => if ij.2 = Fin.castAdd k ij.1 then 1 else 0)
  have hone : coordPlaneBlock (Function.curry fun ij : Fin m × Fin (m + k) =>
      if ij.2 = Fin.castAdd k ij.1 then (1 : ℂ) else 0) = 1 := by
    ext i j
    simp [coordPlaneBlock, Function.curry, Matrix.one_apply, eq_comm]
  rw [h0, map_zero, hone, Matrix.det_one] at h1
  exact zero_ne_one h1

/- English proof (translation)
Use `⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]`. Use `show Measure.pi (fun _ : Fin m × Fin n => (volume : Measure ℂ)) = _`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply, MeasurableEquiv.coe_curry_symm]`.

Establish `hset : Function.uncurry ⁻¹' Set.univ.pi s = Set.univ.pi fun i : Fin m => Set.univ.pi fun j : Fin n => s (i, j)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hset, Measure.pi_pi]`. Repeatedly rewrite using `[volume_pi, Measure.pi_pi]`.

Rewrite using `[Fintype.prod_prod_type]`.
-/
theorem measurePreserving_curry_matrix (m n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
      (volume : Measure (Fin m × Fin n → ℂ)) (Measure.pi fun _ : Fin m => (volume : Measure (Fin n → ℂ))) := by
  refine ⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  show Measure.pi (fun _ : Fin m × Fin n => (volume : Measure ℂ)) = _
  refine Measure.pi_eq fun s hs => ?_
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_curry_symm]
  have hset : Function.uncurry ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : Fin m => Set.univ.pi fun j : Fin n => s (i, j) := by
    ext x
    simp
  rw [hset, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/- English proof (translation)
Establish `hcover : (⋃ r : ℕ, LogInt.polydisc (Fin m × Fin (m + k)) r) = Set.univ`. Use `Set.eq_univ_of_forall fun u => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `exists_nat_ge (∑ ij, ‖u ij‖)`. Use `Set.mem_iUnion.2 ⟨r, ?_⟩` and prove the remaining obligations. Simplify using `only [LogInt.polydisc, Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right]`.

Introduce `ij`. Conclude with `(Finset.single_le_sum (fun ij _ => norm_nonneg (u ij)) (Finset.mem_univ ij)).trans hr`. Establish `hpoly : ∀ᵐ u : Fin m × Fin (m + k) → ℂ, eval u (coordPlaneDetPoly m k) ≠ 0`. Rewrite using `[← Measure.restrict_univ (μ := (volume : Measure (Fin m × Fin (m + k) → ℂ))), ← hcover, ae_restrict_iUnion_iff]`. Conclude with `fun r => LogInt.ae_eval_ne_zero _ (coordPlaneDetPoly_ne_zero m k) r`.

Establish `hp` using `measurePreserving_curry_matrix m (m + k)`. Express the relevant statement in the definitionally equal form `∀ᵐ π ∂(Measure.pi fun _ : Fin m => (volume : Measure (Fin (m + k) → ℂ))), _`. Rewrite using `[← hp.map_eq, (MeasurableEquiv.curry _ _ _).measurableEmbedding.ae_map_iff]`. Use `filter_upwards [hpoly] with u hu`. Rewrite `hu` using `[eval_coordPlaneDetPoly]`. Then use the resulting hypothesis.
-/
theorem ae_coordPlaneBlock_det_ne_zero (m k : ℕ) :
    ∀ᵐ π : Fin m → Fin (m + k) → ℂ, (coordPlaneBlock π).det ≠ 0 := by
  have hcover : (⋃ r : ℕ, LogInt.polydisc (Fin m × Fin (m + k)) r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge (∑ ij, ‖u ij‖)
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    simp only [LogInt.polydisc, Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall,
      dist_zero_right]
    intro ij
    exact (Finset.single_le_sum (fun ij _ => norm_nonneg (u ij)) (Finset.mem_univ ij)).trans hr
  have hpoly : ∀ᵐ u : Fin m × Fin (m + k) → ℂ, eval u (coordPlaneDetPoly m k) ≠ 0 := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Fin m × Fin (m + k) → ℂ))), ← hcover,
      ae_restrict_iUnion_iff]
    exact fun r => LogInt.ae_eval_ne_zero _ (coordPlaneDetPoly_ne_zero m k) r
  have hp := measurePreserving_curry_matrix m (m + k)
  change ∀ᵐ π ∂(Measure.pi fun _ : Fin m => (volume : Measure (Fin (m + k) → ℂ))), _
  rw [← hp.map_eq, (MeasurableEquiv.curry _ _ _).measurableEmbedding.ae_map_iff]
  filter_upwards [hpoly] with u hu
  rwa [eval_coordPlaneDetPoly] at hu

/- English proof (translation)
Rewrite using `[← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top c)]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hN] with π hπ`. Establish `hin : ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (N π w : ℝ≥0∞) = ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (c : ℝ≥0∞)`. Use `lintegral_congr_ae (ae_restrict_of_ae ?_)` and prove the remaining obligations.

Use `filter_upwards [hπ] with w hw`. Rewrite using `[hw]`. Simplify using the standard rewrite rules. Rewrite using `[hin, setLIntegral_const]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lintegral_matGauss_of_ae_eq {m n : ℕ} (c : ℕ)
    (N : (Fin m → Fin n → ℂ) → EuclideanSpace ℂ (Fin m) → ℕ∞)
    (hN : ∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), N π w = c) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (N π w : ℝ≥0∞) =
      (c : ℝ≥0∞) * ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) := by
  rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top c)]
  refine lintegral_congr_ae ?_
  filter_upwards [hN] with π hπ
  have hin : ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (N π w : ℝ≥0∞) =
      ∫⁻ _ in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (c : ℝ≥0∞) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hπ] with w hw
    rw [hw]
    simp
  rw [hin, setLIntegral_const]
  ring

/- English proof (translation)
Establish `: (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot` using `ae_neBot.2 (NeZero.ne _)`. Establish `: (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot` using `ae_neBot.2 (NeZero.ne _)`. Take `⟨π, hπ⟩` from `hfib.exists`. Take `⟨w, hw⟩` from `hπ.exists`.

Establish `hC : (coneSet h J).encard = δ`. Rewrite using `[← hw, fibreCount]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[Subsingleton.elim (linProj π y) w]`.

Establish `hsub : coneSet h J ⊆ {0}`. Introduce `y hy`. Assume the negation of the conclusion as `hy0`. Rewrite `hy0` using `[Set.mem_singleton_iff]`. Establish `hinf : (Set.range fun t : ℂ => t • y).Infinite` using `Set.infinite_range_of_injective (smul_left_injective ℂ hy0)`.

Establish `hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J`. Introduce and unpack `_ ⟨t, rfl⟩ q hq`. Establish `hpt : h.pointOf (t • y) = t • h.pointOf y`. Simplify using `only [HermNorm.pointOf]`. Rewrite using `[← Matrix.mulVec_smul]`.

Both sides reduce to the same expression. Rewrite using `[hpt]`. Conclude with `PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq`. Establish `htop` using `(hinf.mono hsub').encard_eq`. Rewrite `htop` using `[hC]`.

Conclude with `ENat.natCast_ne_top δ htop`. Establish `hset1 : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} = coneSet h J`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hy => hy.2`.

Introduce `hy`. Use `⟨?_, hy⟩` and prove the remaining obligations. Rewrite using `[Set.mem_singleton_iff.1 (hsub hy)]`. Simplify using the standard rewrite rules. Establish `hset2 : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, 0 ≤ (j : ℕ) → y j = 0} = {0}`.

Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff, zero_le, forall_const]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hy⟩`. Use extensionality with `j`.

Simplify using `[hy j]`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Rewrite using `[hset1, hset2, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton, mul_one]`. Break down `Set.subset_singleton_iff_eq.1 hsub with h0 | h0` into its components or cases.

Rewrite `hC` using `[h0, Set.encard_empty]`. Establish `hδ : δ = 0` using `by exact_mod_cast hC.symm`. Rewrite using `[h0, hδ]`. Simplify using the standard rewrite rules. Rewrite `hC` using `[h0, Set.encard_singleton]`.

Establish `hδ : δ = 1` using `by exact_mod_cast hC.symm`. Rewrite using `[h0, hδ, Measure.hausdorffMeasure_zero_singleton]`. Simplify using the standard rewrite rules.
-/
theorem coneMass_of_fibre_zero {n δ : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w = δ) :
    Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
      (δ : ℝ≥0∞) * Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, 0 ≤ (j : ℕ) → y j = 0} := by
  have : (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨π, hπ⟩ := hfib.exists
  obtain ⟨w, hw⟩ := hπ.exists
  have hC : (coneSet h J).encard = δ := by
    rw [← hw, fibreCount]
    congr 1
    ext y
    simp [Subsingleton.elim (linProj π y) w]
  have hsub : coneSet h J ⊆ {0} := by
    intro y hy
    by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    have hinf : (Set.range fun t : ℂ => t • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℂ hy0)
    have hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J := by
      rintro _ ⟨t, rfl⟩ q hq
      have hpt : h.pointOf (t • y) = t • h.pointOf y := by
        simp only [HermNorm.pointOf]
        rw [← Matrix.mulVec_smul]
        rfl
      rw [hpt]
      exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq
    have htop := (hinf.mono hsub').encard_eq
    rw [hC] at htop
    exact ENat.natCast_ne_top δ htop
  have hset1 : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
      coneSet h J := by
    ext y
    constructor
    · exact fun hy => hy.2
    · intro hy
      refine ⟨?_, hy⟩
      rw [Set.mem_singleton_iff.1 (hsub hy)]
      simp
  have hset2 : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, 0 ≤ (j : ℕ) → y j = 0} =
      {0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, zero_le, forall_const]
    constructor
    · rintro ⟨-, hy⟩
      ext j
      simp [hy j]
    · rintro rfl
      simp
  rw [hset1, hset2, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton, mul_one]
  rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h0
  · rw [h0, Set.encard_empty] at hC
    have hδ : δ = 0 := by exact_mod_cast hC.symm
    rw [h0, hδ]
    simp
  · rw [h0, Set.encard_singleton] at hC
    have hδ : δ = 1 := by exact_mod_cast hC.symm
    rw [h0, hδ, Measure.hausdorffMeasure_zero_singleton]
    simp

/- English proof (translation)
Introduce `n m δ h J hJ hfib`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Conclude with `coneMass_of_fibre_zero h J hJ hfib`. Distinguish the cases in `hmn : m ≤ n`. Use `swap`.

Establish `hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ)`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace_fin]`. Conclude with `(by omega : 2 * n < 2 * m)` after adjusting the coercions. Rewrite using `[Real.hausdorffMeasure_of_finrank_lt hlt]`. Simplify using the standard rewrite rules.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Take `⟨K, hK0, hKtop, hK⟩` from `hA (m + k) m`. Establish `hdet` using `ae_coordPlaneBlock_det_ne_zero m k`. Establish `hL1 : ∀ᵐ π : Fin m → Fin (m + k) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount (HermNorm.std (m + k)) (coordPlaneIdeal m k) π w = (1 : ℕ)` using `by filter_upwards [hdet] with π hπ`. Conclude with `Filter.Eventually.of_forall fun w => by`.

Rewrite using `[fibreCount_coordPlaneIdeal π hπ w]`. Both sides reduce to the same expression. Establish `hC` using `hK h J hJ (by filter_upwards [hfib] with π hπ filter_upwards [hπ] with w hw`. Rewrite using `[hw]`. Conclude with `ENat.natCast_ne_top δ)`.

Establish `hL` using `hK (HermNorm.std (m + k)) (coordPlaneIdeal m k) (isProjPrime_coordPlaneIdeal hm k) (by filter_upwards [hL1] with π hπ filter_upwards [hπ] with w hw`. Rewrite using `[hw]`. Conclude with `ENat.natCast_ne_top 1)`. Rewrite `hC` using `[lintegral_matGauss_of_ae_eq δ _ hfib]`. Rewrite `hL` using `[lintegral_matGauss_of_ae_eq 1 _ hL1, Nat.cast_one, one_mul]`.

Establish `hLset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k)} = {y | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, mem_coneSet_coordPlaneIdeal]`. Rewrite `hL` using `[hLset]`. Rewrite `hC` using `[hL, ← mul_assoc, mul_comm (δ : ℝ≥0∞) K, mul_assoc]`.

Conclude with `((ENNReal.mul_right_inj hK0.ne' hKtop.ne).1 hC).symm`.
-/
theorem ConeMassOfFibre.proof (hA : ConeFibreAverage.Statement) : ConeMassOfFibre.Statement := by
  intro n m δ h J hJ hfib
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact coneMass_of_fibre_zero h J hJ hfib
  by_cases hmn : m ≤ n
  swap
  · have hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ) := by
      rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 2 * n < 2 * m)
    rw [Real.hausdorffMeasure_of_finrank_lt hlt]
    simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨K, hK0, hKtop, hK⟩ := hA (m + k) m
  have hdet := ae_coordPlaneBlock_det_ne_zero m k
  have hL1 : ∀ᵐ π : Fin m → Fin (m + k) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m),
      fibreCount (HermNorm.std (m + k)) (coordPlaneIdeal m k) π w = (1 : ℕ) := by
    filter_upwards [hdet] with π hπ
    exact Filter.Eventually.of_forall fun w => by
      rw [fibreCount_coordPlaneIdeal π hπ w]
      rfl
  have hC := hK h J hJ (by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ)
  have hL := hK (HermNorm.std (m + k)) (coordPlaneIdeal m k) (isProjPrime_coordPlaneIdeal hm k) (by
    filter_upwards [hL1] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top 1)
  rw [lintegral_matGauss_of_ae_eq δ _ hfib] at hC
  rw [lintegral_matGauss_of_ae_eq 1 _ hL1, Nat.cast_one, one_mul] at hL
  have hLset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧
      y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k)} =
      {y | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_coneSet_coordPlaneIdeal]
  rw [hLset] at hL
  rw [hL, ← mul_assoc, mul_comm (δ : ℝ≥0∞) K, mul_assoc] at hC
  exact ((ENNReal.mul_right_inj hK0.ne' hKtop.ne).1 hC).symm

end

end GroundTheory.Heights₂.Heights
