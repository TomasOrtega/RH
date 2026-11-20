import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

/- English proof (translation)
Establish `hr : 0 ≤ ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) ⬝ᵥ ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q)`. Simplify using `only [dotProduct]`. Conclude with `Finset.sum_nonneg fun i _ => mul_self_nonneg _`. Establish `hqp : q ⬝ᵥ p = 0` using `by rw [dotProduct_comm]; exact hpq`. Simplify using `only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm p v, dotProduct_comm q v, hv, hp, hpq, hqp] at hr`.

Use polynomial arithmetic with `[hr, hq]`.
-/
theorem bessel2 {d : ℕ} (v p q : Fin d → ℝ) (hv : v ⬝ᵥ v = 1) (hp : p ⬝ᵥ p = 1)
    (hpq : p ⬝ᵥ q = 0) (hq : 0 < q ⬝ᵥ q) :
    (v ⬝ᵥ p) ^ 2 * (q ⬝ᵥ q) + (v ⬝ᵥ q) ^ 2 ≤ q ⬝ᵥ q := by
  have hr : 0 ≤ ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) ⬝ᵥ
      ((q ⬝ᵥ q) • v - ((q ⬝ᵥ q) * (v ⬝ᵥ p)) • p - (v ⬝ᵥ q) • q) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hqp : q ⬝ᵥ p = 0 := by rw [dotProduct_comm]; exact hpq
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm p v, dotProduct_comm q v, hv, hp, hpq, hqp] at hr
  nlinarith [hr, hq]

/- English proof (translation)
Introduce `d L G K R hLR hR hG hKG hKL hK x`. Establish `hRi : R * R⁻¹ = 1` using `Matrix.mul_nonsing_inv R hR`. Establish `hiR : R⁻¹ * R = 1` using `Matrix.nonsing_inv_mul R hR`. Establish `hRt : Rᵀ * (R⁻¹)ᵀ = 1` using `by rw [← Matrix.transpose_mul, hiR, Matrix.transpose_one]`. Establish `htR : (R⁻¹)ᵀ * Rᵀ = 1` using `by rw [← Matrix.transpose_mul, hRi, Matrix.transpose_one]`.

Establish `hCpsd : (R * G * Rᵀ).PosSemidef`. Use `hG.mul_mul_conjTranspose_same R` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_eq_transpose_of_trivial]`. Establish `hCtr : trace (R * G * Rᵀ) = trace (L * G)`. Rewrite using `[Matrix.trace_mul_cycle, hLR]`.

Establish `hJ' : (R⁻¹)ᵀ * K * Rᵀ = -(R * Kᵀ * R⁻¹)`. Establish `h2 : (R⁻¹)ᵀ * (K * L) * R⁻¹ = (R⁻¹)ᵀ * (-(L * Kᵀ)) * R⁻¹` using `by rw [hKL]`. Rewrite `h2` using `[hLR]`. Establish `e1 : (R⁻¹)ᵀ * (K * (Rᵀ * R)) * R⁻¹ = (R⁻¹)ᵀ * K * Rᵀ`. Simplify using `only [Matrix.mul_assoc, hRi, Matrix.mul_one]`.

Establish `e2 : (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * R⁻¹ = -(R * Kᵀ * R⁻¹)`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul]`. Use `congr 1`. Simplify using `only [← Matrix.mul_assoc, htR, Matrix.one_mul]`. Rewrite using `[← e1, h2, e2]`.

Establish `hJskew : ((R⁻¹)ᵀ * K * Rᵀ)ᵀ = -((R⁻¹)ᵀ * K * Rᵀ)`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose, hJ', neg_neg, Matrix.mul_assoc]`. Establish `hCJ : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ)`. Establish `l1 : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * (G * K) * Rᵀ`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = R * (G * K) * Rᵀ := by rw [hRt, Matrix.mul_one]; simp only [Matrix.mul_assoc]`. Establish `l2 : ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = R * (G * K) * Rᵀ`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * G * Rᵀ := by rw [← hLR, hKL, hLR]`. Use `_ = -(((R⁻¹)ᵀ * Rᵀ) * R * (Kᵀ * G) * Rᵀ) := by`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Use `_ = R * (G * K) * Rᵀ := by`. Rewrite using `[htR, hKG, Matrix.one_mul]`.

Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]`. Rewrite using `[l1, l2]`. Establish `hJdet : IsUnit ((R⁻¹)ᵀ * K * Rᵀ).det`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]`. Conclude with `((Matrix.isUnit_nonsing_inv_det R hR).mul hK).mul hR`.

Use `set C := R * G * Rᵀ with hCdef`. Use `set J := (R⁻¹)ᵀ * K * Rᵀ with hJdef`. Establish `hJinj : ∀ v : Fin d → ℝ, J *ᵥ v = 0 → v = 0`. Introduce `v hv`. Establish `: (J⁻¹ * J) *ᵥ v = 0` using `by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]`.

Rewrite `this` using `[Matrix.nonsing_inv_mul J hJdet, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `hH : C.IsHermitian` using `hCpsd.1`. Establish `hCt : Cᵀ = C`. Use `hH.eq` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_eq_transpose_of_trivial]`. Then use the resulting hypothesis.

Establish `hsym : ∀ v w : Fin d → ℝ, (C *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (C *ᵥ w)`. Introduce `v w`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hCt, dotProduct_comm]`. Set `ev : Fin d → (Fin d → ℝ)` to `fun j => ⇑(hH.eigenvectorBasis j)`. Set `lam : Fin d → ℝ` to `hH.eigenvalues`.

Establish `hCev : ∀ j, C *ᵥ ev j = lam j • ev j` using `fun j => hH.mulVec_eigenvectorBasis j`. Establish `hort : ∀ i j, ev i ⬝ᵥ ev j = if j = i then 1 else 0`. Introduce `i j`. Use `(orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) j i` as an intermediate fact. Rewrite `this` using `[EuclideanSpace.inner_eq_star_dotProduct]`.

Simplify `this` using `[ev, star_trivial]`. Establish `hinner : ∀ (v : Fin d → ℝ) j, inner ℝ (WithLp.toLp 2 v) (hH.eigenvectorBasis j) = ev j ⬝ᵥ v`. Introduce `v j`. Rewrite using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `[ev, star_trivial]`.

Establish `hinner' : ∀ (v : Fin d → ℝ) j, inner ℝ (hH.eigenvectorBasis j) (WithLp.toLp 2 v) = ev j ⬝ᵥ v`. Introduce `v j`. Rewrite using `[real_inner_comm]`. Conclude with `hinner v j`. Establish `hquad : ∀ v : Fin d → ℝ, v ⬝ᵥ (C *ᵥ v) = ∑ j, lam j * (ev j ⬝ᵥ v) ^ 2`.

Introduce `v`. Establish `h` using `hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 (C *ᵥ v))`. Rewrite `h` using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h`. Rewrite using `[dotProduct_comm, ← h]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[dotProduct_comm (ev j), ← hsym, hCev, smul_dotProduct, smul_eq_mul, dotProduct_comm v]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpars : ∀ v : Fin d → ℝ, ∑ j, (ev j ⬝ᵥ v) ^ 2 = v ⬝ᵥ v`. Introduce `v`.

Establish `h` using `hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 v)`. Rewrite `h` using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h`. Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Establish `hlam0 : ∀ j, 0 ≤ lam j` using `fun j => hCpsd.eigenvalues_nonneg j`. Establish `htr : trace C = ∑ j, lam j` using `by simpa using hH.trace_eq_sum_eigenvalues`. Establish `hlam : ∀ i, lam i ≤ trace C / 2`. Introduce `i`. Use `set u := J *ᵥ ev i with hu`.

Establish `hCu : C *ᵥ u = lam i • u`. Rewrite using `[hu, Matrix.mulVec_mulVec, hCJ, ← Matrix.mulVec_mulVec, hCev, Matrix.mulVec_smul]`. Establish `hvu : ev i ⬝ᵥ u = 0`. Establish `h1 : ev i ⬝ᵥ u = (Jᵀ *ᵥ ev i) ⬝ᵥ ev i`. Rewrite using `[hu, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]`.

Rewrite `h1` using `[hJskew, Matrix.neg_mulVec, neg_dotProduct, ← hu, dotProduct_comm]`. Establish `h2 : u ⬝ᵥ ev i = 0` using `by linarith`. Rewrite using `[dotProduct_comm]`. Conclude with `h2`. Establish `hv1 : ev i ⬝ᵥ ev i = 1` using `by rw [hort, if_pos rfl]`.

Establish `hu0 : u ≠ 0`. Introduce `h0`. Establish `: ev i = 0` using `hJinj _ (by rw [← hu, h0])`. Rewrite `hv1` using `[this, dotProduct_zero]`. Conclude with `zero_ne_one hv1`.

Establish `huu : 0 < u ⬝ᵥ u`. Break down `(show 0 ≤ u ⬝ᵥ u from Finset.sum_nonneg fun k _ => mul_self_nonneg _).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (dotProduct_self_eq_zero.mp h.symm) hu0`. Establish `hq1 : u ⬝ᵥ (C *ᵥ u) = lam i * (u ⬝ᵥ u)`.

Rewrite using `[hCu, dotProduct_smul, smul_eq_mul]`. Establish `hq2` using `hquad u`. Establish `hsum1 : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u)) = lam i * (u ⬝ᵥ u)`. Simplify using `only [hort]`. Simplify using `[Finset.sum_ite_eq', Finset.mem_univ]`.

Establish `hbes : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u) + (ev j ⬝ᵥ u) ^ 2) ≤ ∑ j, lam j * (u ⬝ᵥ u)`. Use `Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hlam0 j)` and prove the remaining obligations. Conclude with `bessel2 (ev j) (ev i) u (by rw [hort, if_pos rfl]) hv1 hvu huu`. Simplify using `only [mul_add, Finset.sum_add_distrib] at hbes`. Rewrite `hbes` using `[hsum1, ← hq2, hq1, ← Finset.sum_mul, ← htr]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hcore : ∀ w : Fin d → ℝ, w ⬝ᵥ (C *ᵥ w) ≤ trace C / 2 * (w ⬝ᵥ w)`. Introduce `w`. Rewrite using `[hquad, ← hpars, Finset.mul_sum]`. Conclude with `Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlam j) (sq_nonneg _)`.

Establish `hx : x ⬝ᵥ (G *ᵥ x) = ((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ (C *ᵥ ((R⁻¹)ᵀ *ᵥ x))`. Establish `e1 : C *ᵥ ((R⁻¹)ᵀ *ᵥ x) = R *ᵥ (G *ᵥ x)`. Rewrite using `[hCdef, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRt, Matrix.mul_one, ← Matrix.mulVec_mulVec]`. Rewrite using `[e1, Matrix.dotProduct_mulVec ((R⁻¹)ᵀ *ᵥ x) R, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hRt, Matrix.one_mulVec]`. Rewrite using `[hx]`.

Use `hcore ((R⁻¹)ᵀ *ᵥ x)` as an intermediate fact. Rewrite `this` using `[hCtr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem halfTrace_holds : HalfTraceStatement := by
  intro d L G K R hLR hR hG hKG hKL hK x
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRt : Rᵀ * (R⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hiR, Matrix.transpose_one]
  have htR : (R⁻¹)ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRi, Matrix.transpose_one]

  have hCpsd : (R * G * Rᵀ).PosSemidef := by
    have := hG.mul_mul_conjTranspose_same R
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hCtr : trace (R * G * Rᵀ) = trace (L * G) := by
    rw [Matrix.trace_mul_cycle, hLR]
  have hJ' : (R⁻¹)ᵀ * K * Rᵀ = -(R * Kᵀ * R⁻¹) := by
    have h2 : (R⁻¹)ᵀ * (K * L) * R⁻¹ = (R⁻¹)ᵀ * (-(L * Kᵀ)) * R⁻¹ := by rw [hKL]
    rw [hLR] at h2
    have e1 : (R⁻¹)ᵀ * (K * (Rᵀ * R)) * R⁻¹ = (R⁻¹)ᵀ * K * Rᵀ := by
      simp only [Matrix.mul_assoc, hRi, Matrix.mul_one]
    have e2 : (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * R⁻¹ = -(R * Kᵀ * R⁻¹) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]
      congr 1
      simp only [← Matrix.mul_assoc, htR, Matrix.one_mul]
    rw [← e1, h2, e2]
  have hJskew : ((R⁻¹)ᵀ * K * Rᵀ)ᵀ = -((R⁻¹)ᵀ * K * Rᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, hJ', neg_neg, Matrix.mul_assoc]
  have hCJ : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) := by
    have l1 : (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * (G * K) * Rᵀ := by
      calc (R * G * Rᵀ) * ((R⁻¹)ᵀ * K * Rᵀ) = R * G * (Rᵀ * (R⁻¹)ᵀ) * K * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by rw [hRt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    have l2 : ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = R * (G * K) * Rᵀ := by
      calc ((R⁻¹)ᵀ * K * Rᵀ) * (R * G * Rᵀ) = (R⁻¹)ᵀ * (K * (Rᵀ * R)) * G * Rᵀ := by
            simp only [Matrix.mul_assoc]
        _ = (R⁻¹)ᵀ * (-(Rᵀ * R * Kᵀ)) * G * Rᵀ := by rw [← hLR, hKL, hLR]
        _ = -(((R⁻¹)ᵀ * Rᵀ) * R * (Kᵀ * G) * Rᵀ) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = R * (G * K) * Rᵀ := by
            rw [htR, hKG, Matrix.one_mul]
            simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [l1, l2]
  have hJdet : IsUnit ((R⁻¹)ᵀ * K * Rᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]
    exact ((Matrix.isUnit_nonsing_inv_det R hR).mul hK).mul hR
  set C := R * G * Rᵀ with hCdef
  set J := (R⁻¹)ᵀ * K * Rᵀ with hJdef
  have hJinj : ∀ v : Fin d → ℝ, J *ᵥ v = 0 → v = 0 := by
    intro v hv
    have : (J⁻¹ * J) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rwa [Matrix.nonsing_inv_mul J hJdet, Matrix.one_mulVec] at this
  have hH : C.IsHermitian := hCpsd.1
  have hCt : Cᵀ = C := by
    have := hH.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsym : ∀ v w : Fin d → ℝ, (C *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (C *ᵥ w) := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hCt, dotProduct_comm]

  let ev : Fin d → (Fin d → ℝ) := fun j => ⇑(hH.eigenvectorBasis j)
  let lam : Fin d → ℝ := hH.eigenvalues
  have hCev : ∀ j, C *ᵥ ev j = lam j • ev j := fun j => hH.mulVec_eigenvectorBasis j
  have hort : ∀ i j, ev i ⬝ᵥ ev j = if j = i then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) j i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    simpa [ev, star_trivial] using this
  have hinner : ∀ (v : Fin d → ℝ) j,
      inner ℝ (WithLp.toLp 2 v) (hH.eigenvectorBasis j) = ev j ⬝ᵥ v := by
    intro v j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [ev, star_trivial]
  have hinner' : ∀ (v : Fin d → ℝ) j,
      inner ℝ (hH.eigenvectorBasis j) (WithLp.toLp 2 v) = ev j ⬝ᵥ v := by
    intro v j
    rw [real_inner_comm]; exact hinner v j
  have hquad : ∀ v : Fin d → ℝ, v ⬝ᵥ (C *ᵥ v) = ∑ j, lam j * (ev j ⬝ᵥ v) ^ 2 := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 (C *ᵥ v))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [dotProduct_comm, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_comm (ev j), ← hsym, hCev, smul_dotProduct, smul_eq_mul, dotProduct_comm v]
    ring
  have hpars : ∀ v : Fin d → ℝ, ∑ j, (ev j ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := by
    intro v
    have h := hH.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 v) (WithLp.toLp 2 v)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [hinner, hinner', star_trivial, WithLp.ofLp_toLp] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => hCpsd.eigenvalues_nonneg j
  have htr : trace C = ∑ j, lam j := by simpa using hH.trace_eq_sum_eigenvalues

  have hlam : ∀ i, lam i ≤ trace C / 2 := by
    intro i
    set u := J *ᵥ ev i with hu
    have hCu : C *ᵥ u = lam i • u := by
      rw [hu, Matrix.mulVec_mulVec, hCJ, ← Matrix.mulVec_mulVec, hCev, Matrix.mulVec_smul]
    have hvu : ev i ⬝ᵥ u = 0 := by
      have h1 : ev i ⬝ᵥ u = (Jᵀ *ᵥ ev i) ⬝ᵥ ev i := by
        rw [hu, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      rw [hJskew, Matrix.neg_mulVec, neg_dotProduct, ← hu, dotProduct_comm] at h1
      have h2 : u ⬝ᵥ ev i = 0 := by linarith
      rw [dotProduct_comm]; exact h2
    have hv1 : ev i ⬝ᵥ ev i = 1 := by rw [hort, if_pos rfl]
    have hu0 : u ≠ 0 := by
      intro h0
      have : ev i = 0 := hJinj _ (by rw [← hu, h0])
      rw [this, dotProduct_zero] at hv1
      exact zero_ne_one hv1
    have huu : 0 < u ⬝ᵥ u := by
      rcases (show 0 ≤ u ⬝ᵥ u from Finset.sum_nonneg fun k _ => mul_self_nonneg _).lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hu0
    have hq1 : u ⬝ᵥ (C *ᵥ u) = lam i * (u ⬝ᵥ u) := by
      rw [hCu, dotProduct_smul, smul_eq_mul]
    have hq2 := hquad u
    have hsum1 : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u)) = lam i * (u ⬝ᵥ u) := by
      simp only [hort]
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hbes : ∑ j, lam j * ((ev j ⬝ᵥ ev i) ^ 2 * (u ⬝ᵥ u) + (ev j ⬝ᵥ u) ^ 2) ≤
        ∑ j, lam j * (u ⬝ᵥ u) := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hlam0 j)
      exact bessel2 (ev j) (ev i) u (by rw [hort, if_pos rfl]) hv1 hvu huu
    simp only [mul_add, Finset.sum_add_distrib] at hbes
    rw [hsum1, ← hq2, hq1, ← Finset.sum_mul, ← htr] at hbes
    nlinarith

  have hcore : ∀ w : Fin d → ℝ, w ⬝ᵥ (C *ᵥ w) ≤ trace C / 2 * (w ⬝ᵥ w) := by
    intro w
    rw [hquad, ← hpars, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hlam j) (sq_nonneg _)

  have hx : x ⬝ᵥ (G *ᵥ x) = ((R⁻¹)ᵀ *ᵥ x) ⬝ᵥ (C *ᵥ ((R⁻¹)ᵀ *ᵥ x)) := by
    have e1 : C *ᵥ ((R⁻¹)ᵀ *ᵥ x) = R *ᵥ (G *ᵥ x) := by
      rw [hCdef, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRt, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    rw [e1, Matrix.dotProduct_mulVec ((R⁻¹)ᵀ *ᵥ x) R, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hRt, Matrix.one_mulVec]
  rw [hx]
  have := hcore ((R⁻¹)ᵀ *ᵥ x)
  rw [hCtr] at this
  linarith

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
