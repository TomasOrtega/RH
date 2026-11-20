import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContDiffOnInverseFirstBlock

noncomputable section

open Matrix Filter Topology Polynomial
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
The claim follows from `(hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)`.
-/
theorem diffAt_of_cdo {f : M2 n → ℂ} {U : Set (M2 n)} (hf : ContDiffOn ℂ ∞ f U) (hU : IsOpen U) {x : M2 n}
    (hx : x ∈ U) : DifferentiableAt ℂ f x :=
  (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

/- English proof (translation)
Rewrite using `[inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def]`. Conclude with `Complex.mul_conj _`.
-/
theorem D0_eq_numSeg_mul_add {x : M2 n} (hx : InG x) :
    (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
  rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def]
  exact Complex.mul_conj _

/- English proof (translation)
The claim follows from `Complex.normSq_pos.mpr (det_first_block_ne_zero_group hx)`.
-/
theorem normSq_det_first_block_pos {x : M2 n} (hx : InG x) : 0 < Complex.normSq (u1 x).det :=
  Complex.normSq_pos.mpr (det_first_block_ne_zero_group hx)

/- English proof (translation)
Rewrite using `[D0_eq_numSeg_mul_add hx]`. Conclude with `Complex.ofReal_mem_slitPlane.mpr (normSq_det_first_block_pos hx)`.
-/
theorem det_product_mem_slitPlane {x : M2 n} (hx : InG x) : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
  rw [D0_eq_numSeg_mul_add hx]; exact Complex.ofReal_mem_slitPlane.mpr (normSq_det_first_block_pos hx)

/- English proof (translation)
Establish `hU : IsOpen {y : M2 n | det y ≠ 0}` using `isOpen_det_ne`. Establish `hxU : x ∈ {y : M2 n | det y ≠ 0}` using `(isUnit_det_of_inG hx).ne_zero`. Establish `hdet : DifferentiableAt ℂ (fun y : M2 n => det y) x` using `diffAt_of_cdo (cdo_det (fun i j => (contDiff_apply_apply ℂ ℂ i j).contDiffOn)) hU hxU`. Establish `hu1 : DifferentiableAt ℂ (fun y : M2 n => (u1 y).det) x` using `diffAt_of_cdo (cdo_det (fun i j => LVs.contDiffOn_first_cayley_block_entries _ i j)) hU hxU`. Establish `hub1 : DifferentiableAt ℂ (fun y : M2 n => (ub1 y).det) x` using `diffAt_of_cdo (cdo_det (fun i j => PositivityTheory.Rg.Sw.HSt.LoweringDerivative.contDiffOn_inverse_first_block i j)) hU hxU`.

Unfold `fz`. Use `((hdet.zpow (Or.inl hxU)).mul (hu1.zpow (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_` and prove the remaining obligations. Conclude with `(hu1.mul hub1).cpow (differentiableAt_const _) (det_product_mem_slitPlane hx)`.
-/
theorem diff_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) : DifferentiableAt ℂ (fz m e z) x := by
  have hU : IsOpen {y : M2 n | det y ≠ 0} := isOpen_det_ne
  have hxU : x ∈ {y : M2 n | det y ≠ 0} := (isUnit_det_of_inG hx).ne_zero
  have hdet : DifferentiableAt ℂ (fun y : M2 n => det y) x :=
    diffAt_of_cdo (cdo_det (fun i j => (contDiff_apply_apply ℂ ℂ i j).contDiffOn)) hU hxU
  have hu1 : DifferentiableAt ℂ (fun y : M2 n => (u1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => LVs.contDiffOn_first_cayley_block_entries _ i j)) hU hxU
  have hub1 : DifferentiableAt ℂ (fun y : M2 n => (ub1 y).det) x :=
    diffAt_of_cdo (cdo_det (fun i j => PositivityTheory.Rg.Sw.HSt.LoweringDerivative.contDiffOn_inverse_first_block i j)) hU hxU
  unfold fz
  refine ((hdet.zpow (Or.inl hxU)).mul (hu1.zpow (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hu1.mul hub1).cpow (differentiableAt_const _) (det_product_mem_slitPlane hx)

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Establish `h : (fun s : ℂ => (1 + s • A).det) = fun s => 1 + A.trace * s + (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2`. Use function extensionality and compare the values at `s`. Conclude with `Matrix.det_one_add_smul s A`. Rewrite using `[h]`. Establish `h1 : HasDerivAt (fun s : ℂ => 1 + A.trace * s) A.trace 0`.

Simplify using `using ((hasDerivAt_id (0 : ℂ)).const_mul A.trace).const_add 1`. Establish `h2 : HasDerivAt (fun s : ℂ => (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2) 0 0`. Use `(Polynomial.hasDerivAt (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX (0 : ℂ)).fun_mul (hasDerivAt_pow 2 (0 : ℂ)) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`.

Consider the case `simp`. Use `h1.fun_add h2 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `simp`.
-/
theorem hasDerivAt_det_one_add_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • A).det) A.trace 0 := by
  have h : (fun s : ℂ => (1 + s • A).det) = fun s =>
      1 + A.trace * s + (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2 := by
    funext s
    exact Matrix.det_one_add_smul s A
  rw [h]
  have h1 : HasDerivAt (fun s : ℂ => 1 + A.trace * s) A.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul A.trace).const_add 1
  have h2 : HasDerivAt (fun s : ℂ =>
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX.eval s * s ^ 2) 0 0 := by
    convert (Polynomial.hasDerivAt
      (det (1 + (Polynomial.X : ℂ[X]) • A.map Polynomial.C)).divX.divX (0 : ℂ)).fun_mul
      (hasDerivAt_pow 2 (0 : ℂ)) using 1
    all_goals first
      | rfl
      | simp
  convert h1.fun_add h2 using 1
  all_goals first
    | rfl
    | simp

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `n m e z Q x hx`. Establish `hxu : IsUnit x` using `isUnit_of_inG hx`. Establish `hD : (u1 x).det * (ub1 x).det ≠ 0` using `Complex.slitPlane_ne_zero (det_product_mem_slitPlane hx)`. Establish `hB : (ub1 x).det ≠ 0` using `right_ne_zero_of_mul hD`. Rewrite using `[rC_eq _ _ _ (diff_fz hx m e z), lowQ_eq]`.

Establish `hline : ∀ s : ℂ, x + s • (x * Nq Q) = x * (1 + s • Nq Q)`. Introduce `s`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`. Establish `hsub : ∀ s : ℂ, ub1 x - s • (Q * ub2 x) = ub1 x * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x)))`. Introduce `s`.

Establish `hBu : IsUnit (ub1 x).det` using `isUnit_iff_ne_zero.2 hB`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul, smul_neg, sub_eq_add_neg]`. Establish `hcomp : ∀ s : ℂ, fz m e z (x + s • (x * Nq Q)) = det x ^ e * (u1 x).det ^ (-(m : ℤ)) * ((u1 x).det * ((ub1 x).det * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))).det)) ^ (-z)`. Introduce `s`. Rewrite using `[hline s]`.

Unfold `fz`. Rewrite using `[det_lower, first_block_lowering_invariant, inverse_first_block_lowering hxu, hsub, Matrix.det_mul]`. Establish `htr : (-((ub1 x)⁻¹ * (Q * ub2 x))).trace = -(Om x * Q).trace`. Unfold `Om`. Rewrite using `[Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm Q]`.

Establish `hL : HasDerivAt (fun s : ℂ => x + s • (x * Nq Q)) (x * Nq Q) 0`. Use `((hasDerivAt_id (0 : ℂ)).smul_const (x * Nq Q)).const_add x using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `simp`.

Establish `h1 : HasDerivAt (fun s : ℂ => fz m e z (x + s • (x * Nq Q))) (fderiv ℂ (fz m e z) x (x * Nq Q)) 0` using `(diff_fz hx m e z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)`. Establish `hdet` using `hasDerivAt_det_one_add_smul (-((ub1 x)⁻¹ * (Q * ub2 x)))`. Establish `hg` using `(hdet.const_mul (ub1 x).det).const_mul (u1 x).det`. Establish `hg0 : (u1 x).det * ((ub1 x).det * (1 + (0 : ℂ) • -((ub1 x)⁻¹ * (Q * ub2 x))).det) ∈ Complex.slitPlane`. Simplify using `using det_product_mem_slitPlane hx`.

Establish `hp` using `(hg.cpow_const (c := -z) hg0).const_mul (det x ^ e * (u1 x).det ^ (-(m : ℤ)))`. Establish `h2` using `hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hcomp)`. Rewrite using `[h1.unique h2, htr]`. Simplify using `only [zero_smul, add_zero, Matrix.det_one, mul_one]`. Rewrite using `[Complex.cpow_sub _ _ hD, Complex.cpow_one]`.

Establish `hr : (u1 x).det * ((ub1 x).det * -(Om x * Q).trace) = -((u1 x).det * (ub1 x).det * (Om x * Q).trace)` using `by ring`. Rewrite using `[hr]`. Unfold `eQ fz`. Generalize the expression as in `(u1 x).det * (ub1 x).det = D at hD ⊢`. Clear the denominators using the available nonvanishing facts.
-/
theorem lt1 : LoweringDerivativeVacuum := by
  intro n m e z Q x hx
  have hxu : IsUnit x := isUnit_of_inG hx
  have hD : (u1 x).det * (ub1 x).det ≠ 0 := Complex.slitPlane_ne_zero (det_product_mem_slitPlane hx)
  have hB : (ub1 x).det ≠ 0 := right_ne_zero_of_mul hD
  rw [rC_eq _ _ _ (diff_fz hx m e z), lowQ_eq]
  have hline : ∀ s : ℂ, x + s • (x * Nq Q) = x * (1 + s • Nq Q) := by
    intro s
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hsub : ∀ s : ℂ, ub1 x - s • (Q * ub2 x) = ub1 x * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))) := by
    intro s
    have hBu : IsUnit (ub1 x).det := isUnit_iff_ne_zero.2 hB
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul, smul_neg, sub_eq_add_neg]
  have hcomp : ∀ s : ℂ, fz m e z (x + s • (x * Nq Q)) = det x ^ e * (u1 x).det ^ (-(m : ℤ)) *
      ((u1 x).det * ((ub1 x).det * (1 + s • -((ub1 x)⁻¹ * (Q * ub2 x))).det)) ^ (-z) := by
    intro s
    rw [hline s]
    unfold fz
    rw [det_lower, first_block_lowering_invariant, inverse_first_block_lowering hxu, hsub, Matrix.det_mul]
  have htr : (-((ub1 x)⁻¹ * (Q * ub2 x))).trace = -(Om x * Q).trace := by
    unfold Om
    rw [Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_mul_comm Q]
  have hL : HasDerivAt (fun s : ℂ => x + s • (x * Nq Q)) (x * Nq Q) 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const (x * Nq Q)).const_add x using 1
    all_goals first
      | rfl
      | simp
  have h1 : HasDerivAt (fun s : ℂ => fz m e z (x + s • (x * Nq Q)))
      (fderiv ℂ (fz m e z) x (x * Nq Q)) 0 :=
    (diff_fz hx m e z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hdet := hasDerivAt_det_one_add_smul (-((ub1 x)⁻¹ * (Q * ub2 x)))
  have hg := (hdet.const_mul (ub1 x).det).const_mul (u1 x).det
  have hg0 : (u1 x).det * ((ub1 x).det * (1 + (0 : ℂ) • -((ub1 x)⁻¹ * (Q * ub2 x))).det)
      ∈ Complex.slitPlane := by
    simpa using det_product_mem_slitPlane hx
  have hp := (hg.cpow_const (c := -z) hg0).const_mul (det x ^ e * (u1 x).det ^ (-(m : ℤ)))
  have h2 := hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hcomp)
  rw [h1.unique h2, htr]
  simp only [zero_smul, add_zero, Matrix.det_one, mul_one]
  rw [Complex.cpow_sub _ _ hD, Complex.cpow_one]
  have hr : (u1 x).det * ((ub1 x).det * -(Om x * Q).trace) =
      -((u1 x).det * (ub1 x).det * (Om x * Q).trace) := by ring
  rw [hr]
  unfold eQ fz
  generalize (u1 x).det * (ub1 x).det = D at hD ⊢
  field_simp

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative

namespace PositivityTheory.Rg.Sw.HSt

/- English proof (translation)
The claim follows from `LoweringDerivative.lt1`.
-/
theorem lt1 : LoweringDerivativeVacuum := LoweringDerivative.lt1

end PositivityTheory.Rg.Sw.HSt
