import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import ReciprocityTheory.SemistableReduction.BWPolyA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

/- English proof (translation)
Rewrite using `[MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hdeg : ∑ i ∈ m.support, m i = d`. Establish `h` using `hφ (MvPolynomial.mem_support_iff.mp hm)`. Simplify `h` using `[Finsupp.weight_apply, Finsupp.sum]`.

Repeatedly rewrite using `[Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bwp_eval_smul_of_isHomogeneous {σ : Type*} {φ : MvPolynomial σ ℂ} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (t • z) φ = t ^ d * MvPolynomial.eval z φ := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring

def bwpMat {p : ℕ} (z : Fin p × Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun i j => z (i, j)

def bwpId (p : ℕ) : Fin p × Fin p → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

/- English proof (translation)
Use `⟨(Matrix.of fun i j => Polynomial.C (z (i, j)) + Polynomial.C (v (i, j)) * Polynomial.X).det, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, bwpMat, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bwp_det_line_poly {p : ℕ} (z v : Fin p × Fin p → ℂ) :
    ∃ Λ : ℂ[X], ∀ t : ℂ, Λ.eval t = (bwpMat (z + t • v)).det := by
  refine ⟨(Matrix.of fun i j => Polynomial.C (z (i, j)) + Polynomial.C (v (i, j)) * Polynomial.X).det,
    fun t => ?_⟩
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, bwpMat, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/- English proof (translation)
Take `⟨Λ, hΛ⟩` from `bwp_det_line_poly z v`. Establish `hΛ0 : Λ ≠ 0`. Introduce `h`. Apply `hz` to reduce the goal to its premises. Establish `h0` using `hΛ 0`.

Rewrite `h0` using `[h, Polynomial.eval_zero]`. Simplify using `using h0.symm`. Use `(bwp_finite_eval_eq_zero hΛ0).subset fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at ht ⊢`. Rewrite using `[hΛ]`.

Conclude with `ht`.
-/
theorem bwp_finite_det_line {p : ℕ} (z v : Fin p × Fin p → ℂ) (hz : (bwpMat z).det ≠ 0) :
    {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite := by
  obtain ⟨Λ, hΛ⟩ := bwp_det_line_poly z v
  have hΛ0 : Λ ≠ 0 := by
    intro h
    apply hz
    have h0 := hΛ 0
    rw [h, Polynomial.eval_zero] at h0
    simpa using h0.symm
  refine (bwp_finite_eval_eq_zero hΛ0).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [hΛ]
  exact ht

/- English proof (translation)
Establish `hne : (-bwpMat z).charpoly ≠ 0` using `(Matrix.charpoly_monic _).ne_zero`. Use `(bwp_finite_eval_eq_zero hne).subset fun s hs => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hs ⊢`. Rewrite using `[Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `hs using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply, h]`.
-/
theorem bwp_finite_det_id_line {p : ℕ} (z : Fin p × Fin p → ℂ) :
    {s : ℂ | (bwpMat (z + s • bwpId p)).det = 0}.Finite := by
  have hne : (-bwpMat z).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  refine (bwp_finite_eval_eq_zero hne).subset fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  convert hs using 2
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply]
    ring
  · simp [Matrix.charmatrix_apply, bwpMat, bwpId, Matrix.diagonal_apply, h]

/- English proof (translation)
Use `first`. Consider the case `exact continuous_id`. Consider the case `exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)`.
-/
theorem bwp_continuous_of_matrix {p : ℕ} :
    Continuous (fun y : Fin p → Fin p → ℂ => Matrix.of y) := by
  first
    | exact continuous_id
    | exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)

/- English proof (translation)
Use `set S : Set (Fin p → Fin p → ℂ) := {y | Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1} with hS`. Establish `hcl : IsClosed S` using `isClosed_eq (bwp_continuous_of_matrix.matrix_conjTranspose.matrix_mul bwp_continuous_of_matrix) continuous_const`. Establish `hbd : Bornology.IsBounded S`. Rewrite using `[Metric.isBounded_iff_subset_closedBall 0]`. Use `⟨1, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hU : Matrix.of y ∈ Matrix.unitaryGroup (Fin p) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Conclude with `hy`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Use `(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_` and prove the remaining obligations.

Use `first`. Consider the case `exact entry_norm_bound_of_unitary hU i j`. Consider the case `exact Matrix.UnitaryGroup.entry_norm_bound hU i j`. Consider the case `exact Matrix.norm_entry_le_one_of_unitary hU i j`. Establish `hK : IsCompact S` using `Metric.isCompact_of_isClosed_isBounded hcl hbd`.

Establish `hsub : S ⊆ {y | (Matrix.of y).det ≠ 0}` using `fun y hy => by`. Establish `h` using `congrArg Matrix.det (show Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1 from hy)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `right_ne_zero_of_mul_eq_one h`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (DifferentiableOn.continuousOn hP |>.mono hsub)`.

Use `⟨C, fun U hU => ?_⟩` and prove the remaining obligations. Establish `hU' : U ∈ S`. Rewrite `hU` using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Conclude with `hU`. Conclude with `hC U hU'`.
-/
theorem bwp_exists_bound_unitary {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) :
    ∃ C : ℝ, ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ‖P U‖ ≤ C := by
  set S : Set (Fin p → Fin p → ℂ) := {y | Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1} with hS
  have hcl : IsClosed S :=
    isClosed_eq (bwp_continuous_of_matrix.matrix_conjTranspose.matrix_mul bwp_continuous_of_matrix)
      continuous_const
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun y hy => ?_⟩
    have hU : Matrix.of y ∈ Matrix.unitaryGroup (Fin p) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hy
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    first
      | exact entry_norm_bound_of_unitary hU i j
      | exact Matrix.UnitaryGroup.entry_norm_bound hU i j
      | exact Matrix.norm_entry_le_one_of_unitary hU i j
  have hK : IsCompact S := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hsub : S ⊆ {y | (Matrix.of y).det ≠ 0} := fun y hy => by
    have h := congrArg Matrix.det (show Matrix.conjTranspose (Matrix.of y) * Matrix.of y = 1 from hy)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact right_ne_zero_of_mul_eq_one h
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (DifferentiableOn.continuousOn hP |>.mono hsub)
  refine ⟨C, fun U hU => ?_⟩
  have hU' : U ∈ S := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  exact hC U hU'

/- English proof (translation)
Take `⟨C, hC⟩` from `bwp_exists_bound_unitary P hP`. Use `set M : ℝ := ∑ i, ∑ j, (‖z (i, j)‖ + ‖v (i, j)‖) with hMdef`. Establish `hM0 : 0 ≤ M` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity`. Establish `hMj : ∀ j, ∑ i, (‖z (i, j)‖ + ‖v (i, j)‖) ≤ M` using `fun j => Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => ‖z (i, j')‖ + ‖v (i, j')‖) (fun j' _ => by positivity) (Finset.mem_univ j)`. Establish `hbound : ∀ t ∉ {t : ℂ | (bwpMat (z + t • v)).det = 0}, ‖P (bwpMat (z + t • v))‖ ≤ (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i)`.

Introduce `t ht`. Establish `hdet : (bwpMat (z + t • v)).det ≠ 0` using `ht`. Establish `hcol : ∀ j, colNormSq (bwpMat (z + t • v)) j ≤ (M * (1 + ‖t‖)) ^ 2`. Introduce `j`. Establish `hz : ∑ i, ‖z (i, j)‖ ≤ M` using `le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (norm_nonneg _)) (hMj j)`.

Establish `hv : ∑ i, ‖v (i, j)‖ ≤ M` using `le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_left (norm_nonneg _)) (hMj j)`. Use `set e : Fin p → ℝ := fun i => ‖bwpMat (z + t • v) i j‖ with he_def`. Establish `he0 : ∀ i, 0 ≤ e i` using `fun i => norm_nonneg _`. Establish `he : ∑ i, e i ≤ M * (1 + ‖t‖)`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Simplify using `only [he_def, bwpMat, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `(norm_add_le _ _).trans (by rw [norm_mul])`. Use `_ = ∑ i, ‖z (i, j)‖ + ‖t‖ * ∑ i, ‖v (i, j)‖ := by`. Rewrite using `[Finset.sum_add_distrib, Finset.mul_sum]`.

Use `_ ≤ M * (1 + ‖t‖) := by nlinarith [norm_nonneg t]`. Establish `hsq : ∑ i, e i ^ 2 ≤ (∑ i, e i) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hR : 0 ≤ M * (1 + ‖t‖)` using `mul_nonneg hM0 (by positivity)`.

Establish `h` using `hH Unit (fun _ => p) (fun _ => a) (fun x => P (x ())) C (M * (1 + ‖t‖)) (by`. Introduce `x s b hx hb htri`. Consider the cases of `s`. Use `first`. Consider the case `simp only [Function.update_self]`.

Consider the case `simp only [Function.update_same]`. Conclude with `hT (x ()) b (hx ()) hb htri)`. Use the proof step `(fun k hk => hC (k ()) (hk ())) hR (fun _ => bwpMat (z + t • v)) (fun _ => hdet)`. Use the proof step `(fun _ j => hcol j)`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton] at h`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdiff : DifferentiableOn ℂ (fun t => P (bwpMat (z + t • v))) {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ`. Establish `hL : Differentiable ℂ (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ))`. Rewrite using `[differentiable_pi]`. Introduce `i`.

Rewrite using `[differentiable_pi]`. Introduce `j`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `fun_prop`. Establish `hc : DifferentiableOn ℂ ((fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) ∘ (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ))) {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ` using `DifferentiableOn.comp hP hL.differentiableOn (fun t ht => ht)`.

Conclude with `hc`. Take `⟨Q, hQdeg, hQ⟩` from `hO (fun t => P (bwpMat (z + t • v))) _ (C * M ^ (∑ i, a i)) (∑ i, a i) hB hdiff hbound`. Conclude with `⟨Q, hQdeg, fun t ht => hQ t ht⟩`.
-/
theorem bwp_line_poly (hH : LemmaHStatement) (hO : OnePolyGrowthStatement) {p : ℕ} (a : Fin p → ℕ)
    (P : Matrix (Fin p) (Fin p) ℂ → ℂ) (hP : IsHoloGL P) (hT : IsTriEquivariant a P)
    (z v : Fin p × Fin p → ℂ) (hB : {t : ℂ | (bwpMat (z + t • v)).det = 0}.Finite) :
    ∃ Q : ℂ[X], Q.natDegree ≤ ∑ i, a i ∧
      ∀ t, (bwpMat (z + t • v)).det ≠ 0 → P (bwpMat (z + t • v)) = Q.eval t := by
  classical
  obtain ⟨C, hC⟩ := bwp_exists_bound_unitary P hP
  set M : ℝ := ∑ i, ∑ j, (‖z (i, j)‖ + ‖v (i, j)‖) with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hMj : ∀ j, ∑ i, (‖z (i, j)‖ + ‖v (i, j)‖) ≤ M := fun j =>
    Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j' => ‖z (i, j')‖ + ‖v (i, j')‖)
      (fun j' _ => by positivity) (Finset.mem_univ j)
  have hbound : ∀ t ∉ {t : ℂ | (bwpMat (z + t • v)).det = 0},
      ‖P (bwpMat (z + t • v))‖ ≤ (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by
    intro t ht
    have hdet : (bwpMat (z + t • v)).det ≠ 0 := ht
    have hcol : ∀ j, colNormSq (bwpMat (z + t • v)) j ≤ (M * (1 + ‖t‖)) ^ 2 := by
      intro j
      have hz : ∑ i, ‖z (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (norm_nonneg _)) (hMj j)
      have hv : ∑ i, ‖v (i, j)‖ ≤ M :=
        le_trans (Finset.sum_le_sum fun i _ => le_add_of_nonneg_left (norm_nonneg _)) (hMj j)
      set e : Fin p → ℝ := fun i => ‖bwpMat (z + t • v) i j‖ with he_def
      have he0 : ∀ i, 0 ≤ e i := fun i => norm_nonneg _
      have he : ∑ i, e i ≤ M * (1 + ‖t‖) := by
        calc ∑ i, e i ≤ ∑ i, (‖z (i, j)‖ + ‖t‖ * ‖v (i, j)‖) := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [he_def, bwpMat, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              exact (norm_add_le _ _).trans (by rw [norm_mul])
          _ = ∑ i, ‖z (i, j)‖ + ‖t‖ * ∑ i, ‖v (i, j)‖ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ M * (1 + ‖t‖) := by nlinarith [norm_nonneg t]
      have hsq : ∑ i, e i ^ 2 ≤ (∑ i, e i) ^ 2 := by
        calc ∑ i, e i ^ 2 = ∑ i, e i * e i := Finset.sum_congr rfl fun i _ => sq (e i)
          _ ≤ ∑ i, e i * ∑ j', e j' := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (fun j' _ => he0 j') (Finset.mem_univ i)) (he0 i)
          _ = (∑ i, e i) ^ 2 := by rw [← Finset.sum_mul, sq]
      calc colNormSq (bwpMat (z + t • v)) j = ∑ i, e i ^ 2 := rfl
        _ ≤ (∑ i, e i) ^ 2 := hsq
        _ ≤ (M * (1 + ‖t‖)) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => he0 i) he 2
    have hR : 0 ≤ M * (1 + ‖t‖) := mul_nonneg hM0 (by positivity)
    have h := hH Unit (fun _ => p) (fun _ => a) (fun x => P (x ())) C (M * (1 + ‖t‖))
      (by
        intro x s b hx hb htri
        cases s
        first
          | simp only [Function.update_self]
          | simp only [Function.update_same]
        exact hT (x ()) b (hx ()) hb htri)
      (fun k hk => hC (k ()) (hk ())) hR (fun _ => bwpMat (z + t • v)) (fun _ => hdet)
      (fun _ j => hcol j)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    calc ‖P (bwpMat (z + t • v))‖ ≤ C * (M * (1 + ‖t‖)) ^ ∑ i, a i := h
      _ = (C * M ^ (∑ i, a i)) * (1 + ‖t‖) ^ (∑ i, a i) := by rw [mul_pow]; ring
  have hdiff : DifferentiableOn ℂ (fun t => P (bwpMat (z + t • v)))
      {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ := by
    have hL : Differentiable ℂ (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)) := by
      rw [differentiable_pi]
      intro i
      rw [differentiable_pi]
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have hc : DifferentiableOn ℂ ((fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) ∘
        (fun t : ℂ => (fun i j => (z + t • v) (i, j) : Fin p → Fin p → ℂ)))
        {t : ℂ | (bwpMat (z + t • v)).det = 0}ᶜ :=
      DifferentiableOn.comp hP hL.differentiableOn (fun t ht => ht)
    exact hc
  obtain ⟨Q, hQdeg, hQ⟩ := hO (fun t => P (bwpMat (z + t • v))) _ (C * M ^ (∑ i, a i)) (∑ i, a i) hB
    hdiff hbound
  exact ⟨Q, hQdeg, fun t ht => hQ t ht⟩

end ReciprocityTheory.MultiplicativeHeights
