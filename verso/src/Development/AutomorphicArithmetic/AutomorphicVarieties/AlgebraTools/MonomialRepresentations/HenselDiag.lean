import Mathlib

open Polynomial Matrix

section
variable {C ι : Type} [CommRing C] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[← map_one (IsLocalRing.residue C).mapMatrix, ← sub_eq_zero, ← map_sub, ← Matrix.ext_iff]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]`.
-/
private theorem res_one [IsLocalRing C] (u : Matrix ι ι C) :
    (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ↔ (IsLocalRing.residue C).mapMatrix u = 1 := by
  rw [← map_one (IsLocalRing.residue C).mapMatrix, ← sub_eq_zero, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Conclude with `h ((IsLocalRing.residue_eq_zero_iff _).mpr hx)`.
-/
private theorem unit_of_res [IsLocalRing C] (x : C) (h : IsLocalRing.residue C x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h ((IsLocalRing.residue_eq_zero_iff _).mpr hx)

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, IsLocalRing.residue_eq_zero_iff, h i j hij]`.
-/
private theorem res_diag [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) :
    (IsLocalRing.residue C).mapMatrix M = diagonal fun i => IsLocalRing.residue C (M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, IsLocalRing.residue_eq_zero_iff, h i j hij]

/- English proof (translation)
Establish `hc : M.charpoly.map (IsLocalRing.residue C) = ∏ j, (X - Polynomial.C (IsLocalRing.residue C (M j j)))`. Rewrite using `[← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, res_diag M h, Matrix.charpoly_diagonal]`. Establish `h1 : M.charpoly.eval (M i i) ∈ IsLocalRing.maximalIdeal C`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hc, eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`.

Establish `h2 : IsUnit (M.charpoly.derivative.eval (M i i))`. Apply `unit_of_res` to reduce the goal to its premises. Rewrite using `[← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), derivative_mul]`. Simplify using `only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod]`. Use `Finset.prod_ne_zero_iff.mpr fun a ha => ?_` and prove the remaining obligations.

Rewrite using `[← map_sub]`. Conclude with `((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero`. Take `⟨d, hd, hd'⟩` from `HenselianLocalRing.is_henselian M.charpoly M.charpoly_monic (M i i) h1 h2`. Conclude with `⟨d, by rw [← Matrix.eval_charpoly]; exact hd, hd'⟩`.
-/
private theorem exists_root [HenselianLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι) :
    ∃ d : C, (Matrix.scalar ι d - M).det = 0 ∧ d - M i i ∈ IsLocalRing.maximalIdeal C := by
  have hc : M.charpoly.map (IsLocalRing.residue C) = ∏ j, (X - Polynomial.C (IsLocalRing.residue C (M j j))) := by
    rw [← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, res_diag M h, Matrix.charpoly_diagonal]
  have h1 : M.charpoly.eval (M i i) ∈ IsLocalRing.maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hc, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have h2 : IsUnit (M.charpoly.derivative.eval (M i i)) := by
    apply unit_of_res
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hc,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
    rw [← map_sub]
    exact ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨d, hd, hd'⟩ := HenselianLocalRing.is_henselian M.charpoly M.charpoly_monic (M i i) h1 h2
  exact ⟨d, by rw [← Matrix.eval_charpoly]; exact hd, hd'⟩

/- English proof (translation)
Establish `hdi : IsLocalRing.residue C d = IsLocalRing.residue C (M i i)`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hd'`. Use `set A := (Matrix.scalar ι d - M).adjugate with hA`. Establish `h0 : (Matrix.scalar ι d - M) * A = 0` using `by rw [hA, Matrix.mul_adjugate, hd, zero_smul]`.

Establish `h1 : (IsLocalRing.residue C).mapMatrix (Matrix.scalar ι d - M) = diagonal fun k => IsLocalRing.residue C (M i i - M k k)`. Rewrite using `[map_sub, res_diag M h]`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[hdi]`. Simplify using `[hab]`. Establish `h2 : (IsLocalRing.residue C).mapMatrix A = diagonal fun k => ∏ j ∈ Finset.univ.erase k, IsLocalRing.residue C (M i i - M j j)`. Rewrite using `[hA, RingHom.map_adjugate, h1, Matrix.adjugate_diagonal]`. Establish `h3 : IsUnit (A i i)`.

Apply `unit_of_res` to reduce the goal to its premises. Use `congrFun (congrFun h2 i) i` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]`. Rewrite using `[this]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun a ha => ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero`.

Take `⟨c, hc⟩` from `h3.exists_right_inv`. Use `⟨fun k => A k i * c, fun k => ?_, hc, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[sub_mul, sub_eq_zero]`. Use `congrFun (congrFun h0 k) i` as an intermediate fact. Rewrite `this` using `[Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply]`.

Simplify using `only [← mul_assoc]`. Rewrite using `[← Finset.sum_mul, ← this]`. Expand and normalize the polynomial expressions, which then agree. Use `congrFun (congrFun h2 k) i` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hk, IsLocalRing.residue_eq_zero_iff]`.

Conclude with `Ideal.mul_mem_right _ _ this`.
-/
private theorem exists_vec [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι)
    (d : C) (hd : (Matrix.scalar ι d - M).det = 0) (hd' : d - M i i ∈ IsLocalRing.maximalIdeal C) :
    ∃ v : ι → C, (∀ k, ∑ j, M k j * v j = v k * d) ∧ v i = 1 ∧ ∀ k, k ≠ i → v k ∈ IsLocalRing.maximalIdeal C := by
  have hdi : IsLocalRing.residue C d = IsLocalRing.residue C (M i i) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd'
  set A := (Matrix.scalar ι d - M).adjugate with hA
  have h0 : (Matrix.scalar ι d - M) * A = 0 := by rw [hA, Matrix.mul_adjugate, hd, zero_smul]
  have h1 : (IsLocalRing.residue C).mapMatrix (Matrix.scalar ι d - M) =
      diagonal fun k => IsLocalRing.residue C (M i i - M k k) := by
    rw [map_sub, res_diag M h]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdi]
    · simp [hab]
  have h2 : (IsLocalRing.residue C).mapMatrix A =
      diagonal fun k => ∏ j ∈ Finset.univ.erase k, IsLocalRing.residue C (M i i - M j j) := by
    rw [hA, RingHom.map_adjugate, h1, Matrix.adjugate_diagonal]
  have h3 : IsUnit (A i i) := by
    apply unit_of_res
    have := congrFun (congrFun h2 i) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at this
    rw [this]
    exact Finset.prod_ne_zero_iff.mpr fun a ha => ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨c, hc⟩ := h3.exists_right_inv
  refine ⟨fun k => A k i * c, fun k => ?_, hc, fun k hk => ?_⟩
  · rw [sub_mul, sub_eq_zero] at h0
    have := congrFun (congrFun h0 k) i
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply] at this
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, ← this]; ring
  · have := congrFun (congrFun h2 k) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hk,
      IsLocalRing.residue_eq_zero_iff] at this
    exact Ideal.mul_mem_right _ _ this

end

/- English proof (translation)
Introduce `C ι _ _ _ _ M h hu`. Use `choose d hd hd' using exists_root M h hu`. Use `choose v hv hv1 hv0 using fun i => exists_vec M h hu i (d i) (hd i) (hd' i)`. Set `u : Matrix ι ι C` to `Matrix.of fun k i => v i k`. Establish `hu1 : ∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C`.

Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[u, hv1]`. Simplify `hv0 j i hij` using `[u, hij]`.

Establish `hMu : M * u = u * diagonal d`. Use extensionality with `k i`. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Conclude with `hv i k`. Use `⟨u, d, hu1, hMu, hd', fun u' d' hu' hM' => ?_⟩` and prove the remaining obligations.

Establish `r1` using `(res_one u).mp hu1`. Establish `r2` using `(res_one u').mp hu'`. Establish `hdet : IsUnit u`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Apply `unit_of_res` to reduce the goal to its premises.

Rewrite using `[RingHom.map_det, r1, Matrix.det_one]`. Conclude with `one_ne_zero`. Take `⟨U, hU⟩` from `hdet`. Use `set w : Matrix ι ι C := (U⁻¹ : (Matrix ι ι C)ˣ) * u' with hw`. Establish `huw : u' = u * w` using `by rw [hw, ← hU, Units.mul_inv_cancel_left]`.

Establish `r3 : (IsLocalRing.residue C).mapMatrix w = 1`. Rewrite `r2` using `[huw, map_mul, r1, one_mul]`. Conclude with `r2`. Establish `hcomm : diagonal d * w = w * diagonal d'`. Rewrite `hM'` using `[huw, ← mul_assoc, hMu, mul_assoc, mul_assoc, ← hU]`.

Conclude with `(Units.mul_right_inj U).mp hM'`. Establish `he : ∀ i j, (d i - d' j) * w i j = 0`. Introduce `i j`. Use `congrFun (congrFun hcomm i) j` as an intermediate fact. Rewrite `this` using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Rewrite using `[sub_mul, this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd2 : ∀ j, IsLocalRing.residue C (d' j) = IsLocalRing.residue C (M j j)`. Introduce `j`. Use `congrArg (IsLocalRing.residue C).mapMatrix hM'` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul, r2, mul_one, one_mul]`. Use `congrFun (congrFun this j) j` as an intermediate fact. Simplify using `using this.symm`. Establish `hd1 : ∀ j, IsLocalRing.residue C (d j) = IsLocalRing.residue C (M j j)`. Introduce `j`.

Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hd' j`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `i`. Establish `hwi : IsUnit (w i i)`.

Apply `unit_of_res` to reduce the goal to its premises. Use `congrFun (congrFun r3 i) i` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq]`. Rewrite using `[this]`. Conclude with `one_ne_zero`.

Conclude with `(sub_eq_zero.mp (hwi.mul_left_eq_zero.mp (he i i))).symm`. Use `⟨fun i => w i i, ?_⟩` and prove the remaining obligations. Rewrite using `[huw]`. Use `congr 1`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`. Use `(unit_of_res (d i - d' j) ?_).mul_right_eq_zero.mp (he i j)` and prove the remaining obligations.

Rewrite using `[map_sub, hd1, hd2, ← map_sub]`. Conclude with `((hu i j hij).map _).ne_zero`.
-/
theorem UpperTheory.V.AlgebraTools.henselDiag :
    ∀ (C ι : Type) [CommRing C] [HenselianLocalRing C] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C),
      (∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) → (∀ i j, i ≠ j → IsUnit (M i i - M j j)) →
      ∃ (u : Matrix ι ι C) (d : ι → C), (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ∧ M * u = u * diagonal d ∧
        (∀ i, d i - M i i ∈ IsLocalRing.maximalIdeal C) ∧
        ∀ (u' : Matrix ι ι C) (d' : ι → C), (∀ i j, (u' - 1) i j ∈ IsLocalRing.maximalIdeal C) → M * u' = u' * diagonal d' →
          d' = d ∧ ∃ t : ι → C, u' = u * diagonal t := by
  intro C ι _ _ _ _ M h hu
  choose d hd hd' using exists_root M h hu
  choose v hv hv1 hv0 using fun i => exists_vec M h hu i (d i) (hd i) (hd' i)
  let u : Matrix ι ι C := Matrix.of fun k i => v i k
  have hu1 : ∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [u, hv1]
    · simpa [u, hij] using hv0 j i hij
  have hMu : M * u = u * diagonal d := by
    ext k i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    exact hv i k
  refine ⟨u, d, hu1, hMu, hd', fun u' d' hu' hM' => ?_⟩
  have r1 := (res_one u).mp hu1
  have r2 := (res_one u').mp hu'
  have hdet : IsUnit u := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply unit_of_res
    rw [RingHom.map_det, r1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hdet
  set w : Matrix ι ι C := (U⁻¹ : (Matrix ι ι C)ˣ) * u' with hw
  have huw : u' = u * w := by rw [hw, ← hU, Units.mul_inv_cancel_left]
  have r3 : (IsLocalRing.residue C).mapMatrix w = 1 := by
    rw [huw, map_mul, r1, one_mul] at r2; exact r2
  have hcomm : diagonal d * w = w * diagonal d' := by
    rw [huw, ← mul_assoc, hMu, mul_assoc, mul_assoc, ← hU] at hM'
    exact (Units.mul_right_inj U).mp hM'
  have he : ∀ i j, (d i - d' j) * w i j = 0 := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    rw [sub_mul, this]; ring
  have hd2 : ∀ j, IsLocalRing.residue C (d' j) = IsLocalRing.residue C (M j j) := by
    intro j
    have := congrArg (IsLocalRing.residue C).mapMatrix hM'
    rw [map_mul, map_mul, r2, mul_one, one_mul] at this
    have := congrFun (congrFun this j) j
    simpa using this.symm
  have hd1 : ∀ j, IsLocalRing.residue C (d j) = IsLocalRing.residue C (M j j) := by
    intro j
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd' j
  constructor
  · funext i
    have hwi : IsUnit (w i i) := by
      apply unit_of_res
      have := congrFun (congrFun r3 i) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq] at this
      rw [this]; exact one_ne_zero
    exact (sub_eq_zero.mp (hwi.mul_left_eq_zero.mp (he i i))).symm
  · refine ⟨fun i => w i i, ?_⟩
    rw [huw]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      refine (unit_of_res (d i - d' j) ?_).mul_right_eq_zero.mp (he i j)
      rw [map_sub, hd1, hd2, ← map_sub]
      exact ((hu i j hij).map _).ne_zero
