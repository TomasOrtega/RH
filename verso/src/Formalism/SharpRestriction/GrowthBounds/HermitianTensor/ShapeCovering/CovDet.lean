import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.StatementY

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

/- English proof (translation)
Rewrite using `[Matrix.adjugate_fin_succ_eq_det_submatrix]`. Simplify using `only [Fin.val_zero, add_zero, Fin.succAbove_zero]`. Both sides reduce to the same expression.
-/
private theorem cvd_adj {B : Type*} [CommRing B] {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (i : Fin (m + 1)) :
    M.adjugate 0 i = (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => M (i.succAbove a) b.succ) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, Fin.succAbove_zero]
  rfl

private def cvdM (K : Type) [Field K] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  fun a b => Fin.cases 0 (fun b' : Fin m => X (a, b'.castSucc)) b

/- English proof (translation)
Rewrite using `[cvd_adj]`. Simplify using `only [covY]`. Use `congr 2`.
-/
private theorem cvd_covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    covY K m i = (cvdM K m).adjugate 0 i := by
  rw [cvd_adj]
  simp only [covY]
  congr 2

/- English proof (translation)
Introduce `K _ m g i`. Establish `hM : (rowAct K (n` using `m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix (cvdM K m) = g.map C * cvdM K m := by`. Use extensionality with `a b`. Use `Fin.cases ?_ (fun b' => ?_) b` and prove the remaining obligations. Simplify using `[cvdM, Matrix.mul_apply]`.

Simplify using `[cvdM, Matrix.mul_apply, rowAct]`. Rewrite using `[cvd_covY]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.adjugate_mul_distrib]`. Use `_ = ∑ j, C (g.adjugate j i) * covY K m j := by`.

Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← cvd_covY, mul_comm]`. Use `congr 1`. Rewrite using `[show g.map C = (C : K →+* MvPolynomial (Fin (m + 1) × Fin (m + 1)) K).mapMatrix g from rfl, ← RingHom.map_adjugate]`.

Both sides reduce to the same expression.
-/
theorem signed_minors_cofactor_adjugate : CovL5adj := by
  intro K _ m g i
  have hM : (rowAct K (n := m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix (cvdM K m)
      = g.map C * cvdM K m := by
    ext a b
    refine Fin.cases ?_ (fun b' => ?_) b
    · simp [cvdM, Matrix.mul_apply]
    · simp [cvdM, Matrix.mul_apply, rowAct]
  rw [cvd_covY]
  calc rowAct K g ((cvdM K m).adjugate 0 i)
      = ((rowAct K (n := m + 1) g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →+* _).mapMatrix
          (cvdM K m).adjugate) 0 i := rfl
    _ = (g.map C * cvdM K m).adjugate 0 i := by rw [RingHom.map_adjugate, hM]
    _ = (((cvdM K m).adjugate * (g.map C).adjugate :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) 0 i) := by
        rw [Matrix.adjugate_mul_distrib]
    _ = ∑ j, C (g.adjugate j i) * covY K m j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← cvd_covY, mul_comm]
      congr 1
      rw [show g.map C = (C : K →+* MvPolynomial (Fin (m + 1) × Fin (m + 1)) K).mapMatrix g from rfl,
        ← RingHom.map_adjugate]
      rfl

/- English proof (translation)
Introduce `K _ m g i hg`. Rewrite using `[signed_minors_cofactor_adjugate K m g i, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← C_mul, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, Ring.mul_inverse_cancel _ hg, one_mul]`.
-/
theorem signed_minors_cofactor_transform : SignedMinorsCofactorTransform := by
  intro K _ m g i hg
  rw [signed_minors_cofactor_adjugate K m g i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← C_mul, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
    Ring.mul_inverse_cancel _ hg, one_mul]

private def cvdN {F : Type*} [Field F] {k : ℕ} (z : Fin (k + 2) → F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F :=
  fun i j => if i = 0 then z j else if i = j then (if i = 1 then (z 0)⁻¹ else 1) else 0

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Rewrite using `[Fin.prod_univ_succ, Fin.prod_univ_succ]`. Simplify using `[cvdN, Fin.succ_ne_zero, Fin.succ_succ_ne_one, h0]`. Introduce `i j hij`. Establish `h1 : i ≠ 0`.

Introduce and unpack `rfl`. Conclude with `absurd hij (Fin.not_lt_zero _)`. Establish `h2 : i ≠ j` using `ne_of_gt hij`. Simplify using `[cvdN, h1, h2]`.
-/
private theorem cvdN_det {F : Type*} [Field F] {k : ℕ} (z : Fin (k + 2) → F) (h0 : z 0 ≠ 0) :
    (cvdN z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [cvdN, Fin.succ_ne_zero, Fin.succ_succ_ne_one, h0]
  · intro i j hij
    have h1 : i ≠ 0 := by
      rintro rfl
      exact absurd hij (Fin.not_lt_zero _)
    have h2 : i ≠ j := ne_of_gt hij
    simp [cvdN, h1, h2]

/- English proof (translation)
Introduce `K _ m hm`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Set `L` to `FractionRing (MvPolynomial (Fin (k + 1 + 1)) K)`. Set `ι : MvPolynomial (Fin (k + 1 + 1)) K →ₐ[K] L` to `IsScalarTower.toAlgHom K _ L`. Establish `hι : Function.Injective ι` using `IsFractionRing.injective _ _`.

Set `z : Fin (k + 1 + 1) → L` to `fun i => ι (X i)`. Establish `hz : AlgebraicIndependent K z` using `(MvPolynomial.algebraicIndependent_X _ _ : AlgebraicIndependent K (X : Fin (k + 1 + 1) → MvPolynomial (Fin (k + 1 + 1)) K)).map' hι`. Establish `hz0 : z 0 ≠ 0` using `(map_ne_zero_iff ι hι).mpr (MvPolynomial.X_ne_zero (R := K) (0 : Fin (k + 1 + 1)))`. Set `N` to `cvdN z`. Establish `hN : N.det = 1` using `cvdN_det z hz0`.

Set `Q` to `N⁻¹`. Establish `hQ : Q.adjugate = N`. Establish `h1 : N * Q = 1` using `Matrix.mul_nonsing_inv N (by rw [hN]; exact isUnit_one)`. Establish `h2 : Q * Q.adjugate = 1`. Rewrite using `[Matrix.mul_adjugate, Matrix.det_nonsing_inv, hN, Ring.inverse_one, one_smul]`.

Combine the equalities or inequalities in the displayed calculation. Set `f : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K →ₐ[K] L` to `aeval fun v => Fin.lastCases 0 (fun b : Fin (k + 1) => Q v.1 b.succ) v.2`. Apply `AlgebraicIndependent.of_comp f` to reduce the goal to its premises. Use `hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Use `show f (covY K (k + 1) i) = z i`. Establish `hzi : Q.adjugate 0 i = z i`. Rewrite using `[hQ]`. Simplify using `[N, cvdN]`. Rewrite using `[← hzi, cvd_adj]`.

Simplify using `only [covY, map_mul, map_pow, map_neg, map_one]`. Use `congr 1`. Use `(AlgHom.map_det f (Matrix.of fun a b : Fin (k + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K))).trans ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[f]`.
-/
theorem signed_minors_alg_independent : SignedMinorsAlgIndependent := by
  intro K _ m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let L := FractionRing (MvPolynomial (Fin (k + 1 + 1)) K)
  let ι : MvPolynomial (Fin (k + 1 + 1)) K →ₐ[K] L := IsScalarTower.toAlgHom K _ L
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let z : Fin (k + 1 + 1) → L := fun i => ι (X i)
  have hz : AlgebraicIndependent K z := (MvPolynomial.algebraicIndependent_X _ _ :
    AlgebraicIndependent K (X : Fin (k + 1 + 1) → MvPolynomial (Fin (k + 1 + 1)) K)).map' hι
  have hz0 : z 0 ≠ 0 := (map_ne_zero_iff ι hι).mpr (MvPolynomial.X_ne_zero (R := K) (0 : Fin (k + 1 + 1)))
  let N := cvdN z
  have hN : N.det = 1 := cvdN_det z hz0
  let Q := N⁻¹
  have hQ : Q.adjugate = N := by
    have h1 : N * Q = 1 := Matrix.mul_nonsing_inv N (by rw [hN]; exact isUnit_one)
    have h2 : Q * Q.adjugate = 1 := by
      rw [Matrix.mul_adjugate, Matrix.det_nonsing_inv, hN, Ring.inverse_one, one_smul]
    calc Q.adjugate = (N * Q) * Q.adjugate := by rw [h1, one_mul]
      _ = N := by rw [mul_assoc, h2, mul_one]
  let f : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K →ₐ[K] L :=
    aeval fun v => Fin.lastCases 0 (fun b : Fin (k + 1) => Q v.1 b.succ) v.2
  apply AlgebraicIndependent.of_comp f
  convert hz using 1
  funext i
  show f (covY K (k + 1) i) = z i
  have hzi : Q.adjugate 0 i = z i := by
    rw [hQ]
    simp [N, cvdN]
  rw [← hzi, cvd_adj]
  simp only [covY, map_mul, map_pow, map_neg, map_one]
  congr 1
  refine (AlgHom.map_det f (Matrix.of fun a b : Fin (k + 1) =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K))).trans ?_
  congr 1
  ext a b
  simp [f]

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
