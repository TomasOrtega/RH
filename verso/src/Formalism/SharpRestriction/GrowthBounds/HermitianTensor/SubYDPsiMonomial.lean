import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Unfold `midOf`. Rewrite using `[dif_neg]`. Simplify using the standard rewrite rules.
-/
theorem midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dif_neg]
  simp

/- English proof (translation)
Simplify using `only [subY, aeval_X, midOf_zero]`.
-/
theorem subY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) : subY A r (X (a, 0)) = X (a, 0) := by
  simp only [subY, aeval_X, midOf_zero]

/- English proof (translation)
Simplify using `only [subY, aeval_X, midOf_midI]`.
-/
theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

def dOneY (A : Type) [CommRing A] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) :=
  fun s t => Fin.cases (Fin.cases 1 (fun _ => 0) t) (fun s' => Fin.cases 0 (fun t' => C (X (s', t'))) t) s

/- English proof (translation)
Rewrite using `[Matrix.det_succ_column_zero, Fin.sum_univ_succ]`. Establish `h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0` using `fun i => rfl`. Establish `h1 : dOneY A r 0 0 = 1` using `rfl`. Simplify using `only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]`. Unfold `detY`.

Establish `h` using `RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+* MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))`. Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Use `congr 1`.
-/
theorem det_dOneY (A : Type) [CommRing A] (r : ℕ) : (dOneY A r).det = C (detY A r) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0 := fun i => rfl
  have h1 : dOneY A r 0 0 = 1 := rfl
  simp only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  unfold detY
  have h := RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+*
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A))
    (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine Eq.trans ?_ h.symm
  congr 1

/- English proof (translation)
Unfold `covY`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]`. Establish `hA` using `AlgHom.map_det (subY K r) (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))`. Establish `hB` using `RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K)) (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))`. Establish `hM : (subY K r).mapMatrix (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) = (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : Mv …`.

Apply `Matrix.ext` to reduce the goal to its premises. Introduce `a b`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_succ]`. Proceed by induction on `b using Fin.cases with`. Consider the case `zero`.

Establish `h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0` using `fun s => rfl`. Establish `h1 : dOneY K r 0 0 = 1` using `rfl`. Simplify using `only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]`. Use `show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))`. Rewrite using `[Fin.castSucc_zero, subY_X_zero, map_X]`.

Consider the case `succ j`. Establish `h0 : dOneY K r 0 j.succ = 0` using `rfl`. Establish `h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j))` using `fun s => rfl`. Simplify using `only [h0, h1, mul_zero, zero_add]`. Use `show subY K r (X (i.succAbove a, j.succ.castSucc)) = ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))`.

Establish `e : ∀ s : Fin r, s.succ.castSucc = midI r s` using `fun s => (Fin.succ_castSucc s).symm`. Simplify using `only [e, map_X]`. Rewrite using `[subY_X_mid]`. Conclude with `Finset.sum_congr rfl fun s _ => mul_comm _ _`. Establish `hdet : subY K r (Matrix.det fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) = C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) …`.

Use `hA.trans ?_` and prove the remaining obligations. Rewrite using `[hM, Matrix.det_mul, det_dOneY, mul_comm]`. Use `congr 1`. Conclude with `hB.symm`. Rewrite using `[hdet]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem subY_covY (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1 + 1)) :
    subY K r (covY K (r + 1) i) = C (detY K r) * map C (covY K (r + 1) i) := by
  unfold covY
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hA := AlgHom.map_det (subY K r)
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hB := RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K))
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hM : (subY K r).mapMatrix
      (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix
        (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) *
        dOneY K r := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    induction b using Fin.cases with
    | zero =>
      have h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0 := fun s => rfl
      have h1 : dOneY K r 0 0 = 1 := rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
      show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))
      rw [Fin.castSucc_zero, subY_X_zero, map_X]
    | succ j =>
      have h0 : dOneY K r 0 j.succ = 0 := rfl
      have h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j)) := fun s => rfl
      simp only [h0, h1, mul_zero, zero_add]
      show subY K r (X (i.succAbove a, j.succ.castSucc)) =
        ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))
      have e : ∀ s : Fin r, s.succ.castSucc = midI r s := fun s => (Fin.succ_castSucc s).symm
      simp only [e, map_X]
      rw [subY_X_mid]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hdet : subY K r (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) := by
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, det_dOneY, mul_comm]
    congr 1
    exact hB.symm
  rw [hdet]
  ring

/- English proof (translation)
Establish `hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0)`. Introduce `i`. Simplify using `[PsiXY, deltaB]`. Establish `hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i`. Introduce `i`.

Simplify using `only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]`. Establish `: (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id` using `rfl`. Rewrite using `[this, rename_id_apply]`. Rewrite using `[monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]`. Simplify using `only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]`.

Establish `hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c)))`. Simplify using `only [← algebraMap_eq, AlgHom.commutes]`. Simplify using `[algebraMap_eq]`. Rewrite using `[hC]`. Establish `hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v`.

Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression. Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem subY_dPsi_monomial (K : Type) [Field K] (r : ℕ) (v : XY (r + 1 + 1) →₀ ℕ) (c : K) :
    subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) =
      C (detY K r ^ yDeg v) * map C (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) := by
  have hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id := rfl
    rw [this, rename_id_apply]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]
  have hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) := by
    simp only [← algebraMap_eq, AlgHom.commutes]
    simp [algebraMap_eq]
  rw [hC]
  have hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  ring

/- English proof (translation)
Introduce `p n' R r hr P Q F hF`. Rewrite `hF` using `[← tie3 h2 h5 hCO R (r + 1) (by omega) P Q]`. Take `⟨f, hf, rfl⟩` from `hF`. Rewrite using `[dPsi_apply, f.as_sum]`. Simplify using `only [map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[subY_dPsi_monomial, (hf v hv).2]`.
-/
theorem subMuP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : SubMuP := by
  intro p n' R r hr P Q F hF
  rw [← tie3 h2 h5 hCO R (r + 1) (by omega) P Q] at hF
  obtain ⟨f, hf, rfl⟩ := hF
  rw [dPsi_apply, f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [subY_dPsi_monomial, (hf v hv).2]

end Formalism.MainNotions.flipOneThree.Pf

end
