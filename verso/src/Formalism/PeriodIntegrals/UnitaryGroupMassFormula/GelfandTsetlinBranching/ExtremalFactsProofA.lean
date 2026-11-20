import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

/- English proof (translation)
Establish `hN : 0 < N` using `lt_of_le_of_lt (Nat.zero_le _) i.isLt`. Establish `hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i` using `lam.anti (show i ≤ ⟨N - 1, by omega⟩ by rw [Fin.le_def]; simp; omega)`. Unfold `DomWeight.natW DomWeight.detShift`. Rewrite using `[dif_pos hN, Int.toNat_of_nonneg (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem natW_add_A {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) + lam.detShift = lam.w i := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i :=
    lam.anti (show i ≤ ⟨N - 1, by omega⟩ by rw [Fin.le_def]; simp; omega)
  unfold DomWeight.natW DomWeight.detShift
  rw [dif_pos hN, Int.toNat_of_nonneg (by omega)]
  ring

/- English proof (translation)
Introduce `i j hij`. Use `lam.anti hij` as an intermediate fact. Unfold `DomWeight.natW`. Conclude with `Int.toNat_le_toNat (by omega)`.
-/
theorem natW_anti_A {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

/- English proof (translation)
Unfold `sqAct`. Conclude with `Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n mu.natW _ s hs)`.
-/
theorem sqAct_mem_nabla_A (n : ℕ) (mu : DomWeight n) (g : GL (Fin n) ℂ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    sqAct ℂ n mu g s ∈ nablaSq ℂ n mu := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n mu.natW _ s hs)

/- English proof (translation)
Simplify using `[Formalism.GradedWeylDivisibility.rowAct]`.
-/
theorem rowAct_X_A {r n : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r × Fin n) :
    Formalism.GradedWeylDivisibility.rowAct ℂ M (X v) = ∑ b : Fin r, C (M v.1 b) * X (b, v.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[AlgHom.map_det, AlgHom.mapMatrix_apply]`. Establish `hmat : (Matrix.of fun p q : Fin s => (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ)).map (Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `n) M) = (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) : MvPolynomial (Fin n × Fin n) ℂ)) * Matrix.of fun p q : Fin s => (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ) := by`. Use extensionality with `p q`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]`.

Rewrite using `[rowAct_X_A]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hs))), Finset.sum_map]`. Both sides reduce to the same expression. Introduce `b _ hb`. Establish `hbs : s ≤ b.val`.

Assume the negation of the conclusion as `hlt`. Apply `hb` to reduce the goal to its premises. Conclude with `Finset.mem_map.mpr ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩`. Simplify using `only`. Rewrite using `[hM _ _ (by rw [Fin.lt_def]; simp; omega), map_zero, zero_mul]`.

Establish `hL : (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) : MvPolynomial (Fin n × Fin n) ℂ)).IsLowerTriangular`. Introduce `i j hij`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hM _ _ (by rw [Fin.lt_def]; simpa using hij), map_zero]`. Rewrite using `[hmat, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL]`.

Simplify using `[hd]`.
-/
theorem rowAct_lpMinor_A (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (s : ℕ) (hs : s ≤ n) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M (Formalism.GradedWeylDivisibility.lpMinor ℂ s hs hs) = Formalism.GradedWeylDivisibility.lpMinor ℂ s hs hs := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have hmat : (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ)).map
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M) =
      (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) ℂ)) *
      Matrix.of fun p q : Fin s => (X (Fin.castLE hs p, Fin.castLE hs q) : MvPolynomial (Fin n × Fin n) ℂ) := by
    ext p q
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    rw [rowAct_X_A]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hs))), Finset.sum_map]
    · rfl
    · intro b _ hb
      have hbs : s ≤ b.val := by
        by_contra hlt
        apply hb
        exact Finset.mem_map.mpr ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
      simp only
      rw [hM _ _ (by rw [Fin.lt_def]; simp; omega), map_zero, zero_mul]
  have hL : (Matrix.of fun p b : Fin s => (C (M (Fin.castLE hs p) (Fin.castLE hs b)) :
        MvPolynomial (Fin n × Fin n) ℂ)).IsLowerTriangular := by
    intro i j hij
    simp only [Matrix.of_apply]
    rw [hM _ _ (by rw [Fin.lt_def]; simpa using hij), map_zero]
  rw [hmat, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hL]
  simp [hd]

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.hw`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, rowAct_lpMinor_A n M hM hd]`.
-/
theorem rowAct_hw_A (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ i j, i < j → M i j = 0)
    (hd : ∀ i, M i i = 1) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) = Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν := by
  unfold Formalism.GradedWeylDivisibility.hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rowAct_lpMinor_A n M hM hd]

/- English proof (translation)
Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular]`. Simplify using `[hd]`. Introduce `i j hij`. Conclude with `hl i j hij`.
-/
theorem det_unitri_A (n : ℕ) (g : GL (Fin n) ℂ) (hl : ∀ i j, j < i → g i j = 0) (hd : ∀ i, g i i = 1) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular]
  · simp [hd]
  · intro i j hij
    exact hl i j hij

/- English proof (translation)
Introduce `n mu`. Use `⟨?_, ?_, fun g s hs => sqAct_mem_nabla_A n mu g s hs⟩` and prove the remaining obligations. Introduce `g hl hd`. Unfold `sqAct detPow extremal`. Rewrite using `[det_unitri_A n g hl hd, one_zpow, Units.val_one, one_smul]`.

Apply `rowAct_hw_A` to reduce the goal to its premises. Introduce `i j hij`. Simplify using `only [Matrix.transpose_apply]`. Conclude with `hl j i hij`. Introduce `i`.

Simplify using `only [Matrix.transpose_apply]`. Conclude with `hd i`. Introduce `t`. Unfold `sqAct detPow extremal`. Establish `hdiag : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = Matrix.diagonal fun a => (t a : ℂ)`.

Simplify using `[diagGL]`. Rewrite using `[hdiag, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ n n _ _ _ (Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl mu.natW (natW_anti_A mu)), smul_smul]`. Use `congr 1`. Establish `hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ n t) = ∏ a, t a`. Use `ext`.

Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, diagGL, Matrix.det_diagonal]`. Establish `hrow : ∀ a : Fin n, Formalism.GradedWeylDivisibility.rowNu (r` using `n) mu.natW a = mu.natW a := by`. Introduce `a`. Simplify using `[Formalism.GradedWeylDivisibility.rowNu]`. Simplify using `only [hrow, hdet]`.

Establish `key : (∏ a, t a) ^ mu.detShift * ∏ a, t a ^ ((mu.natW a : ℕ) : ℤ) = ∏ a, t a ^ mu.w a`. Rewrite using `[← Finset.prod_zpow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add, add_comm, natW_add_A]`. Rewrite using `[← key, Units.val_mul, Units.coe_prod]`.

Simplify using `[zpow_natCast]`.
-/
theorem extremalFacts_proof_A : ExtremalFacts := by
  intro n mu
  refine ⟨?_, ?_, fun g s hs => sqAct_mem_nabla_A n mu g s hs⟩
  · intro g hl hd
    unfold sqAct detPow extremal
    rw [det_unitri_A n g hl hd, one_zpow, Units.val_one, one_smul]
    apply rowAct_hw_A
    · intro i j hij
      simp only [Matrix.transpose_apply]
      exact hl j i hij
    · intro i
      simp only [Matrix.transpose_apply]
      exact hd i
  · intro t
    unfold sqAct detPow extremal
    have hdiag : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose =
        Matrix.diagonal fun a => (t a : ℂ) := by
      simp [diagGL]
    rw [hdiag, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ n n _ _ _
      (Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl mu.natW (natW_anti_A mu)), smul_smul]
    congr 1
    have hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ n t) = ∏ a, t a := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL, Matrix.det_diagonal]
    have hrow : ∀ a : Fin n, Formalism.GradedWeylDivisibility.rowNu (r := n) mu.natW a = mu.natW a := by
      intro a
      simp [Formalism.GradedWeylDivisibility.rowNu]
    simp only [hrow, hdet]
    have key : (∏ a, t a) ^ mu.detShift * ∏ a, t a ^ ((mu.natW a : ℕ) : ℤ) = ∏ a, t a ^ mu.w a := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← zpow_add, add_comm, natW_add_A]
    rw [← key, Units.val_mul, Units.coe_prod]
    simp [zpow_natCast]

/- English proof (translation)
The claim follows from `extremalFacts_proof_A`.
-/
theorem extremalFacts_of_A (_h : PI.HwIrred) : ExtremalFacts := extremalFacts_proof_A

end PI.WGB
