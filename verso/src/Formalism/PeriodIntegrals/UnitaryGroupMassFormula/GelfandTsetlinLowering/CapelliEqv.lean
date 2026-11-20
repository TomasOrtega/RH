import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionA

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Simplify using `[embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem embGL_cc {n : ℕ} (g : GL (Fin n) ℂ) (i j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem embGL_lc {n : ℕ} (g : GL (Fin n) ℂ) (j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem embGL_cl {n : ℕ} (g : GL (Fin n) ℂ) (i : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem embGL_ll {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

def lmapPoly {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (p : Polynomial (MvPolynomial σ ℂ)) :
    Polynomial (MvPolynomial τ ℂ) :=
  ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.C (φ (p.coeff k)) * Polynomial.X ^ k

/- English proof (translation)
Simplify using `only [lmapPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hk`. Both sides reduce to the same expression. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), map_zero]`.
-/
theorem lmapPoly_coeff {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : Polynomial (MvPolynomial σ ℂ)) (k : ℕ) : (lmapPoly φ p).coeff k = φ (p.coeff k) := by
  simp only [lmapPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), map_zero]

/- English proof (translation)
Rewrite using `[Polynomial.eval_eq_sum_range (p := p), lmapPoly, Polynomial.eval_finsetSum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← C_pow]`. Rewrite using `[mul_comm (φ _), mul_comm (p.coeff i), ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]`.
-/
theorem lmapPoly_eval {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : Polynomial (MvPolynomial σ ℂ)) (t : ℂ) : (lmapPoly φ p).eval (C t) = φ (p.eval (C t)) := by
  rw [Polynomial.eval_eq_sum_range (p := p), lmapPoly, Polynomial.eval_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← C_pow]
  rw [mul_comm (φ _), mul_comm (p.coeff i), ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `hD : (1 + Matrix.single a a t) = Matrix.diagonal (fun i => if i = a then 1 + t else 1)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hia, Ne.symm hia]`.

Simplify using `[hij, Matrix.single_apply]`. Introduce `h1 h2`. Conclude with `absurd (h1.symm.trans h2) hij`. Rewrite using `[hD, Matrix.det_diagonal, Finset.prod_ite_eq']`. Simplify using `[add_comm]`.

Use `Matrix.det_transvection_of_ne a b hab t` as an intermediate fact. Unfold `Matrix.transvection at this`. Rewrite using `[this, if_neg hab]`.
-/
theorem det_one_add_single {n : ℕ} (a b : Fin n) (t : ℂ) :
    (1 + Matrix.single a b t).det = if a = b then t + 1 else 1 := by
  by_cases hab : a = b
  · subst hab
    have hD : (1 + Matrix.single a a t) = Matrix.diagonal (fun i => if i = a then 1 + t else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hia : i = a
        · subst hia; simp
        · simp [hia, Ne.symm hia]
      · simp [hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [hD, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp [add_comm]
  · have := Matrix.det_transvection_of_ne a b hab t
    unfold Matrix.transvection at this
    rw [this, if_neg hab]

/- English proof (translation)
Use extensionality with `i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp [Matrix.transpose_apply, embGL_ll, Matrix.single_apply]`.

Consider the case `cast j`. Simplify using `[Matrix.transpose_apply, embGL_cl, Matrix.one_apply]`. Conclude with `fun h => Fin.castSucc_ne_last j h.symm`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => simp [Matrix.transpose_apply, embGL_lc, Matrix.single_apply, Matrix.one_apply]`. Consider the case `cast j`. Rewrite using `[Matrix.transpose_apply, embGL_cc, hg]`. Simplify using `[Matrix.single_apply, Matrix.one_apply, eq_comm, and_comm]`.
-/
theorem embGL_transvec {n : ℕ} (g : GL (Fin n) ℂ) (a b : Fin n) (t : ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b t) :
    ((embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).transpose =
      1 + Matrix.single b.castSucc a.castSucc t := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_ll, Matrix.single_apply]
    | cast j =>
      simp [Matrix.transpose_apply, embGL_cl, Matrix.one_apply]
      exact fun h => Fin.castSucc_ne_last j h.symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_lc, Matrix.single_apply, Matrix.one_apply]
    | cast j =>
      rw [Matrix.transpose_apply, embGL_cc, hg]
      simp [Matrix.single_apply, Matrix.one_apply, eq_comm, and_comm]

/- English proof (translation)
Substitute `h` using the available equality. Establish `hι : ∀ x : Fin n, Fin.castLE (by omega : n ≤ n + 1) x = Fin.castSucc x` using `fun x => Fin.ext rfl`. Rewrite using `[hι a, hι b]`. Use `set d1 := mu.detShift with hd1`. Use `set d2 := lam.detShift with hd2`.

Use `set K : ℤ := |d1| + |d2| with hK`. Establish `hK1 : 0 ≤ d1 + K` using `by have := neg_abs_le d1; have := abs_nonneg d2; omega`. Establish `hK2 : 0 ≤ d2 + K` using `by have := neg_abs_le d2; have := abs_nonneg d1; omega`. Use `set e1 := (d1 + K).toNat with he1d`. Use `set e2 := (d2 + K).toNat with he2d`.

Establish `he1 : (e1 : ℤ) = d1 + K` using `Int.toNat_of_nonneg hK1`. Establish `he2 : (e2 : ℤ) = d2 + K` using `Int.toNat_of_nonneg hK2`. Use `set Q : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) := if a = b then Polynomial.X + 1 else 1 with hQ`. Use `set P := Q ^ e1 * lmapPoly φ (rowGen ℂ a b s) - Q ^ e2 * rowGen ℂ a.castSucc b.castSucc (φ s) with hP`. Establish `key : ∀ t : ℕ, P.eval (C (t : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ))`.

Introduce `t`. Rewrite using `[Submodule.mem_bot]`. Use `set D : ℂ := if a = b then (t : ℂ) + 1 else 1 with hD`. Set `g` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ (PI.WHw.det_one_add_single_ne a b t)`. Establish `hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (t : ℂ)` using `rfl`.

Establish `hgT : (g : Matrix (Fin n) (Fin n) ℂ).transpose = 1 + Matrix.single b a (t : ℂ)`. Rewrite using `[hgv, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]`. Establish `hgT'` using `embGL_transvec g a b t hgv`. Establish `hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = D`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hgv, det_one_add_single]`.

Establish `hu' : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) : ℂˣ) : ℂ) = D`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hgT', det_one_add_single]`. Break down `eq_or_ne a b with hab | hab` into its components or cases. Substitute `hab` using the available equality. Simplify using `[hD]`.

Simplify using `[hD, hab, Ne.symm hab]`. Establish `huu : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g` using `Units.ext (hu'.trans hu.symm)`. Establish `heq` using `hφ.2 g s hs`. Unfold `sqAct detPow at heq`. Rewrite `heq` using `[hgT, hgT', huu, map_smul, ← PI.WHw.eval_rowGen, ← PI.WHw.eval_rowGen]`.

Use `set u := Matrix.GeneralLinearGroup.det g`. Establish `heq2` using `congrArg (fun x => ((u ^ K : ℂˣ) : ℂ) • x) heq`. Simplify using `only [smul_smul, ← Units.val_mul, ← zpow_add] at heq2`. Rewrite `heq2` using `[show K + mu.detShift = (e1 : ℤ) by omega, show K + lam.detShift = (e2 : ℤ) by omega, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]`. Establish `hQe : Q.eval (C (t : ℂ)) = C D`.

Apply the tactic sequence `rw [hQ, hD]; split_ifs <;> simp`. Rewrite using `[hP, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow, hQe, lmapPoly_eval, ← C_pow, ← C_pow, ← smul_eq_C_mul, ← smul_eq_C_mul, heq2, sub_self]`. Establish `h1` using `PI.WHw.coeff_mem_of_eval ⊥ P key 1`. Rewrite `h1` using `[Submodule.mem_bot]`. Establish `hL0 : (lmapPoly φ (rowGen ℂ a b s)).coeff 0 = φ s`.

Rewrite using `[lmapPoly_coeff, rowGen_coeff_zero]`. Establish `hL1 : (lmapPoly φ (rowGen ℂ a b s)).coeff 1 = φ (pol ℂ a b s)`. Rewrite using `[lmapPoly_coeff, pol_eq_rowDiv]`. Both sides reduce to the same expression. Establish `hG0 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 0 = φ s` using `rowGen_coeff_zero ℂ _ _ _`.

Establish `hG1 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 1 = pol ℂ a.castSucc b.castSucc (φ s)`. Rewrite using `[pol_eq_rowDiv]`. Both sides reduce to the same expression. Establish `hc1 : ∀ (e : ℕ) (F : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)), (Q ^ e * F).coeff 1 = F.coeff 1 + (if a = b then (e : MvPolynomial _ ℂ) * F.coeff 0 else 0)`. Introduce `e F`.

Rewrite using `[hQ]`. Use `split_ifs with hab`. Rewrite using `[Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_add_one_pow]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite `h1` using `[hP, Polynomial.coeff_sub, hc1, hc1, hL0, hL1, hG0, hG1]`. Distinguish the cases in `hab : a = b`. Simplify using `only [hab, if_true] at h1 ⊢`. Establish `c1 : ((e1 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d1 : ℂ) + (K : ℂ))`. Rewrite using `[← map_natCast C]`.

Use `congr 1`. Conclude with `he1` after adjusting the coercions. Establish `c2 : ((e2 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d2 : ℂ) + (K : ℂ))`. Rewrite using `[← map_natCast C]`. Use `congr 1`.

Conclude with `he2` after adjusting the coercions. Rewrite `h1` using `[c1, c2, map_add, map_add]`. Rewrite using `[smul_eq_C_mul, smul_eq_C_mul]`. Substitute `hab` using the available equality. Take the linear combination `h1`.

Simplify using `only [hab, if_false, add_zero] at h1 ⊢`. Conclude with `sub_eq_zero.mp h1`.
-/
theorem eqv_pol {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (a b : Fin n) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    φ (pol ℂ a b s) + (if a = b then (mu.detShift : ℂ) • φ s else 0) =
      pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) (φ s) +
        (if a = b then (lam.detShift : ℂ) • φ s else 0) := by
  subst h
  have hι : ∀ x : Fin n, Fin.castLE (by omega : n ≤ n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  rw [hι a, hι b]
  set d1 := mu.detShift with hd1
  set d2 := lam.detShift with hd2
  set K : ℤ := |d1| + |d2| with hK
  have hK1 : 0 ≤ d1 + K := by have := neg_abs_le d1; have := abs_nonneg d2; omega
  have hK2 : 0 ≤ d2 + K := by have := neg_abs_le d2; have := abs_nonneg d1; omega
  set e1 := (d1 + K).toNat with he1d
  set e2 := (d2 + K).toNat with he2d
  have he1 : (e1 : ℤ) = d1 + K := Int.toNat_of_nonneg hK1
  have he2 : (e2 : ℤ) = d2 + K := Int.toNat_of_nonneg hK2
  set Q : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :=
    if a = b then Polynomial.X + 1 else 1 with hQ
  set P := Q ^ e1 * lmapPoly φ (rowGen ℂ a b s) - Q ^ e2 * rowGen ℂ a.castSucc b.castSucc (φ s) with hP
  have key : ∀ t : ℕ, P.eval (C (t : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro t
    rw [Submodule.mem_bot]
    set D : ℂ := if a = b then (t : ℂ) + 1 else 1 with hD
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (PI.WHw.det_one_add_single_ne a b t)
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (t : ℂ) := rfl
    have hgT : (g : Matrix (Fin n) (Fin n) ℂ).transpose = 1 + Matrix.single b a (t : ℂ) := by
      rw [hgv, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have hgT' := embGL_transvec g a b t hgv
    have hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, det_one_add_single]
    have hu' : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hgT', det_one_add_single]
      rcases eq_or_ne a b with hab | hab
      · subst hab; simp [hD]
      · simp [hD, hab, Ne.symm hab]
    have huu : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g :=
      Units.ext (hu'.trans hu.symm)
    have heq := hφ.2 g s hs
    unfold sqAct detPow at heq
    rw [hgT, hgT', huu, map_smul, ← PI.WHw.eval_rowGen, ← PI.WHw.eval_rowGen] at heq
    set u := Matrix.GeneralLinearGroup.det g
    have heq2 := congrArg (fun x => ((u ^ K : ℂˣ) : ℂ) • x) heq
    simp only [smul_smul, ← Units.val_mul, ← zpow_add] at heq2
    rw [show K + mu.detShift = (e1 : ℤ) by omega, show K + lam.detShift = (e2 : ℤ) by omega,
      zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu] at heq2
    have hQe : Q.eval (C (t : ℂ)) = C D := by
      rw [hQ, hD]; split_ifs <;> simp
    rw [hP, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, hQe, lmapPoly_eval, ← C_pow, ← C_pow, ← smul_eq_C_mul, ← smul_eq_C_mul, heq2, sub_self]
  have h1 := PI.WHw.coeff_mem_of_eval ⊥ P key 1
  rw [Submodule.mem_bot] at h1
  have hL0 : (lmapPoly φ (rowGen ℂ a b s)).coeff 0 = φ s := by
    rw [lmapPoly_coeff, rowGen_coeff_zero]
  have hL1 : (lmapPoly φ (rowGen ℂ a b s)).coeff 1 = φ (pol ℂ a b s) := by
    rw [lmapPoly_coeff, pol_eq_rowDiv]; rfl
  have hG0 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 0 = φ s := rowGen_coeff_zero ℂ _ _ _
  have hG1 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 1 = pol ℂ a.castSucc b.castSucc (φ s) := by
    rw [pol_eq_rowDiv]; rfl
  have hc1 : ∀ (e : ℕ) (F : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)),
      (Q ^ e * F).coeff 1 = F.coeff 1 + (if a = b then (e : MvPolynomial _ ℂ) * F.coeff 0 else 0) := by
    intro e F
    rw [hQ]
    split_ifs with hab
    · rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_add_one_pow]
      simp
    · simp
  rw [hP, Polynomial.coeff_sub, hc1, hc1, hL0, hL1, hG0, hG1] at h1
  by_cases hab : a = b
  · simp only [hab, if_true] at h1 ⊢
    have c1 : ((e1 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d1 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he1
    have c2 : ((e2 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d2 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he2
    rw [c1, c2, map_add, map_add] at h1
    rw [smul_eq_C_mul, smul_eq_C_mul]
    subst hab
    linear_combination h1
  · simp only [hab, if_false, add_zero] at h1 ⊢
    exact sub_eq_zero.mp h1

end PI.WGL
