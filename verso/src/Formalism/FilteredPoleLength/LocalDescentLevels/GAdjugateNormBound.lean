import Formalism.FilteredPoleLength.ReducedBasisBounds.GFiniteOrderUnipotent

open scoped BigOperators
open Finset

namespace Formalism.LatticeBaseChangeAlt

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `hterm : ∀ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ x ^ n`. Introduce `σ`. Establish `hp : ‖∏ i, A (σ i) i‖ ≤ x ^ n`.

Rewrite using `[norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases. Rewrite using `[hs, one_smul]`. Conclude with `hp`.

Rewrite using `[hs, Units.neg_smul, one_smul, norm_neg]`. Conclude with `hp`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]`.
-/
private lemma norm_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (hx : ∀ i j, ‖A i j‖ ≤ x) : ‖A.det‖ ≤ n.factorial * x ^ n := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ x ^ n := by
    intro σ
    have hp : ‖∏ i, A (σ i) i‖ ≤ x ^ n := by
      rw [norm_prod]
      calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin n, x :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
        _ = x ^ n := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hp
    · rw [hs, Units.neg_smul, one_smul, norm_neg]
      exact hp
  calc ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin n), x ^ n := Finset.sum_le_sum fun σ _ => hterm σ
    _ = n.factorial * x ^ n := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/- English proof (translation)
Establish `htr : G.trace = (n : ℝ)`. Simplify using `[Matrix.trace, hd]`. Establish `hev : ∑ i, hG.1.eigenvalues i = (n : ℝ)`. Use `hG.1.trace_eq_sum_eigenvalues` as an intermediate fact. Rewrite `this` using `[htr]`.

Conclude with `this.symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_sub_distrib, hev]`. Simplify using the standard rewrite rules.
-/
private theorem det_le_one_of_posSemidef_of_diag_eq_one {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hd : ∀ j, G j j = 1) : G.det ≤ 1 := by
  have htr : G.trace = (n : ℝ) := by
    simp [Matrix.trace, hd]
  have hev : ∑ i, hG.1.eigenvalues i = (n : ℝ) := by
    have := hG.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    exact this.symm
  calc G.det = ∏ i, hG.1.eigenvalues i := hG.1.det_eq_prod_eigenvalues
    _ ≤ ∏ i, Real.exp (hG.1.eigenvalues i - 1) :=
        Finset.prod_le_prod (fun i _ => hG.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hG.1.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hG.1.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by
        rw [Finset.sum_sub_distrib, hev]
        simp

/- English proof (translation)
Introduce `n M`. Establish `hs0 : ∀ j, 0 ≤ ∑ i, M i j ^ 2` using `fun j => Finset.sum_nonneg fun i _ => sq_nonneg _`. Distinguish the cases in `hz : ∃ j, ∑ i, M i j ^ 2 = 0`. Take `⟨j, hj⟩` from `hz`. Establish `hcol : ∀ i, M i j = 0`.

Introduce `i`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (M i j))).mp hj i (Finset.mem_univ _)` as an intermediate fact. Conclude with `pow_eq_zero_iff two_ne_zero |>.mp this`. Rewrite using `[Matrix.det_eq_zero_of_column_eq_zero j hcol, abs_zero]`. Conclude with `Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _`.

Use `push_neg at hz`. Establish `hpos : ∀ j, 0 < ∑ i, M i j ^ 2` using `fun j => lt_of_le_of_ne (hs0 j) (Ne.symm (hz j))`. Take `⟨r, hr⟩ : ∃ r : Fin n → ℝ, r = fun j => Real.sqrt (∑ i, M i j ^ 2)` from `⟨_, rfl⟩`. Establish `hr0 : ∀ j, 0 < r j` using `fun j => by`. Rewrite using `[hr]`.

Conclude with `Real.sqrt_pos.mpr (hpos j)`. Establish `hrsq : ∀ j, r j ^ 2 = ∑ i, M i j ^ 2` using `fun j => by`. Rewrite using `[hr]`. Conclude with `Real.sq_sqrt (hpos j).le`. Take `⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℝ, N = M * Matrix.diagonal (fun j => (r j)⁻¹)` from `⟨_, rfl⟩`.

Establish `hNe : ∀ i j, N i j = M i j * (r j)⁻¹` using `fun i j => by`. Rewrite using `[hN, Matrix.mul_diagonal]`. Establish `hdiag : ∀ j, (N.conjTranspose * N) j j = 1`. Introduce `j`. Rewrite using `[Matrix.mul_apply]`.

Establish `e : ∀ x, N.conjTranspose j x * N x j = M x j ^ 2 / r j ^ 2` using `fun x => by`. Rewrite using `[Matrix.conjTranspose_apply, star_trivial, hNe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div, hrsq j]`. Conclude with `div_self (ne_of_gt (hpos j))`.

Establish `hdetG : (N.conjTranspose * N).det = N.det ^ 2`. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, sq]`. Establish `h1 : N.det ^ 2 ≤ 1`. Rewrite using `[← hdetG]`. Conclude with `det_le_one_of_posSemidef_of_diag_eq_one _ (Matrix.posSemidef_conjTranspose_mul_self N) hdiag`.

Establish `h1' : |N.det| ≤ 1` using `abs_le.mpr ⟨by nlinarith, by nlinarith⟩`. Establish `hP : 0 < ∏ j, r j` using `Finset.prod_pos fun j _ => hr0 j`. Establish `h2 : N.det = M.det / ∏ j, r j`. Rewrite using `[hN, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_inv_distrib, div_eq_mul_inv]`. Rewrite `h1'` using `[h2, abs_div, abs_of_pos hP, div_le_one hP]`.

Establish `h3 : ∏ j, r j = ∏ j, Real.sqrt (∑ i, M i j ^ 2)`. Rewrite using `[hr]`. Rewrite using `[← h3]`. Conclude with `h1'`.
-/
theorem gHadamard : GHadamard := by
  intro n M
  have hs0 : ∀ j, 0 ≤ ∑ i, M i j ^ 2 := fun j => Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hz : ∃ j, ∑ i, M i j ^ 2 = 0
  · obtain ⟨j, hj⟩ := hz
    have hcol : ∀ i, M i j = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (M i j))).mp hj i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    rw [Matrix.det_eq_zero_of_column_eq_zero j hcol, abs_zero]
    exact Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  push_neg at hz
  have hpos : ∀ j, 0 < ∑ i, M i j ^ 2 := fun j => lt_of_le_of_ne (hs0 j) (Ne.symm (hz j))
  obtain ⟨r, hr⟩ : ∃ r : Fin n → ℝ, r = fun j => Real.sqrt (∑ i, M i j ^ 2) := ⟨_, rfl⟩
  have hr0 : ∀ j, 0 < r j := fun j => by
    rw [hr]
    exact Real.sqrt_pos.mpr (hpos j)
  have hrsq : ∀ j, r j ^ 2 = ∑ i, M i j ^ 2 := fun j => by
    rw [hr]
    exact Real.sq_sqrt (hpos j).le
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℝ,
      N = M * Matrix.diagonal (fun j => (r j)⁻¹) := ⟨_, rfl⟩
  have hNe : ∀ i j, N i j = M i j * (r j)⁻¹ := fun i j => by
    rw [hN, Matrix.mul_diagonal]
  have hdiag : ∀ j, (N.conjTranspose * N) j j = 1 := by
    intro j
    rw [Matrix.mul_apply]
    have e : ∀ x, N.conjTranspose j x * N x j = M x j ^ 2 / r j ^ 2 := fun x => by
      rw [Matrix.conjTranspose_apply, star_trivial, hNe]
      ring
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div, hrsq j]
    exact div_self (ne_of_gt (hpos j))
  have hdetG : (N.conjTranspose * N).det = N.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, sq]
  have h1 : N.det ^ 2 ≤ 1 := by
    rw [← hdetG]
    exact det_le_one_of_posSemidef_of_diag_eq_one _ (Matrix.posSemidef_conjTranspose_mul_self N)
      hdiag
  have h1' : |N.det| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hP : 0 < ∏ j, r j := Finset.prod_pos fun j _ => hr0 j
  have h2 : N.det = M.det / ∏ j, r j := by
    rw [hN, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_inv_distrib, div_eq_mul_inv]
  rw [h2, abs_div, abs_of_pos hP, div_le_one hP] at h1'
  have h3 : ∏ j, r j = ∏ j, Real.sqrt (∑ i, M i j ^ 2) := by
    rw [hr]
  rw [← h3]
  exact h1'

end Formalism.LatticeBaseChangeAlt
