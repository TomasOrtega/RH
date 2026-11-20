import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm

open GlobalTheory.Count Formalism.MainNotions.S Formalism.REAL Matrix NumberField
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.Count.Cartan

variable {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dOp_eq (g : Matrix (Fin n) (Fin n) ℂ) : dOp g = Real.log ‖g‖ := rfl

/- English proof (translation)
Establish `hc : A.charpoly = (diagonal (fun i => (d i : ℂ))).charpoly`. Rewrite using `[h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]`. Establish `hr : (diagonal (fun i => (d i : ℂ))).charpoly.roots = Multiset.map (fun i => (d i : ℂ)) Finset.univ.val`. Rewrite using `[Matrix.charpoly_diagonal, Polynomial.roots_prod]`. Simplify using the standard rewrite rules.

Simplify using `[Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]`. Establish `hm : Multiset.map (fun i => (hA.eigenvalues i : ℂ)) Finset.univ.val = Multiset.map (fun i => (d i : ℂ)) Finset.univ.val`. Rewrite using `[← hr, ← hc, hA.roots_charpoly_eq_eigenvalues]`. Both sides reduce to the same expression. Establish `hm' : Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val`.

Apply `Multiset.map_injective Complex.ofReal_injective` to reduce the goal to its premises. Simplify `hm` using `only [Multiset.map_map, Function.comp_def]`. Establish `h2` using `congrArg (fun s => (Multiset.map f s).sum) hm'`. Simplify using `only [Multiset.map_map, Function.comp_def] at h2`. Conclude with `h2`.
-/
theorem sum_eig {A U : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hU : Uᴴ * U = 1) (d : Fin n → ℝ)
    (h : A = U * diagonal (fun i => (d i : ℂ)) * Uᴴ) (f : ℝ → ℝ) :
    ∑ i, f (hA.eigenvalues i) = ∑ i, f (d i) := by
  have hc : A.charpoly = (diagonal (fun i => (d i : ℂ))).charpoly := by
    rw [h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hr : (diagonal (fun i => (d i : ℂ))).charpoly.roots =
      Multiset.map (fun i => (d i : ℂ)) Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hm : Multiset.map (fun i => (hA.eigenvalues i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => (d i : ℂ)) Finset.univ.val := by
    rw [← hr, ← hc, hA.roots_charpoly_eq_eigenvalues]
    rfl
  have hm' : Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    apply Multiset.map_injective Complex.ofReal_injective
    simpa only [Multiset.map_map, Function.comp_def] using hm
  have h2 := congrArg (fun s => (Multiset.map f s).sum) hm'
  simp only [Multiset.map_map, Function.comp_def] at h2
  exact h2

/- English proof (translation)
Use `⟨(hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Unitary.coe_star_mul_self _`. Conclude with `Unitary.coe_mul_star_self _`. Use `conv_lhs => rw [hX.spectral_theorem]`. Rewrite using `[Unitary.conjStarAlgAut_apply]`.

Both sides reduce to the same expression.
-/
theorem exists_diag {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      X = U * diagonal (fun i => (hX.eigenvalues i : ℂ)) * Uᴴ := by
  refine ⟨(hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩
  · exact Unitary.coe_star_mul_self _
  · exact Unitary.coe_mul_star_self _
  · conv_lhs => rw [hX.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl

/- English proof (translation)
Establish `hinv : U⁻¹ = Uᴴ` using `Matrix.inv_eq_left_inv hU`. Establish `hunit : IsUnit U` using `⟨⟨U, Uᴴ, hU', hU⟩, rfl⟩`. Establish `he : (NormedSpace.exp (fun i => (d i : ℂ)) : Fin n → ℂ) = fun i => ((Real.exp (d i) : ℝ) : ℂ)`. Rewrite using `[Pi.exp_def]`. Use function extensionality and compare the values at `i`.

Rewrite using `[Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]`. Rewrite using `[← hinv, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, he]`.
-/
theorem exp_diag {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) (d : Fin n → ℝ) :
    NormedSpace.exp (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) =
      U * diagonal (fun i => ((Real.exp (d i) : ℝ) : ℂ)) * Uᴴ := by
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hU', hU⟩, rfl⟩
  have he : (NormedSpace.exp (fun i => (d i : ℂ)) : Fin n → ℂ) =
      fun i => ((Real.exp (d i) : ℝ) : ℂ) := by
    rw [Pi.exp_def]
    funext i
    rw [Complex.ofReal_exp, Complex.exp_eq_exp_ℂ]
  rw [← hinv, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, he]

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]`. Simplify using `only [Complex.star_def, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma re_star_mul_self_eq_norm_sq' (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Simplify using `only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (re_star_mul_self_eq_norm_sq' _).symm`.
-/
theorem hs_eq_trace (X : Matrix (Fin n) (Fin n) ℂ) : hs X = (trace (Xᴴ * X)).re := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (re_star_mul_self_eq_norm_sq' _).symm

/- English proof (translation)
Establish `hDh : (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ))`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Complex.conj_ofReal]`.

Establish `h1 : (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)ᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) = U * (diagonal (fun i => (d i : ℂ)) * diagonal (fun i => (d i : ℂ))) * Uᴴ`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]`. Rewrite using `[hs_eq_trace, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.ofReal_mul, Complex.ofReal_re, sq]`.
-/
theorem hs_diag {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (d : Fin n → ℝ) :
    hs (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) = ∑ i, d i ^ 2 := by
  have hDh : (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  have h1 : (U * diagonal (fun i => (d i : ℂ)) * Uᴴ)ᴴ * (U * diagonal (fun i => (d i : ℂ)) * Uᴴ) =
      U * (diagonal (fun i => (d i : ℂ)) * diagonal (fun i => (d i : ℂ))) * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
  rw [hs_eq_trace, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]

/- English proof (translation)
The claim follows from `CStarRing.norm_mem_unitary_mul g hk`.
-/
theorem norm_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖k * g‖ = ‖g‖ := CStarRing.norm_mem_unitary_mul g hk

/- English proof (translation)
The claim follows from `CStarRing.norm_mul_mem_unitary g hk`.
-/
theorem norm_mul_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖g * k‖ = ‖g‖ := CStarRing.norm_mul_mem_unitary g hk

/- English proof (translation)
Take `⟨U, hU, hU', hXU⟩` from `exists_diag hX`. Establish `hkk : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk`. Establish `h2X : X + X = U * diagonal (fun i => ((2 * hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ` using `by conv_lhs => rw [hXU]`. Rewrite using `[← add_mul, ← mul_add, Matrix.diagonal_add]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = U * diagonal (fun i => ((Real.exp (2 * hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ`. Rewrite using `[Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hX.eq, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ, hkk, Matrix.one_mul, ← Matrix.exp_add_of_commute X X (Commute.refl X), h2X, exp_diag hU hU']`.

Establish `hs1` using `sum_eig (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hU _ hE (fun t => (Real.log t / 2) ^ 2)`. Use `beta_reduce at hs1`. Unfold `dHS`. Use `congr 1`. Rewrite using `[hs1]`.

Use `conv_rhs => rw [hXU]`. Rewrite using `[hs_diag hU]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dHS_polar {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hX : X.IsHermitian) : dHS (k * NormedSpace.exp X) = Real.sqrt (hs X) := by
  obtain ⟨U, hU, hU', hXU⟩ := exists_diag hX
  have hkk : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have h2X : X + X = U * diagonal (fun i => ((2 * hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hXU]
    rw [← add_mul, ← mul_add, Matrix.diagonal_add]
    congr 2
    funext i
    push_cast
    ring
  have hE : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) =
      U * diagonal (fun i => ((Real.exp (2 * hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hX.eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc kᴴ, hkk, Matrix.one_mul, ← Matrix.exp_add_of_commute X X (Commute.refl X),
      h2X, exp_diag hU hU']
  have hs1 := sum_eig (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hU _ hE
    (fun t => (Real.log t / 2) ^ 2)
  beta_reduce at hs1
  unfold dHS
  congr 1
  rw [hs1]
  conv_rhs => rw [hXU]
  rw [hs_diag hU]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_exp]
  ring

/- English proof (translation)
Establish `hkk : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk`. Establish `hk2 : k' * k'ᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hk'`. Take `⟨U, hU, hU', hMU⟩` from `exists_diag (Matrix.isHermitian_conjTranspose_mul_self g)`. Establish `h1 : (k * g * k')ᴴ * (k * g * k') = k'ᴴ * (gᴴ * g) * k'`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc kᴴ k, hkk, Matrix.one_mul]`. Establish `h2 : k'ᴴ * (gᴴ * g) * k' = (k'ᴴ * U) * diagonal (fun i => ((Matrix.isHermitian_conjTranspose_mul_self g).eigenvalues i : ℂ)) * (k'ᴴ * U)ᴴ` using `by conv_lhs => rw [hMU]`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hV : (k'ᴴ * U)ᴴ * (k'ᴴ * U) = 1`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc k', hk2, Matrix.one_mul, hU]`. Establish `e1` using `sum_eig (Matrix.isHermitian_conjTranspose_mul_self (k * g * k')) hV _ (h1.trans h2) (fun t => (Real.log t / 2) ^ 2)`. Unfold `dHS`. Conclude with `congrArg Real.sqrt e1`.
-/
theorem dHS_unitary {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hk' : k' ∈ Matrix.unitaryGroup (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    dHS (k * g * k') = dHS g := by
  have hkk : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hk2 : k' * k'ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hk'
  obtain ⟨U, hU, hU', hMU⟩ := exists_diag (Matrix.isHermitian_conjTranspose_mul_self g)
  have h1 : (k * g * k')ᴴ * (k * g * k') = k'ᴴ * (gᴴ * g) * k' := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᴴ k, hkk, Matrix.one_mul]
  have h2 : k'ᴴ * (gᴴ * g) * k' = (k'ᴴ * U) *
      diagonal (fun i => ((Matrix.isHermitian_conjTranspose_mul_self g).eigenvalues i : ℂ)) *
      (k'ᴴ * U)ᴴ := by
    conv_lhs => rw [hMU]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hV : (k'ᴴ * U)ᴴ * (k'ᴴ * U) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc k', hk2, Matrix.one_mul, hU]
  have e1 := sum_eig (Matrix.isHermitian_conjTranspose_mul_self (k * g * k')) hV _ (h1.trans h2)
    (fun t => (Real.log t / 2) ^ 2)
  unfold dHS
  exact congrArg Real.sqrt e1

/- English proof (translation)
Unfold `Matrix.rank`. Rewrite using `[Matrix.mulVecLin_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_add_le' (A B : Matrix (Fin n) (Fin n) ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule ℂ (Fin n → ℂ))) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/- English proof (translation)
Establish `hent : ∀ i j, ε i = ε j → X i j = 0`. Introduce `i j hij`. Establish `h` using `congrFun (congrFun hX.2 i) j`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h`. Rewrite `h` using `[hij]`.

Apply the tactic sequence `have hc : (if ε j = true then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Establish `h3 : (2 * (if ε j = true then (1 : ℂ) else -1)) * X i j = 0` using `by linear_combination h`. Break down `mul_eq_zero.mp h3 with h0 | h0` into its components or cases. Conclude with `absurd h0 (mul_ne_zero two_ne_zero hc)`. Conclude with `h0`.

Take `⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = diagonal fun a => if ε a = s then 1 else 0` from `⟨_, rfl⟩`. Take `⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q = diagonal fun a => if ε a = s then 0 else 1` from `⟨_, rfl⟩`. Establish `hPQ : P + Q = 1`. Rewrite using `[hP, hQ, Matrix.diagonal_add, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hXQ : X * Q = P * X * Q`. Use extensionality with `i j`. Simplify using `only [hP, hQ, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Distinguish the cases in `hj : ε j = s`. Simplify using `[hj]`. Distinguish the cases in `hi : ε i = s`. Simplify using `[hi, hj]`. Establish `hij : ε i = ε j` using `by revert hi hj`.

Apply the tactic sequence `cases ε i <;> cases ε j <;> cases s <;> simp`. Simplify using `[hi, hj, hent i j hij]`. Combine the equalities or inequalities in the displayed calculation. Use `add_le_add (Matrix.rank_mul_le_right _ _) ?_` and prove the remaining obligations. Rewrite using `[hXQ]`.

Conclude with `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)`. Use `_ = 2 * (Finset.univ.filter fun a => ε a = s).card := by`. Rewrite using `[← two_mul, hP, Matrix.rank_diagonal]`. Simplify using `[Fintype.card_subtype]`.
-/
theorem rank_le_of_inP {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (s : Bool) :
    X.rank ≤ 2 * (Finset.univ.filter fun a => ε a = s).card := by
  classical
  have hent : ∀ i j, ε i = ε j → X i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hX.2 i) j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h
    rw [hij] at h
    have hc : (if ε j = true then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have h3 : (2 * (if ε j = true then (1 : ℂ) else -1)) * X i j = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact absurd h0 (mul_ne_zero two_ne_zero hc)
    · exact h0
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ,
      P = diagonal fun a => if ε a = s then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ,
      Q = diagonal fun a => if ε a = s then 0 else 1 := ⟨_, rfl⟩
  have hPQ : P + Q = 1 := by
    rw [hP, hQ, Matrix.diagonal_add, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hXQ : X * Q = P * X * Q := by
    ext i j
    simp only [hP, hQ, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hj : ε j = s
    · simp [hj]
    · by_cases hi : ε i = s
      · simp [hi, hj]
      · have hij : ε i = ε j := by
          revert hi hj
          cases ε i <;> cases ε j <;> cases s <;> simp
        simp [hi, hj, hent i j hij]
  calc X.rank = (X * P + X * Q).rank := by rw [← mul_add, hPQ, mul_one]
    _ ≤ (X * P).rank + (X * Q).rank := rank_add_le' _ _
    _ ≤ P.rank + P.rank := by
        refine add_le_add (Matrix.rank_mul_le_right _ _) ?_
        rw [hXQ]
        exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)
    _ = 2 * (Finset.univ.filter fun a => ε a = s).card := by
        rw [← two_mul, hP, Matrix.rank_diagonal]
        simp [Fintype.card_subtype]

/- English proof (translation)
Unfold `rkR`. Break down `min_cases (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card with ⟨h, _⟩ | ⟨h, _⟩` into its components or cases. Rewrite using `[h]`. Conclude with `rank_le_of_inP hX true`. Rewrite using `[h]`.

Conclude with `rank_le_of_inP hX false`.
-/
theorem rank_le_rkR {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    X.rank ≤ 2 * rkR ε := by
  unfold rkR
  rcases min_cases (Finset.univ.filter fun a => ε a = true).card
      (Finset.univ.filter fun a => ε a = false).card with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact rank_le_of_inP hX true
  · rw [h]; exact rank_le_of_inP hX false

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Jm_conjTranspose, Jm_mul_self]`.
-/
theorem Jm_unitary (ε : Fin n → Bool) : Jm ε ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Jm_conjTranspose, Jm_mul_self]

/- English proof (translation)
Take `⟨U, hU, hU', hXU⟩` from `exists_diag hX`. Establish `hJ1 : Jm ε * Jm ε = 1` using `Jm_mul_self ε`. Establish `hJh : (Jm ε)ᴴ = Jm ε` using `Jm_conjTranspose ε`. Establish `hneg : -X = Jm ε * X * Jm ε`. Rewrite using `[Matrix.mul_assoc, hP.2, mul_neg, ← Matrix.mul_assoc, hJ1, Matrix.one_mul]`.

Establish `hXn : (-X).IsHermitian` using `hX.neg`. Establish `h1 : -X = (Jm ε * U) * diagonal (fun i => (hX.eigenvalues i : ℂ)) * (Jm ε * U)ᴴ`. Rewrite using `[hneg, Matrix.conjTranspose_mul, hJh]`. Use `conv_lhs => rw [hXU]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hV : (Jm ε * U)ᴴ * (Jm ε * U) = 1`. Rewrite using `[Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε) (Jm ε), hJ1, Matrix.one_mul, hU]`. Establish `h2 : -X = U * diagonal (fun i => ((-hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ` using `by conv_lhs => rw [hXU]`. Rewrite using `[← neg_mul, ← mul_neg, Matrix.diagonal_neg]`. Simplify using `only [Complex.ofReal_neg]`.

Establish `e1` using `sum_eig hXn hV _ h1 (fun t => if t = -hX.eigenvalues j then (1 : ℝ) else 0)`. Establish `e2` using `sum_eig hXn hU _ h2 (fun t => if t = -hX.eigenvalues j then (1 : ℝ) else 0)`. Use `beta_reduce at e1 e2`. Establish `key` using `e1.symm.trans e2`. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Establish `h0 : ∑ i, (if hX.eigenvalues i = -hX.eigenvalues j then (1 : ℝ) else 0) = 0` using `Finset.sum_eq_zero fun i _ => by simp [hne i]`. Apply the tactic sequence `have h3 : (if -hX.eigenvalues j = -hX.eigenvalues j then (1 : ℝ) else 0) ≤ ∑ i, (if -hX.eigenvalues i = -hX.eigenvalues j then (1 : ℝ) else 0) := Finset.single_le_sum (f := fun i => if -hX.eigenvalues i = -hX.eigenvalues j then (1 : ℝ) else 0) (fun i _ => by split_ifs <;> norm_nu …`. Rewrite `h3` using `[if_pos rfl]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_neg_eig {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hP : inP ε X)
    (hX : X.IsHermitian) (j : Fin n) : ∃ i, hX.eigenvalues i = -hX.eigenvalues j := by
  classical
  obtain ⟨U, hU, hU', hXU⟩ := exists_diag hX
  have hJ1 : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hneg : -X = Jm ε * X * Jm ε := by
    rw [Matrix.mul_assoc, hP.2, mul_neg, ← Matrix.mul_assoc, hJ1, Matrix.one_mul]
  have hXn : (-X).IsHermitian := hX.neg
  have h1 : -X = (Jm ε * U) * diagonal (fun i => (hX.eigenvalues i : ℂ)) * (Jm ε * U)ᴴ := by
    rw [hneg, Matrix.conjTranspose_mul, hJh]
    conv_lhs => rw [hXU]
    simp only [Matrix.mul_assoc]
  have hV : (Jm ε * U)ᴴ * (Jm ε * U) = 1 := by
    rw [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm ε) (Jm ε), hJ1,
      Matrix.one_mul, hU]
  have h2 : -X = U * diagonal (fun i => ((-hX.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hXU]
    rw [← neg_mul, ← mul_neg, Matrix.diagonal_neg]
    simp only [Complex.ofReal_neg]
  have e1 := sum_eig hXn hV _ h1 (fun t => if t = -hX.eigenvalues j then (1 : ℝ) else 0)
  have e2 := sum_eig hXn hU _ h2 (fun t => if t = -hX.eigenvalues j then (1 : ℝ) else 0)
  beta_reduce at e1 e2
  have key := e1.symm.trans e2
  by_contra hne
  push Not at hne
  have h0 : ∑ i, (if hX.eigenvalues i = -hX.eigenvalues j then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by simp [hne i]
  have h3 : (if -hX.eigenvalues j = -hX.eigenvalues j then (1 : ℝ) else 0) ≤
      ∑ i, (if -hX.eigenvalues i = -hX.eigenvalues j then (1 : ℝ) else 0) :=
    Finset.single_le_sum (f := fun i => if -hX.eigenvalues i = -hX.eigenvalues j then (1 : ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  rw [if_pos rfl] at h3
  linarith

/- English proof (translation)
Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Take `⟨j, -, hj⟩` from `Finset.exists_max_image Finset.univ hX.eigenvalues Finset.univ_nonempty`. Use `⟨j, ?_, fun i => hj i (Finset.mem_univ i)⟩` and prove the remaining obligations. Take `⟨U, hU, hU', hXU⟩` from `exists_diag hX`. Establish `hUu : U ∈ Matrix.unitaryGroup (Fin n) ℂ` using `Matrix.mem_unitaryGroup_iff'.mpr hU`.

Establish `hUhu : Uᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Conclude with `hU'`. Rewrite using `[dOp_eq, norm_unitary_mul hk]`. Use `conv_lhs => rw [hXU]`.

Rewrite using `[exp_diag hU hU', norm_mul_unitary hUhu, norm_unitary_mul hUu, Matrix.l2_opNorm_diagonal]`. Establish `hnorm : ∀ i, ‖((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)‖ = Real.exp (hX.eigenvalues i)`. Introduce `i`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]`. Establish `hsup : ‖(fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ))‖ = Real.exp (hX.eigenvalues j)`.

Apply `le_antisymm` to reduce the goal to its premises. Use `(pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun i => ?_` and prove the remaining obligations. Rewrite using `[hnorm]`. Conclude with `Real.exp_le_exp.mpr (hj i (Finset.mem_univ i))`. Use `norm_le_pi_norm (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) j` as an intermediate fact.

Rewrite `this` using `[hnorm]`. Then use the resulting hypothesis. Rewrite using `[hsup, Real.log_exp]`.
-/
theorem dOp_polar (hn : 1 ≤ n) {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hX : X.IsHermitian) : ∃ j, dOp (k * NormedSpace.exp X) = hX.eigenvalues j ∧
      ∀ i, hX.eigenvalues i ≤ hX.eigenvalues j := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ hX.eigenvalues Finset.univ_nonempty
  refine ⟨j, ?_, fun i => hj i (Finset.mem_univ i)⟩
  obtain ⟨U, hU, hU', hXU⟩ := exists_diag hX
  have hUu : U ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hU
  have hUhu : Uᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact hU'
  rw [dOp_eq, norm_unitary_mul hk]
  conv_lhs => rw [hXU]
  rw [exp_diag hU hU', norm_mul_unitary hUhu, norm_unitary_mul hUu, Matrix.l2_opNorm_diagonal]
  have hnorm : ∀ i, ‖((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)‖ = Real.exp (hX.eigenvalues i) := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have hsup : ‖(fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ))‖ = Real.exp (hX.eigenvalues j) := by
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun i => ?_
      rw [hnorm]
      exact Real.exp_le_exp.mpr (hj i (Finset.mem_univ i))
    · have := norm_le_pi_norm (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) j
      rwa [hnorm] at this
  rw [hsup, Real.log_exp]

/- English proof (translation)
Establish `hX : X.IsHermitian` using `hermitian_of_mem_hermitian_part hP`. Take `⟨j, hdj, hj⟩` from `dOp_polar hn hk hX`. Rewrite using `[hdj]`. Take `⟨j', hj'⟩` from `exists_neg_eig hP hX j`. Establish `habs : ∀ i, -hX.eigenvalues j ≤ hX.eigenvalues i ∧ hX.eigenvalues i ≤ hX.eigenvalues j`.

Introduce `i`. Take `⟨i', hi'⟩` from `exists_neg_eig hP hX i`. Use `hj i'` as an intermediate fact. Conclude with `⟨by linarith, hj i⟩`. Establish `h0 : 0 ≤ hX.eigenvalues j` using `by have := hj j'; linarith`.

Take `⟨U, hU, hU', hXU⟩` from `exists_diag hX`. Establish `hhs : hs X = ∑ i, hX.eigenvalues i ^ 2` using `by conv_lhs => rw [hXU]`. Conclude with `hs_diag hU _`. Use `⟨h0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hhs]`.

Break down `eq_or_lt_of_le h0 with h00 | hpos` into its components or cases. Rewrite using `[← h00, mul_zero]`. Conclude with `Real.sqrt_nonneg _`. Establish `hne : j' ≠ j`. Introduce `h`.

Rewrite `hj'` using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : 2 * hX.eigenvalues j ^ 2 ≤ ∑ i, hX.eigenvalues i ^ 2`. Establish `hsub : ({j, j'} : Finset (Fin n)) ⊆ Finset.univ` using `Finset.subset_univ _`. Use `Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => hX.eigenvalues i ^ 2) hsub (fun i _ _ => sq_nonneg _)` as an intermediate fact.

Rewrite `this` using `[Finset.sum_pair hne.symm, hj']`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (by norm_num), Real.sqrt_sq h0]`. Use `_ ≤ Real.sqrt (∑ i, hX.eigenvalues i ^ 2) := Real.sqrt_le_sqrt hsum`.

Rewrite using `[hhs]`. Establish `hcard : (Finset.univ.filter fun i => hX.eigenvalues i ≠ 0).card ≤ 2 * rkR ε`. Use `hX.rank_eq_card_non_zero_eigs` as an intermediate fact. Rewrite `this` using `[Fintype.card_subtype]`. Rewrite using `[← this]`.

Conclude with `rank_le_rkR hP`. Establish `hsum : ∑ i, hX.eigenvalues i ^ 2 ≤ (2 * (rkR ε : ℝ)) * hX.eigenvalues j ^ 2`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hi`.

Use `habs i` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `push Not at hi`. Rewrite using `[hi]`. Evaluate the numerical expressions.

Use `_ = ((Finset.univ.filter fun i => hX.eigenvalues i ≠ 0).card : ℝ) * hX.eigenvalues j ^ 2 := by`. Rewrite using `[Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero]`. Use `_ ≤ _ := by`. Apply `mul_le_mul_of_nonneg_right _ (sq_nonneg _)` to reduce the goal to its premises. Conclude with `hcard` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_mul (by positivity), Real.sqrt_sq h0]`.
-/
theorem dOp_bounds (hn : 1 ≤ n) {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hP : inP ε X) :
    0 ≤ dOp (k * NormedSpace.exp X) ∧
      Real.sqrt 2 * dOp (k * NormedSpace.exp X) ≤ Real.sqrt (hs X) ∧
      Real.sqrt (hs X) ≤ Real.sqrt (2 * rkR ε) * dOp (k * NormedSpace.exp X) := by
  classical
  have hX : X.IsHermitian := hermitian_of_mem_hermitian_part hP
  obtain ⟨j, hdj, hj⟩ := dOp_polar hn hk hX
  rw [hdj]
  obtain ⟨j', hj'⟩ := exists_neg_eig hP hX j
  have habs : ∀ i, -hX.eigenvalues j ≤ hX.eigenvalues i ∧ hX.eigenvalues i ≤ hX.eigenvalues j := by
    intro i
    obtain ⟨i', hi'⟩ := exists_neg_eig hP hX i
    have := hj i'
    exact ⟨by linarith, hj i⟩
  have h0 : 0 ≤ hX.eigenvalues j := by have := hj j'; linarith
  obtain ⟨U, hU, hU', hXU⟩ := exists_diag hX
  have hhs : hs X = ∑ i, hX.eigenvalues i ^ 2 := by
    conv_lhs => rw [hXU]
    exact hs_diag hU _
  refine ⟨h0, ?_, ?_⟩
  · rw [hhs]
    rcases eq_or_lt_of_le h0 with h00 | hpos
    · rw [← h00, mul_zero]; exact Real.sqrt_nonneg _
    · have hne : j' ≠ j := by
        intro h; rw [h] at hj'; linarith
      have hsum : 2 * hX.eigenvalues j ^ 2 ≤ ∑ i, hX.eigenvalues i ^ 2 := by
        have hsub : ({j, j'} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => hX.eigenvalues i ^ 2) hsub
          (fun i _ _ => sq_nonneg _)
        rw [Finset.sum_pair hne.symm, hj'] at this
        nlinarith
      calc Real.sqrt 2 * hX.eigenvalues j = Real.sqrt (2 * hX.eigenvalues j ^ 2) := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq h0]
        _ ≤ Real.sqrt (∑ i, hX.eigenvalues i ^ 2) := Real.sqrt_le_sqrt hsum
  · rw [hhs]
    have hcard : (Finset.univ.filter fun i => hX.eigenvalues i ≠ 0).card ≤ 2 * rkR ε := by
      have := hX.rank_eq_card_non_zero_eigs
      rw [Fintype.card_subtype] at this
      rw [← this]
      exact rank_le_rkR hP
    have hsum : ∑ i, hX.eigenvalues i ^ 2 ≤ (2 * (rkR ε : ℝ)) * hX.eigenvalues j ^ 2 := by
      calc ∑ i, hX.eigenvalues i ^ 2
          ≤ ∑ i, (if hX.eigenvalues i ≠ 0 then hX.eigenvalues j ^ 2 else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            split_ifs with hi
            · have := habs i; nlinarith
            · push Not at hi; rw [hi]; norm_num
        _ = ((Finset.univ.filter fun i => hX.eigenvalues i ≠ 0).card : ℝ) * hX.eigenvalues j ^ 2 := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact_mod_cast hcard
    calc Real.sqrt (∑ i, hX.eigenvalues i ^ 2)
        ≤ Real.sqrt ((2 * (rkR ε : ℝ)) * hX.eigenvalues j ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (2 * rkR ε) * hX.eigenvalues j := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h0]

/- English proof (translation)
Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Conclude with `norm_pos_iff.mpr hg.ne_zero`.
-/
theorem norm_pos_of_isUnit (hn : 1 ≤ n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) : 0 < ‖g‖ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact norm_pos_iff.mpr hg.ne_zero

/- English proof (translation)
Rewrite using `[dOp_eq, dOp_eq, dOp_eq, ← Real.log_mul (norm_pos_of_isUnit hn hg).ne' (norm_pos_of_isUnit hn hg').ne']`. Conclude with `Real.log_le_log (norm_pos_of_isUnit hn (hg.mul hg')) (norm_mul_le _ _)`.
-/
theorem dOp_mul_le (hn : 1 ≤ n) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (hg' : IsUnit g') :
    dOp (g * g') ≤ dOp g + dOp g' := by
  rw [dOp_eq, dOp_eq, dOp_eq, ← Real.log_mul (norm_pos_of_isUnit hn hg).ne'
    (norm_pos_of_isUnit hn hg').ne']
  exact Real.log_le_log (norm_pos_of_isUnit hn (hg.mul hg')) (norm_mul_le _ _)

/- English proof (translation)
Rewrite using `[dOp_eq, dOp_eq, norm_mul_unitary hk', norm_unitary_mul hk]`.
-/
theorem dOp_unitary {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hk' : k' ∈ Matrix.unitaryGroup (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    dOp (k * g * k') = dOp g := by
  rw [dOp_eq, dOp_eq, norm_mul_unitary hk', norm_unitary_mul hk]

/- English proof (translation)
Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[show Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) by simp only [Matrix.mul_assoc], hg', Jm_mul_self]`.
-/
theorem inv_eq_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g⁻¹ = Jm ε * gᴴ * Jm ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  apply Matrix.inv_eq_left_inv
  rw [show Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) by simp only [Matrix.mul_assoc], hg',
    Jm_mul_self]

/- English proof (translation)
Rewrite using `[inv_eq_of_inUJ hg, dOp_eq, dOp_eq, norm_mul_unitary (Jm_unitary ε), norm_unitary_mul (Jm_unitary ε), Matrix.l2_opNorm_conjTranspose]`.
-/
theorem dOp_inv {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    dOp g⁻¹ = dOp g := by
  rw [inv_eq_of_inUJ hg, dOp_eq, dOp_eq, norm_mul_unitary (Jm_unitary ε),
    norm_unitary_mul (Jm_unitary ε), Matrix.l2_opNorm_conjTranspose]

/- English proof (translation)
Establish `hk` using `mul_exp_neg_polarLog_mem_compact hg`. Establish `hL : (polarLog g).IsHermitian` using `polar_log_hermitian g`. Use `conv_lhs => rw [polar_decomposition_eq (g := g)]`. Conclude with `dHS_polar hk.1 hL`.
-/
theorem dHS_eq_log {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    dHS g = Real.sqrt (hs (polarLog g)) := by
  have hk := mul_exp_neg_polarLog_mem_compact hg
  have hL : (polarLog g).IsHermitian := polar_log_hermitian g
  conv_lhs => rw [polar_decomposition_eq (g := g)]
  exact dHS_polar hk.1 hL

/- English proof (translation)
Establish `hcs : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => hs M)`. Unfold `hs`. Conclude with `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ((continuous_id.matrix_elem i j).norm).pow 2`. Establish `h : ContinuousOn (fun g => Real.sqrt (hs (polarLog g))) {g | inUJ ε g}` using `(Real.continuous_sqrt.comp hcs).comp_continuousOn (continuousOn_polarLog ε)`. Conclude with `h.congr fun g hg => dHS_eq_log hg`.
-/
theorem continuousOn_dHS (ε : Fin n → Bool) : ContinuousOn (dHS (n := n)) {g | inUJ ε g} := by
  have hcs : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => hs M) := by
    unfold hs
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_id.matrix_elem i j).norm).pow 2
  have h : ContinuousOn (fun g => Real.sqrt (hs (polarLog g))) {g | inUJ ε g} :=
    (Real.continuous_sqrt.comp hcs).comp_continuousOn (continuousOn_polarLog ε)
  exact h.congr fun g hg => dHS_eq_log hg

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `h0 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = dOp (0 : Matrix (Fin 0) (Fin 0) ℂ)` using `fun g => by rw [Subsingleton.elim g 0]`. Conclude with `continuousOn_const.congr fun g _ => h0 g`. Establish `hc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => Real.log ‖g‖) {g | inUJ ε g}` using `continuous_norm.continuousOn.log fun g hg => (norm_pos_of_isUnit hn (indefinite_unitary_preserves_form hg).2).ne'`. Conclude with `hc.congr fun g _ => dOp_eq g`.
-/
theorem continuousOn_dOp (ε : Fin n → Bool) : ContinuousOn (dOp (n := n)) {g | inUJ ε g} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ g : Matrix (Fin 0) (Fin 0) ℂ, dOp g = dOp (0 : Matrix (Fin 0) (Fin 0) ℂ) :=
      fun g => by rw [Subsingleton.elim g 0]
    exact continuousOn_const.congr fun g _ => h0 g
  · have hc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => Real.log ‖g‖) {g | inUJ ε g} :=
      continuous_norm.continuousOn.log fun g hg => (norm_pos_of_isUnit hn (indefinite_unitary_preserves_form hg).2).ne'
    exact hc.congr fun g _ => dOp_eq g

/- English proof (translation)
Introduce `n ε`. Establish `hmem : ∀ g : UJ ε, inUJ ε (uMat g)` using `fun g => g.2`. Establish `hdec : ∀ g : UJ ε, uMat g = (uMat g * NormedSpace.exp (-polarLog (uMat g))) * NormedSpace.exp (polarLog (uMat g))` using `fun g => polar_decomposition_eq`. Use `⟨fun k X hk hX => dHS_polar hk.1 (hermitian_of_mem_hermitian_part hX), fun g g' hn => ?_, fun k hk k' hk' g => ⟨dOp_unitary hk.1 hk'.1 _, dHS_unitary hk.1 hk'.1 _⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hb` using `dOp_bounds hn (mul_exp_neg_polarLog_mem_compact (hmem g)).1 (polarLog_mem_hermitian_part (hmem g))`.

Rewrite `hb` using `[← hdec g]`. Establish `hinv : uMat g⁻¹ = (uMat g)⁻¹`. Simplify using `only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]`. Establish `hmul : uMat (g * g') = uMat g * uMat g'`. Simplify using `only [uMat, Subgroup.coe_mul, Units.val_mul]`.

Rewrite using `[hinv, hmul, dHS_eq_log (hmem g)]`. Conclude with `⟨hb.1, dOp_inv (hmem g), dOp_mul_le hn (Units.isUnit _) (Units.isUnit _), hb.2.1, hb.2.2⟩`. Conclude with `(continuousOn_dHS ε).comp_continuous (Units.continuous_val.comp continuous_subtype_val) fun g => hmem g`. Conclude with `(continuousOn_dOp ε).comp_continuous (Units.continuous_val.comp continuous_subtype_val) fun g => hmem g`.
-/
theorem cartan_distances : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Kset ε → inP ε X → dHS (k * NormedSpace.exp X) = Real.sqrt (hs X)) ∧ (∀ g g' : UJ ε, 1 ≤ n → 0 ≤ dOp (uMat g) ∧ dOp (uMat g⁻¹) = dOp (uMat g) ∧ dOp (uMat (g * g')) ≤ dOp (uMat g) + dOp (uMat g') ∧ Real.sqrt 2 * dOp (uMat g) ≤ dHS (uMat g) ∧ dHS (uMat g) ≤ Real.sqrt (2 * rkR ε) * dOp (uMat g)) ∧ (∀ k ∈ Kset ε, ∀ k' ∈ Kset ε, ∀ g : UJ ε, dOp (k * uMat g * k') = dOp (uMat g) ∧ dHS (k * uMat g * k') = dHS (uMat g)) ∧ Continuous (fun g : UJ ε => dHS (uMat g)) ∧ Continuous (fun g : UJ ε => dOp (uMat g)) := by
  intro n ε
  have hmem : ∀ g : UJ ε, inUJ ε (uMat g) := fun g => g.2
  have hdec : ∀ g : UJ ε, uMat g =
      (uMat g * NormedSpace.exp (-polarLog (uMat g))) * NormedSpace.exp (polarLog (uMat g)) :=
    fun g => polar_decomposition_eq
  refine ⟨fun k X hk hX => dHS_polar hk.1 (hermitian_of_mem_hermitian_part hX), fun g g' hn => ?_,
    fun k hk k' hk' g => ⟨dOp_unitary hk.1 hk'.1 _, dHS_unitary hk.1 hk'.1 _⟩, ?_, ?_⟩
  · have hb := dOp_bounds hn (mul_exp_neg_polarLog_mem_compact (hmem g)).1 (polarLog_mem_hermitian_part (hmem g))
    rw [← hdec g] at hb
    have hinv : uMat g⁻¹ = (uMat g)⁻¹ := by
      simp only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
    have hmul : uMat (g * g') = uMat g * uMat g' := by
      simp only [uMat, Subgroup.coe_mul, Units.val_mul]
    rw [hinv, hmul, dHS_eq_log (hmem g)]
    exact ⟨hb.1, dOp_inv (hmem g), dOp_mul_le hn (Units.isUnit _) (Units.isUnit _), hb.2.1, hb.2.2⟩
  · exact (continuousOn_dHS ε).comp_continuous (Units.continuous_val.comp continuous_subtype_val)
      fun g => hmem g
  · exact (continuousOn_dOp ε).comp_continuous (Units.continuous_val.comp continuous_subtype_val)
      fun g => hmem g

end GlobalTheory.Count.Cartan
