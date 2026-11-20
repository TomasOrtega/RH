import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwoDiagonalZeroSize
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableGermIntegrand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks

noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXHead

/- English proof (translation)
Unfold `LeftFubiniLemmas.lhOf U.lowW`. Simplify using `only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]`. Use `ContDiff.sum fun j _ => ?_` and prove the remaining obligations. Use `ContDiff.mul ?_ contDiff_const` and prove the remaining obligations. Use `ContDiff.sum fun i _ => ?_` and prove the remaining obligations.

Use `contDiff_const.mul ?_` and prove the remaining obligations. Use `contDiff_const.add ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `contDiff_apply ℝ ℂ _`. Conclude with `contDiff_const`.
-/
theorem cd_lhOf_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (a b : Fin p) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => LeftFubiniLemmas.lhOf σ v a b) := by
  unfold LeftFubiniLemmas.lhOf U.lowW
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
  refine ContDiff.sum fun j _ => ?_
  refine ContDiff.mul ?_ contDiff_const
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_const.mul ?_
  refine contDiff_const.add ?_
  split_ifs
  · exact contDiff_apply ℝ ℂ _
  · exact contDiff_const

/- English proof (translation)
Unfold `U.subS`. Use `ContDiff.sum fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Apply the tactic sequence `exact cd_lhOf_entry σ _ _`. Conclude with `contDiff_const`.
-/
theorem cd_subS_lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    ContDiff ℝ ∞ (fun v : U.LW σ → ℂ => U.subS (LeftFubiniLemmas.lhOf σ v)) := by
  unfold U.subS
  refine ContDiff.sum fun i _ => ?_
  split_ifs
  · exact cd_lhOf_entry σ _ _
  · exact contDiff_const

/- English proof (translation)
Establish `h2` using `cd_subS_lhOf (D.ptPerm h)`. Unfold `G.psi`. Establish `hre : ContDiff ℝ ∞ (fun v : PBQ.XH h => ((U.betaU * U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)).re : ℂ))`. Establish `hm : ContDiff ℝ ∞ (fun v : PBQ.XH h => U.betaU * U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v))` using `contDiff_const.mul h2`. Conclude with `Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hm)`.

Conclude with `Complex.contDiff_exp.comp (contDiff_const.mul hre)`.
-/
theorem cd_psiH (h : C.LPt) :
    ContDiff ℝ ∞ (fun v : PBQ.XH h => G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v))) := by
  have h2 := cd_subS_lhOf (D.ptPerm h)
  unfold G.psi
  have hre : ContDiff ℝ ∞ (fun v : PBQ.XH h => ((U.betaU * U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)).re : ℂ)) := by
    have hm : ContDiff ℝ ∞ (fun v : PBQ.XH h => U.betaU * U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)) :=
      contDiff_const.mul h2
    exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hm)
  exact Complex.contDiff_exp.comp (contDiff_const.mul hre)

/- English proof (translation)
Establish `key : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ L V : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) → (∀ i, L i i = 1) → (∀ i j, j < i → V i j = 0) → (∀ i, V i i = 1) → (∀ i j, ‖(L * Matrix.diagonal d * V) i j‖ ≤ B) → ∀ c : Fin n, c.val < k → ∀ a, ‖L a c‖ ≤ C ∧ ‖V c a‖ ≤ C`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ c hc _ => absurd hc (Nat.not_lt_zero _)⟩`. Consider the case `succ k ih`.

Take `⟨C, hC0, hC⟩` from `ih`. Take `⟨Dm, hDm0, hdle⟩ : ∃ Dm : ℝ, 0 ≤ Dm ∧ ∀ i, ‖d i‖ ≤ Dm` from `⟨∑ j, ‖d j‖, Finset.sum_nonneg fun j _ => norm_nonneg _, fun i => Finset.single_le_sum (f := fun j => ‖d j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)⟩`. Establish `hCDC : 0 ≤ C * Dm * C` using `mul_nonneg (mul_nonneg hC0 hDm0) hC0`. Take `⟨T, hT0, hTdef⟩ : ∃ T : ℝ, 0 ≤ T ∧ |B| + n * (C * Dm * C) ≤ T` from `⟨_, add_nonneg (abs_nonneg B) (mul_nonneg (Nat.cast_nonneg n) hCDC), le_rfl⟩`. Establish `hS0 : 0 ≤ ∑ c, T / ‖d c‖` using `Finset.sum_nonneg fun c _ => div_nonneg hT0 (norm_nonneg _)`.

Use `⟨max C (1 + ∑ c, T / ‖d c‖), le_trans hC0 (le_max_left _ _), ?_⟩` and prove the remaining obligations. Introduce `L V hL1 hL2 hV1 hV2 hN c hc a`. Establish `hdc : 0 < ‖d c‖` using `norm_pos_iff.mpr (hd c)`. Establish `hcT : T / ‖d c‖ ≤ max C (1 + ∑ c, T / ‖d c‖)`. Establish `hsg : T / ‖d c‖ ≤ ∑ i, T / ‖d i‖` using `Finset.single_le_sum (f := fun i => T / ‖d i‖) (fun i _ => div_nonneg hT0 (norm_nonneg _)) (Finset.mem_univ c)`.

Conclude with `le_trans (by linarith) (le_max_right _ _)`. Establish `h1 : (1 : ℝ) ≤ max C (1 + ∑ c, T / ‖d c‖)` using `le_trans (by linarith) (le_max_right _ _)`. Establish `core : ∀ x y : Fin n, (x = c ∨ y = c) → ‖L x c * d c * V c y‖ ≤ T`. Introduce `x y hxy`. Establish `hsum : (L * Matrix.diagonal d * V) x y = L x c * d c * V c y + ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y`.

Establish `h` using `Finset.add_sum_erase Finset.univ (fun e => L x e * d e * V e y) (Finset.mem_univ c)`. Rewrite using `[h]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal]`. Establish `hterm : ∀ e ∈ Finset.univ.erase c, ‖L x e * d e * V e y‖ ≤ C * Dm * C`.

Introduce `e he`. Establish `hne : e ≠ c` using `Finset.ne_of_mem_erase he`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases. Establish `hek : e.val < k`. Establish `: e.val < c.val` using `hlt`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[norm_mul, norm_mul]`. Establish `hA` using `(hC L V hL1 hL2 hV1 hV2 hN e hek x).1`. Establish `hB` using `(hC L V hL1 hL2 hV1 hV2 hN e hek y).2`. Conclude with `mul_le_mul (mul_le_mul hA (hdle e) (norm_nonneg _) hC0) hB (norm_nonneg _) (mul_nonneg hC0 hDm0)`.

Establish `hz : L x e * d e * V e y = 0`. Break down `hxy with rfl | rfl` into its components or cases. Rewrite using `[hL1 _ _ hgt]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hV1 _ _ hgt]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz, norm_zero]`. Conclude with `hCDC`. Establish `hrest : ‖∑ e ∈ Finset.univ.erase c, L x e * d e * V e y‖ ≤ n * (C * Dm * C)`. Use `le_trans (norm_sum_le _ _) ?_` and prove the remaining obligations.

Use `le_trans (Finset.sum_le_sum hterm) ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Establish `hcard : ((Finset.univ.erase c).card : ℝ) ≤ n`. Establish `: (Finset.univ.erase c).card ≤ n`. Rewrite using `[Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Conclude with `mul_le_mul_of_nonneg_right hcard hCDC`. Establish `hNxy` using `hN x y`. Rewrite `hNxy` using `[hsum]`.

Combine the equalities or inequalities in the displayed calculation. Break down `lt_trichotomy a c with hac | rfl | hac` into its components or cases. Rewrite using `[hL1 _ _ hac, hV1 _ _ hac, norm_zero]`. Conclude with `⟨le_trans zero_le_one h1, le_trans zero_le_one h1⟩`. Rewrite using `[hL2, hV2, norm_one]`.

Conclude with `⟨h1, h1⟩`. Prove the components needed by the constructor for the conclusion. Establish `hx` using `core a c (Or.inr rfl)`. Rewrite `hx` using `[hV2, mul_one, norm_mul]`. Conclude with `le_trans ((le_div_iff₀ hdc).mpr hx) hcT`.

Establish `hx` using `core c a (Or.inl rfl)`. Rewrite `hx` using `[hL2, one_mul, norm_mul]`. Conclude with `le_trans ((le_div_iff₀ hdc).mpr (by rw [mul_comm]; exact hx)) hcT`. Take `⟨C, -, hC⟩` from `key n`. Conclude with `⟨C, fun L V hL1 hL2 hV1 hV2 hN i j => (hC L V hL1 hL2 hV1 hV2 hN j j.isLt i).1⟩`.
-/
private theorem exists_bound_unitriangular_of_ldu_bounded {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) (B : ℝ) :
    ∃ C : ℝ, ∀ L V : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) → (∀ i, L i i = 1) →
      (∀ i j, j < i → V i j = 0) → (∀ i, V i i = 1) →
      (∀ i j, ‖(L * Matrix.diagonal d * V) i j‖ ≤ B) → ∀ i j, ‖L i j‖ ≤ C := by
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ L V : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) →
      (∀ i, L i i = 1) → (∀ i j, j < i → V i j = 0) → (∀ i, V i i = 1) →
      (∀ i j, ‖(L * Matrix.diagonal d * V) i j‖ ≤ B) →
      ∀ c : Fin n, c.val < k → ∀ a, ‖L a c‖ ≤ C ∧ ‖V c a‖ ≤ C := by
    intro k
    induction k with
    | zero => exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ c hc _ => absurd hc (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      obtain ⟨Dm, hDm0, hdle⟩ : ∃ Dm : ℝ, 0 ≤ Dm ∧ ∀ i, ‖d i‖ ≤ Dm :=
        ⟨∑ j, ‖d j‖, Finset.sum_nonneg fun j _ => norm_nonneg _, fun i =>
          Finset.single_le_sum (f := fun j => ‖d j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)⟩
      have hCDC : 0 ≤ C * Dm * C := mul_nonneg (mul_nonneg hC0 hDm0) hC0
      obtain ⟨T, hT0, hTdef⟩ : ∃ T : ℝ, 0 ≤ T ∧ |B| + n * (C * Dm * C) ≤ T :=
        ⟨_, add_nonneg (abs_nonneg B) (mul_nonneg (Nat.cast_nonneg n) hCDC), le_rfl⟩
      have hS0 : 0 ≤ ∑ c, T / ‖d c‖ := Finset.sum_nonneg fun c _ => div_nonneg hT0 (norm_nonneg _)
      refine ⟨max C (1 + ∑ c, T / ‖d c‖), le_trans hC0 (le_max_left _ _), ?_⟩
      intro L V hL1 hL2 hV1 hV2 hN c hc a
      have hdc : 0 < ‖d c‖ := norm_pos_iff.mpr (hd c)
      have hcT : T / ‖d c‖ ≤ max C (1 + ∑ c, T / ‖d c‖) := by
        have hsg : T / ‖d c‖ ≤ ∑ i, T / ‖d i‖ :=
          Finset.single_le_sum (f := fun i => T / ‖d i‖) (fun i _ => div_nonneg hT0 (norm_nonneg _))
            (Finset.mem_univ c)
        exact le_trans (by linarith) (le_max_right _ _)
      have h1 : (1 : ℝ) ≤ max C (1 + ∑ c, T / ‖d c‖) := le_trans (by linarith) (le_max_right _ _)
      have core : ∀ x y : Fin n, (x = c ∨ y = c) → ‖L x c * d c * V c y‖ ≤ T := by
        intro x y hxy
        have hsum : (L * Matrix.diagonal d * V) x y = L x c * d c * V c y +
            ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y := by
          have h := Finset.add_sum_erase Finset.univ (fun e => L x e * d e * V e y) (Finset.mem_univ c)
          rw [h]
          rw [Matrix.mul_apply]
          simp only [Matrix.mul_diagonal]
        have hterm : ∀ e ∈ Finset.univ.erase c, ‖L x e * d e * V e y‖ ≤ C * Dm * C := by
          intro e he
          have hne : e ≠ c := Finset.ne_of_mem_erase he
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hek : e.val < k := by
              have : e.val < c.val := hlt
              omega
            rw [norm_mul, norm_mul]
            have hA := (hC L V hL1 hL2 hV1 hV2 hN e hek x).1
            have hB := (hC L V hL1 hL2 hV1 hV2 hN e hek y).2
            exact mul_le_mul (mul_le_mul hA (hdle e) (norm_nonneg _) hC0) hB (norm_nonneg _)
              (mul_nonneg hC0 hDm0)
          · have hz : L x e * d e * V e y = 0 := by
              rcases hxy with rfl | rfl
              · rw [hL1 _ _ hgt]; ring
              · rw [hV1 _ _ hgt]; ring
            rw [hz, norm_zero]
            exact hCDC
        have hrest : ‖∑ e ∈ Finset.univ.erase c, L x e * d e * V e y‖ ≤ n * (C * Dm * C) := by
          refine le_trans (norm_sum_le _ _) ?_
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.univ.erase c).card : ℝ) ≤ n := by
            have : (Finset.univ.erase c).card ≤ n := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
              omega
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hcard hCDC
        have hNxy := hN x y
        rw [hsum] at hNxy
        calc ‖L x c * d c * V c y‖
            = ‖(L x c * d c * V c y + ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y)
                - ∑ e ∈ Finset.univ.erase c, L x e * d e * V e y‖ := by rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
          _ ≤ |B| + n * (C * Dm * C) := add_le_add (le_trans hNxy (le_abs_self B)) hrest
          _ ≤ T := hTdef
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [hL1 _ _ hac, hV1 _ _ hac, norm_zero]
        exact ⟨le_trans zero_le_one h1, le_trans zero_le_one h1⟩
      · rw [hL2, hV2, norm_one]
        exact ⟨h1, h1⟩
      · constructor
        · have hx := core a c (Or.inr rfl)
          rw [hV2, mul_one, norm_mul] at hx
          exact le_trans ((le_div_iff₀ hdc).mpr hx) hcT
        · have hx := core c a (Or.inl rfl)
          rw [hL2, one_mul, norm_mul] at hx
          exact le_trans ((le_div_iff₀ hdc).mpr (by rw [mul_comm]; exact hx)) hcT
  obtain ⟨C, -, hC⟩ := key n
  exact ⟨C, fun L V hL1 hL2 hV1 hV2 hN i j => (hC L V hL1 hL2 hV1 hV2 hN j j.isLt i).1⟩

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.symm_apply_eq, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hab, Ne.symm hab]`.
-/
private theorem wP_mul_wP_symm_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ * U.wP σ.symm = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Equiv.symm_apply_eq, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

/- English proof (translation)
Establish `hwP : ∀ (τ : Equiv.Perm (Fin (D.ptSize h))) (X : Matrix (Fin (D.ptSize h)) (Fin (D.ptSize h)) ℂ) a b, (U.wP τ * X) a b = X (τ a) b`. Introduce `τ X a b`. Simplify using `[U.wP, Matrix.mul_apply]`. Establish `hmul : U.wP (D.ptPerm h) * U.wP (D.ptPerm h).symm = 1`. Use extensionality with `a b`.

Rewrite using `[hwP]`. Simplify using `[U.wP, Matrix.one_apply]`. Establish `hmul' : U.wP (D.ptPerm h).symm * U.wP (D.ptPerm h) = 1`. Use extensionality with `a b`. Rewrite using `[hwP]`.

Simplify using `[U.wP, Matrix.one_apply]`. Establish `hinv : (U.wP (D.ptPerm h))⁻¹ = U.wP (D.ptPerm h).symm` using `Matrix.inv_eq_right_inv hmul`. Simplify using `only [LeftFubiniLemmas.lhOf, U.hMat, hinv, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (U.wP (D.ptPerm h).symm), hmul', Matrix.one_mul]`.
-/
private theorem lhOf_mul_hMat_eq_wP_mul_lowW_mul_diagonal (h : C.LPt) (v : PBQ.XH h) :
    LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) =
      U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) := by
  have hwP : ∀ (τ : Equiv.Perm (Fin (D.ptSize h))) (X : Matrix (Fin (D.ptSize h)) (Fin (D.ptSize h)) ℂ) a b,
      (U.wP τ * X) a b = X (τ a) b := by
    intro τ X a b
    simp [U.wP, Matrix.mul_apply]
  have hmul : U.wP (D.ptPerm h) * U.wP (D.ptPerm h).symm = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hmul' : U.wP (D.ptPerm h).symm * U.wP (D.ptPerm h) = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hinv : (U.wP (D.ptPerm h))⁻¹ = U.wP (D.ptPerm h).symm := Matrix.inv_eq_right_inv hmul
  simp only [LeftFubiniLemmas.lhOf, U.hMat, hinv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP (D.ptPerm h).symm), hmul', Matrix.one_mul]

/- English proof (translation)
Rewrite using `[lhOf_mul_hMat_eq_wP_mul_lowW_mul_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]`. Establish `hwdet : (U.wP (D.ptPerm h)).det ≠ 0`. Establish `hd` using `congrArg Matrix.det (wP_mul_wP_symm_eq_one (D.ptPerm h))`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one hd`.

Establish `hbt : (U.lowW (D.ptPerm h) v).BlockTriangular OrderDual.toDual`. Introduce `i j hij`. Establish `hij' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`. Simplify using `[U.lowW, Matrix.one_apply_ne hij'.ne, not_lt_of_gt hij']`. Establish `hlow : (U.lowW (D.ptPerm h) v).det = 1`.

Rewrite using `[Matrix.det_of_lowerTriangular _ hbt]`. Simplify using `[U.lowW]`. Rewrite using `[hlow, one_mul]`. Conclude with `mul_ne_zero hwdet (Finset.prod_ne_zero_iff.mpr fun i _ => PBJ.Asm.ptScal_ne h hh1 i i.isLt)`.
-/
private theorem det_lhOf_mul_hMat_ptPerm_ne_zero (h : C.LPt) (hh1 : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) (v : PBQ.XH h) :
    (LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
  rw [lhOf_mul_hMat_eq_wP_mul_lowW_mul_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hwdet : (U.wP (D.ptPerm h)).det ≠ 0 := by
    have hd := congrArg Matrix.det (wP_mul_wP_symm_eq_one (D.ptPerm h))
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact left_ne_zero_of_mul_eq_one hd
  have hbt : (U.lowW (D.ptPerm h) v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [U.lowW, Matrix.one_apply_ne hij'.ne, not_lt_of_gt hij']
  have hlow : (U.lowW (D.ptPerm h) v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ hbt]
    simp [U.lowW]
  rw [hlow, one_mul]
  exact mul_ne_zero hwdet (Finset.prod_ne_zero_iff.mpr fun i _ => PBJ.Asm.ptScal_ne h hh1 i i.isLt)

/- English proof (translation)
Take `⟨hh1, hh2⟩` from `hh`. Substitute `hh2` using the available equality. Take `⟨B, hB⟩` from `hK1.isBounded.exists_norm_le`. Establish `hd : ∀ i, D.ptDiag h i ≠ 0` using `fun i => PBJ.Asm.ptScal_ne h hh1 i i.isLt`. Take `⟨C, hC⟩` from `exists_bound_unitriangular_of_ldu_bounded (D.ptDiag h) hd B`.

Use `⟨max C 0, fun v hv u hu hmem => ?_⟩` and prove the remaining obligations. Establish `hwP : ∀ (τ : Equiv.Perm (Fin (D.ptSize h))) (X : Matrix (Fin (D.ptSize h)) (Fin (D.ptSize h)) ℂ) a b, (U.wP τ * X) a b = X (τ a) b`. Introduce `τ X a b`. Simplify using `[U.wP, Matrix.mul_apply]`. Establish `hmul : U.wP (D.ptPerm h) * U.wP (D.ptPerm h).symm = 1`.

Use extensionality with `a b`. Rewrite using `[hwP]`. Simplify using `[U.wP, Matrix.one_apply]`. Establish `hmul' : U.wP (D.ptPerm h).symm * U.wP (D.ptPerm h) = 1`. Use extensionality with `a b`.

Rewrite using `[hwP]`. Simplify using `[U.wP, Matrix.one_apply]`. Establish `hinv : (U.wP (D.ptPerm h))⁻¹ = U.wP (D.ptPerm h).symm` using `Matrix.inv_eq_right_inv hmul`. Establish `hz : PBQ.zxH h (D.ptSize h) rfl v = U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))`. Simplify using `only [PBQ.zxH, LeftFubiniLemmas.lhOf, U.hMat, finCongr_refl, Matrix.reindex_refl_refl, Equiv.refl_apply, hinv]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (U.wP (D.ptPerm h).symm), hmul', Matrix.one_mul]`. Rewrite `hmem` using `[hz]`. Establish `hN : ∀ i k, ‖(U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h) * u) i k‖ ≤ B`. Introduce `i k`.

Establish `hm` using `hB _ hmem`. Establish `he` using `(norm_le_pi_norm (Matrix.of.symm (Matrix.of (U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))) * u) ((D.ptPerm h).symm i)) k).trans (norm_le_pi_norm (Matrix.of.symm (Matrix.of (U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))) * …`. Use `le_trans (le_of_eq ?_) (le_trans he hm)` and prove the remaining obligations. Use `show _ = ‖(U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) * u) ((D.ptPerm h).symm i) k‖`. Rewrite using `[Matrix.mul_assoc (U.wP _), hwP, Equiv.apply_symm_apply]`.

Establish `hL` using `hC (U.lowW (D.ptPerm h) v) u (fun i k hik => by simp [U.lowW, Matrix.one_apply_ne hik.ne, not_lt_of_gt hik]) (fun i => by simp [U.lowW]) (fun i k hik => hu.1 hik) hu.2 hN`. Establish `hvle : ‖v‖ ≤ max C 0`. Use `(pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨a, b⟩, hq⟩`. Establish `hab` using `hL a b`.

Establish `he : U.lowW (D.ptPerm h) v a b = v ⟨(a, b), hq⟩`. Simplify using `[U.lowW, hq, Matrix.one_apply_ne (ne_of_gt hq.1)]`. Rewrite `hab` using `[he]`. Conclude with `le_trans hab (le_max_left _ _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem head_bound (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (K1 : Set (Fin j → Fin j → ℂ)) (hK1 : IsCompact K1) :
    ∃ R : ℝ, ∀ v : PBQ.XH h, R < ‖v‖ → ∀ u : Matrix (Fin j) (Fin j) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u →
      Matrix.of.symm (Matrix.of (PBQ.zxH h j hh.2 v) * u) ∉ K1 := by
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  obtain ⟨B, hB⟩ := hK1.isBounded.exists_norm_le
  have hd : ∀ i, D.ptDiag h i ≠ 0 := fun i => PBJ.Asm.ptScal_ne h hh1 i i.isLt
  obtain ⟨C, hC⟩ := exists_bound_unitriangular_of_ldu_bounded (D.ptDiag h) hd B
  refine ⟨max C 0, fun v hv u hu hmem => ?_⟩
  have hwP : ∀ (τ : Equiv.Perm (Fin (D.ptSize h))) (X : Matrix (Fin (D.ptSize h)) (Fin (D.ptSize h)) ℂ) a b,
      (U.wP τ * X) a b = X (τ a) b := by
    intro τ X a b
    simp [U.wP, Matrix.mul_apply]
  have hmul : U.wP (D.ptPerm h) * U.wP (D.ptPerm h).symm = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hmul' : U.wP (D.ptPerm h).symm * U.wP (D.ptPerm h) = 1 := by
    ext a b
    rw [hwP]
    simp [U.wP, Matrix.one_apply]
  have hinv : (U.wP (D.ptPerm h))⁻¹ = U.wP (D.ptPerm h).symm := Matrix.inv_eq_right_inv hmul
  have hz : PBQ.zxH h (D.ptSize h) rfl v =
      U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) := by
    simp only [PBQ.zxH, LeftFubiniLemmas.lhOf, U.hMat, finCongr_refl, Matrix.reindex_refl_refl, Equiv.refl_apply, hinv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP (D.ptPerm h).symm), hmul', Matrix.one_mul]
  rw [hz] at hmem
  have hN : ∀ i k, ‖(U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h) * u) i k‖ ≤ B := by
    intro i k
    have hm := hB _ hmem
    have he := (norm_le_pi_norm (Matrix.of.symm (Matrix.of (U.wP (D.ptPerm h) *
      (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))) * u) ((D.ptPerm h).symm i)) k).trans
      (norm_le_pi_norm (Matrix.of.symm (Matrix.of (U.wP (D.ptPerm h) *
      (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h))) * u)) ((D.ptPerm h).symm i))
    refine le_trans (le_of_eq ?_) (le_trans he hm)
    show _ = ‖(U.wP (D.ptPerm h) * (U.lowW (D.ptPerm h) v * Matrix.diagonal (D.ptDiag h)) * u)
      ((D.ptPerm h).symm i) k‖
    rw [Matrix.mul_assoc (U.wP _), hwP, Equiv.apply_symm_apply]
  have hL := hC (U.lowW (D.ptPerm h) v) u
    (fun i k hik => by simp [U.lowW, Matrix.one_apply_ne hik.ne, not_lt_of_gt hik])
    (fun i => by simp [U.lowW])
    (fun i k hik => hu.1 hik) hu.2 hN
  have hvle : ‖v‖ ≤ max C 0 := by
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr ?_
    rintro ⟨⟨a, b⟩, hq⟩
    have hab := hL a b
    have he : U.lowW (D.ptPerm h) v a b = v ⟨(a, b), hq⟩ := by
      simp [U.lowW, hq, Matrix.one_apply_ne (ne_of_gt hq.1)]
    rw [he] at hab
    exact le_trans hab (le_max_left _ _)
  linarith

end Formalism.FourierDecayAlt.P.CutEXHead

open Formalism.FourierDecayAlt.P.CutEXHead in
/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.P.CutEX.HeadFam`. Introduce `Wp Wq _ _ _ _ _ _ P p h hh f hf K hK hKU hsupp`. Establish `hZ : ContDiff ℝ ∞ (fun v : Formalism.FourierDecayAlt.P.PBQ.XH h => Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 v))`. Use `contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [Formalism.FourierDecayAlt.P.PBQ.zxH, Matrix.of_symm_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]`.

Apply the tactic sequence `exact ContDiff.sum fun c _ => (cd_lhOf_entry _ _ _).mul contDiff_const`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `q₀ ⟨-, hq₀2⟩ hlev`. Establish `hdet : (Matrix.of (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1)).det ≠ 0` using `by show (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1).det ≠ 0`. Simplify using `only [Formalism.FourierDecayAlt.P.PBQ.zxH]`.

Rewrite using `[Matrix.det_reindex_self]`. Conclude with `det_lhOf_mul_hMat_ptPerm_ne_zero h hh.1 q₀.1`. Take `⟨U', F', hU'o, hmem', hF', hagree⟩` from `hf (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1, q₀.2) ⟨hdet, hq₀2⟩ hlev`. Establish `hΦ : ContDiff ℝ ∞ (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2))` using `(hZ.comp contDiff_fst).prodMk contDiff_snd`. Use `⟨(fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U', fun q => Formalism.FourierDecayAlt.P.PBQ.ellH h q.1 (F' (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1, q.2)), hU'o.prei …` and prove the remaining obligations.

Establish `h1 : ContDiffOn ℝ ∞ (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => F' (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1, q.2)) ((fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P. …` using `hF'.comp hΦ.contDiffOn (Set.mapsTo_preimage _ _)`. Establish `h2` using `((cd_psiH h).comp contDiff_fst).contDiffOn (s := (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U')`. Use `(h2.smul h1).congr fun q _ => ?_` and prove the remaining obligations. Simplify using `[Formalism.FourierDecayAlt.P.PBQ.ellH]`. Introduce `q hq hlev'`.

Conclude with `congrArg _ (hagree _ hq hlev')`. Take `⟨R, hR⟩` from `head_bound h P.r hh (Prod.fst '' K) (hK.image continuous_fst)`. Use `⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun v hv y hy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨u, hu, huK⟩` from `hsupp (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 v, y) hy hne`.

Establish `hvR : R < ‖v‖`. Simplify `hv` using `[Metric.mem_closedBall, dist_zero_right, not_le]`. Conclude with `hR v hvR u hu ⟨_, huK, rfl⟩`.
-/
theorem Formalism.FourierDecayAlt.P.head_family_exhaustion : Formalism.FourierDecayAlt.P.CutEX.HeadFam := by
  unfold Formalism.FourierDecayAlt.P.CutEX.HeadFam
  intro Wp Wq _ _ _ _ _ _ P p h hh f hf K hK hKU hsupp
  have hZ : ContDiff ℝ ∞ (fun v : Formalism.FourierDecayAlt.P.PBQ.XH h =>
      Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 v)) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    simp only [Formalism.FourierDecayAlt.P.PBQ.zxH, Matrix.of_symm_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact ContDiff.sum fun c _ => (cd_lhOf_entry _ _ _).mul contDiff_const
  refine ⟨?_, ?_⟩
  · rintro q₀ ⟨-, hq₀2⟩ hlev
    have hdet : (Matrix.of (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1)).det ≠ 0 := by
      show (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1).det ≠ 0
      simp only [Formalism.FourierDecayAlt.P.PBQ.zxH]
      rw [Matrix.det_reindex_self]
      exact det_lhOf_mul_hMat_ptPerm_ne_zero h hh.1 q₀.1
    obtain ⟨U', F', hU'o, hmem', hF', hagree⟩ := hf (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q₀.1, q₀.2) ⟨hdet, hq₀2⟩ hlev
    have hΦ : ContDiff ℝ ∞ (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) =>
        (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) :=
      (hZ.comp contDiff_fst).prodMk contDiff_snd
    refine ⟨(fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U',
      fun q => Formalism.FourierDecayAlt.P.PBQ.ellH h q.1 (F' (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1, q.2)), hU'o.preimage hΦ.continuous, hmem', ?_, ?_⟩
    · have h1 : ContDiffOn ℝ ∞ (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => F' (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1, q.2))
          ((fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U') :=
        hF'.comp hΦ.contDiffOn (Set.mapsTo_preimage _ _)
      have h2 := ((cd_psiH h).comp contDiff_fst).contDiffOn
        (s := (fun q : Formalism.FourierDecayAlt.P.PBQ.XH h × Mt P.k (P.r - P.r) => (Matrix.of.symm (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 q.1), q.2)) ⁻¹' U')
      refine (h2.smul h1).congr fun q _ => ?_
      simp [Formalism.FourierDecayAlt.P.PBQ.ellH]
    · intro q hq hlev'
      exact congrArg _ (hagree _ hq hlev')
  · obtain ⟨R, hR⟩ := head_bound h P.r hh (Prod.fst '' K) (hK.image continuous_fst)
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun v hv y hy => ?_⟩
    by_contra hne
    obtain ⟨u, hu, huK⟩ := hsupp (Formalism.FourierDecayAlt.P.PBQ.zxH h P.r hh.2 v, y) hy hne
    have hvR : R < ‖v‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hv
    exact hR v hvR u hu ⟨_, huK, rfl⟩
