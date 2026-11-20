import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[Equiv.symm_apply_eq]`.

Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[D.castM, Matrix.reindex_apply]`.
-/
theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (p q : Fin (2 * b + k + 1)) :
    D.castM h g p q = g (Fin.cast (by omega) p) (Fin.cast (by omega) q) := by
  subst h; simp [D.castM, Matrix.reindex_apply]

/- English proof (translation)
Substitute `h` using the available equality. Simplify `hg` using `[D.castM]`.
-/
theorem castM_GV' {k a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ B.GV k a) : D.castM h g ∈ B.GV k b := by
  subst h; simpa [D.castM] using hg

/- English proof (translation)
Simplify using `only [zfull, U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply, fsym]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.fromBlocks]`.
-/
theorem zfull_apply {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (c d : Fin (j + 1)) :
    zfull Z τ c d = if hc : c.val < j then (if hd : d.val < j then Z ⟨c.val, hc⟩ ⟨d.val, hd⟩ else 0)
      else (if d.val < j then 0 else τ) := by
  simp only [zfull, U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply, fsym]
  split_ifs <;> simp [Matrix.fromBlocks]

/- English proof (translation)
Unfold `zfull U.blk2`. Rewrite using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[Matrix.det_unique]`.
-/
theorem det_zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_unique]

/- English proof (translation)
Simplify using `[G.wMat, Matrix.mul_apply]`.
-/
theorem wMat_mul_apply {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (c : Fin n) :
    (G.wMat d * M) i c = M i.rev c := by
  simp [G.wMat, Matrix.mul_apply]

/- English proof (translation)
Unfold `x0`. Rewrite using `[castM_apply']`. Establish `hrow : (Fin.cast (by omega) (esI k r (Fin.castLE (by omega) a)) : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) = U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩)` using `by ext; rw [Ux4.block_index_last_val_eq]; simp [esI]; omega`. Rewrite using `[hrow]`. Take `⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q` from `⟨_, Equiv.apply_symm_apply _ _⟩`.

Rewrite using `[← hy]`. Unfold `U.mMap`. Rewrite using `[Ux4.block3_apply]`. Break down `y with ((c | c) | c)` into its components or cases. Establish `hq : q.val = c.val`.

Use `congrArg Fin.val hy` as an intermediate fact. Rewrite `this` using `[Ux4.block_index_first_val_eq]`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]`.

Rewrite using `[wMat_mul_apply]`. Establish `hrev : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = ⟨a.val, by omega⟩` using `by ext; simp [Fin.rev]; omega`. Rewrite using `[hrev, zfull_apply, dif_pos (by simp)]`. Distinguish the cases in `h : c.val < j`. Rewrite using `[dif_pos h, dif_pos (by omega)]`.

Conclude with `congrArg₂ Z (Fin.ext rfl) (Fin.ext hq.symm)`. Rewrite using `[dif_neg h, dif_neg (by omega)]`. Establish `hq : q.val = j + 1 + c.val`. Use `congrArg Fin.val hy` as an intermediate fact. Rewrite `this` using `[Ux4.block_index_middle_val_eq]`.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr, Matrix.zero_apply]`. Rewrite using `[dif_neg (by omega)]`. Establish `hq : q.val = j + 1 + (2 * (r - (j + 1)) + k + 1) + c.val`.

Use `congrArg Fin.val hy` as an intermediate fact. Rewrite `this` using `[Ux4.block_index_last_val_eq]`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]`.

Rewrite using `[dif_neg (by omega)]`.
-/
theorem level_point_first_lines (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r (Fin.castLE (by omega) a)) q = if hq : q.val < j then Z a ⟨q.val, hq⟩ else 0 := by
  unfold x0
  rw [castM_apply']
  have hrow : (Fin.cast (by omega) (esI k r (Fin.castLE (by omega) a)) : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    ext; rw [Ux4.block_index_last_val_eq]; simp [esI]; omega
  rw [hrow]
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  rw [← hy]
  unfold U.mMap
  rw [Ux4.block3_apply]
  rcases y with ((c | c) | c)
  · have hq : q.val = c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_first_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [wMat_mul_apply]
    have hrev : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = ⟨a.val, by omega⟩ := by
      ext; simp [Fin.rev]; omega
    rw [hrev, zfull_apply, dif_pos (by simp)]
    by_cases h : c.val < j
    · rw [dif_pos h, dif_pos (by omega)]
      exact congrArg₂ Z (Fin.ext rfl) (Fin.ext hq.symm)
    · rw [dif_neg h, dif_neg (by omega)]
  · have hq : q.val = j + 1 + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_middle_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    rw [dif_neg (by omega)]
  · have hq : q.val = j + 1 + (2 * (r - (j + 1)) + k + 1) + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_last_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    rw [dif_neg (by omega)]

/- English proof (translation)
Simplify using `only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_eI_row (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_eI_col (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r s (eI k r a) = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_low (k r : ℕ) (p s : Fin (2 * r + k + 1)) (hs : s.val < r) :
    Hpk k r p s = if p.val + s.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Introduce `k r j hj Z τ γ a p`. Establish `h1 : ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (bvec (eI k r (Fin.castLE (by omega) a))) = ∑ s, Hpk k r (eI k r (Fin.castLE (by omega) a)) s * v s`. Introduce `v`. Simplify using `[herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]`. Rewrite using `[h1]`.

Simplify using `only [Hpk_eI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.transpose_apply]`. Conclude with `level_point_first_lines k r j hj Z τ γ a p`.
-/
theorem xiCoef : XiCoef := by
  intro k r j hj Z τ γ a p
  have h1 : ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (bvec (eI k r (Fin.castLE (by omega) a))) =
      ∑ s, Hpk k r (eI k r (Fin.castLE (by omega) a)) s * v s := by
    intro v
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  simp only [Hpk_eI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.transpose_apply]
  exact level_point_first_lines k r j hj Z τ γ a p

/- English proof (translation)
Unfold `x0`. Apply `castM_GV'` to reduce the goal to its premises. Conclude with `(Ux2.sliceMem k (j + 1) (r - (j + 1))).1 _ _ (by rw [det_zfull]; exact mul_ne_zero hZ hτ) hγ`.
-/
theorem x0_GV (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  unfold x0
  apply castM_GV'
  exact (Ux2.sliceMem k (j + 1) (r - (j + 1))).1 _ _ (by rw [det_zfull]; exact mul_ne_zero hZ hτ) hγ

/- English proof (translation)
Introduce `k r j hj Z τ γ hZ hτ hγ`. Conclude with `⟨x0_GV k r j hj Z τ γ hZ hτ hγ, fun a ha => absurd ha (by simp)⟩`.
-/
theorem xiMem : XiMem := by
  intro k r j hj Z τ γ hZ hτ hγ
  exact ⟨x0_GV k r j hj Z τ γ hZ hτ hγ, fun a ha => absurd ha (by simp)⟩

/- English proof (translation)
Introduce `k r j hj Z τ γ hZ hτ hγ a p`. Establish `hinv` using `PBG.inv_GV (x0_GV k r j hj Z τ γ hZ hτ hγ)`. Rewrite using `[hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `hH : Hpk k r *ᵥ bvec (eI k r (Fin.castLE (by omega) a)) = bvec (esI k r (Fin.castLE (by omega) a))`. Use extensionality with `s`.

Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Hpk_eI_col, Pi.single_apply]`. Rewrite using `[hH]`. Simplify using `only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Simplify using `only [Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]`.

Use `split_ifs with hp`. Rewrite using `[Fintype.sum_eq_single ⟨2 * r + k - p.val, by omega⟩]`. Establish `hH1 : Hpk k r p ⟨2 * r + k - p.val, by omega⟩ = 1`. Rewrite using `[Hpk_low _ _ _ _ (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk]; omega)]`. Rewrite using `[hH1, one_mul, dif_pos (by simp only [Fin.val_mk]; omega)]`.

Both sides reduce to the same expression. Introduce `s hs`. Distinguish the cases in `h : s.val < j`. Rewrite using `[dif_pos h]`. Establish `: Hpk k r p s = 0`.

Rewrite using `[Hpk_low _ _ _ _ (by omega), if_neg (by intro h'; apply hs; ext; simp only [Fin.val_mk]; omega)]`. Rewrite using `[this, zero_mul]`. Rewrite using `[dif_neg h, star_zero, mul_zero]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : s.val < j`.

Rewrite using `[dif_pos h]`. Establish `: Hpk k r p s = 0`. Rewrite using `[Hpk_low _ _ _ _ (by omega), if_neg (by omega)]`. Rewrite using `[this, zero_mul]`. Rewrite using `[dif_neg h, star_zero, mul_zero]`.
-/
theorem xiCoefV : XiCoefV := by
  intro k r j hj Z τ γ hZ hτ hγ a p
  have hinv := PBG.inv_GV (x0_GV k r j hj Z τ γ hZ hτ hγ)
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hH : Hpk k r *ᵥ bvec (eI k r (Fin.castLE (by omega) a)) = bvec (esI k r (Fin.castLE (by omega) a)) := by
    ext s
    simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Hpk_eI_col, Pi.single_apply]
  rw [hH]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  simp only [Matrix.mulVec, dotProduct]
  simp only [Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  split_ifs with hp
  · rw [Fintype.sum_eq_single ⟨2 * r + k - p.val, by omega⟩]
    · have hH1 : Hpk k r p ⟨2 * r + k - p.val, by omega⟩ = 1 := by
        rw [Hpk_low _ _ _ _ (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk]; omega)]
      rw [hH1, one_mul, dif_pos (by simp only [Fin.val_mk]; omega)]
      rfl
    · intro s hs
      by_cases h : s.val < j
      · rw [dif_pos h]
        have : Hpk k r p s = 0 := by
          rw [Hpk_low _ _ _ _ (by omega), if_neg (by intro h'; apply hs; ext; simp only [Fin.val_mk]; omega)]
        rw [this, zero_mul]
      · rw [dif_neg h, star_zero, mul_zero]
  · refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h : s.val < j
    · rw [dif_pos h]
      have : Hpk k r p s = 0 := by
        rw [Hpk_low _ _ _ _ (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · rw [dif_neg h, star_zero, mul_zero]

section smooth

variable {j : ℕ}

/- English proof (translation)
Simplify using `only [zfull_apply]`. Use `split_ifs`. Conclude with `contDiff_apply_apply ℝ ℂ _ _`. Conclude with `contDiff_const`. Conclude with `contDiff_const`.

Conclude with `contDiff_const`.
-/
theorem contDiff_zfull (τ : ℂ) (c d : Fin (j + 1)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun Z : MJ j => zfull Z τ c d) := by
  simp only [zfull_apply]
  split_ifs
  · exact contDiff_apply_apply ℝ ℂ _ _
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Apply `PBG.contDiff_det'` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`.

Conclude with `contDiff_const`. Conclude with `contDiff_zfull τ a b`.
-/
theorem contDiff_adj_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiff ℝ ⊤ (fun Z : MJ j => (zfull Z τ).adjugate c d) := by
  simp only [Matrix.adjugate_apply]
  apply PBG.contDiff_det'
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_zfull τ a b

/- English proof (translation)
Establish `he : ∀ Z : MJ j, (zfull Z τ)⁻¹ c d = (Z.det)⁻¹ * τ⁻¹ * (zfull Z τ).adjugate c d`. Introduce `Z`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, det_zfull, Ring.inverse_eq_inv', mul_inv, smul_eq_mul]`. Simplify using `only [he]`. Establish `hdet : ContDiff ℝ ⊤ (fun Z : MJ j => Z.det)` using `PBG.contDiff_det' (fun Z : MJ j => Z) (fun a b => contDiff_apply_apply ℝ ℂ a b)`.

Conclude with `((((hdet.of_le le_top).contDiffOn.inv (fun Z hZ => hZ)).mul contDiffOn_const).mul ((contDiff_adj_zfull τ c d).of_le le_top).contDiffOn)`.
-/
theorem contDiffOn_inv_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (zfull Z τ)⁻¹ c d) {Z | Z.det ≠ 0} := by
  have he : ∀ Z : MJ j, (zfull Z τ)⁻¹ c d = (Z.det)⁻¹ * τ⁻¹ * (zfull Z τ).adjugate c d := by
    intro Z
    rw [Matrix.inv_def, Matrix.smul_apply, det_zfull, Ring.inverse_eq_inv', mul_inv, smul_eq_mul]
  simp only [he]
  have hdet : ContDiff ℝ ⊤ (fun Z : MJ j => Z.det) :=
    PBG.contDiff_det' (fun Z : MJ j => Z) (fun a b => contDiff_apply_apply ℝ ℂ a b)
  exact ((((hdet.of_le le_top).contDiffOn.inv (fun Z hZ => hZ)).mul contDiffOn_const).mul
    ((contDiff_adj_zfull τ c d).of_le le_top).contDiffOn)

/- English proof (translation)
Take `⟨x, hx⟩ : ∃ x, U.eB k (j + 1) (r - (j + 1)) x = Fin.cast (by omega) p` from `⟨_, Equiv.apply_symm_apply _ _⟩`. Take `⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q` from `⟨_, Equiv.apply_symm_apply _ _⟩`. Establish `he : ∀ Z : MJ j, x0 k r j hj Z τ γ p q = Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 γ) (Matrix.fromRows ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) 0) (Matrix.fromCols (G.wMat (j + 1) * zfull Z τ) 0) 0 x y`. Introduce `Z`. Unfold `x0 U.mMap`.

Rewrite using `[castM_apply', ← hx, ← hy, Ux4.block3_apply]`. Simplify using `only [he]`. Establish `h13 : ∀ c d : Fin (j + 1), ContDiffOn ℝ ∞ (fun Z : MJ j => ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) c d) {Z | Z.det ≠ 0}`. Introduce `c d`. Simplify using `only [Matrix.mul_apply, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply]`.

Conclude with `ContDiffOn.sum fun t _ => (PBG.contDiff_starC.comp_contDiffOn (contDiffOn_inv_zfull τ t c)).mul contDiffOn_const`. Establish `h31 : ∀ c d : Fin (j + 1), ContDiffOn ℝ ∞ (fun Z : MJ j => (G.wMat (j + 1) * zfull Z τ) c d) {Z | Z.det ≠ 0}`. Introduce `c d`. Simplify using `only [Matrix.mul_apply]`. Conclude with `ContDiffOn.sum fun t _ => contDiffOn_const.mul (contDiff_zfull τ t d).contDiffOn`.

Apply the tactic sequence `rcases x with ((c | c) | c) <;> rcases y with ((d | d) | d) <;>`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply]`. Conclude with `contDiffOn_const`. Conclude with `contDiffOn_const`. Conclude with `h13 c d`.

Conclude with `contDiffOn_const`. Conclude with `contDiffOn_const`. Conclude with `contDiffOn_const`. Conclude with `h31 c d`. Conclude with `contDiffOn_const`.

Conclude with `contDiffOn_const`.
-/
theorem level_point_entry_contDiffOn (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (p q : Fin (2 * r + k + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ p q) {Z | Z.det ≠ 0} := by
  obtain ⟨x, hx⟩ : ∃ x, U.eB k (j + 1) (r - (j + 1)) x = Fin.cast (by omega) p := ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  have he : ∀ Z : MJ j, x0 k r j hj Z τ γ p q =
      Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 γ) (Matrix.fromRows ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) 0)
        (Matrix.fromCols (G.wMat (j + 1) * zfull Z τ) 0) 0 x y := by
    intro Z
    unfold x0 U.mMap
    rw [castM_apply', ← hx, ← hy, Ux4.block3_apply]
  simp only [he]
  have h13 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun t _ =>
      (PBG.contDiff_starC.comp_contDiffOn (contDiffOn_inv_zfull τ t c)).mul contDiffOn_const
  have h31 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => (G.wMat (j + 1) * zfull Z τ) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun t _ => contDiffOn_const.mul (contDiff_zfull τ t d).contDiffOn
  rcases x with ((c | c) | c) <;> rcases y with ((d | d) | d) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h13 c d
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h31 c d
  · exact contDiffOn_const
  · exact contDiffOn_const

/- English proof (translation)
Introduce `k r j hj τ γ`. Conclude with `contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => level_point_entry_contDiffOn k r j hj τ γ p q`.
-/
theorem xiSmooth : XiSmooth := by
  intro k r j hj τ γ
  exact contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => level_point_entry_contDiffOn k r j hj τ γ p q

end smooth

end Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `WirtingerOperators.XiPf.xiCoef`.
-/
theorem xi_coefficient : WirtingerOperators.XiCoef := WirtingerOperators.XiPf.xiCoef

/- English proof (translation)
The claim follows from `WirtingerOperators.XiPf.xiCoefV`.
-/
theorem xi_coefficient_vector : WirtingerOperators.XiCoefV := WirtingerOperators.XiPf.xiCoefV

/- English proof (translation)
The claim follows from `WirtingerOperators.XiPf.xiMem`.
-/
theorem xiMem_statement : WirtingerOperators.XiMem := WirtingerOperators.XiPf.xiMem

/- English proof (translation)
The claim follows from `WirtingerOperators.XiPf.xiSmooth`.
-/
theorem xi_smooth : WirtingerOperators.XiSmooth := WirtingerOperators.XiPf.xiSmooth

end Formalism.FourierDecayAlt.P
