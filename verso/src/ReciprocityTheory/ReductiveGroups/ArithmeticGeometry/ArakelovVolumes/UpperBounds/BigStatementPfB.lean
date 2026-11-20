import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModelNefness
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def Hf (X : Data E r) (Xa : ArchInM X) (x : Frame X.Ψ r) : ℝ :=
  (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ (1 / ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ)) /
    (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2

/- English proof (translation)
The claim follows from `(Xa.w_van k).1.1.1`.
-/
theorem w_sec (X : Data E r) (Xa : ArchInM X) (k : Fin Xa.N) : X.IsSec Xa.L (Xa.w k) :=
  (Xa.w_van k).1.1.1

/- English proof (translation)
Take `⟨k, hk⟩` from `Xa.w_nz x hx`. Establish `hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re` using `hx`. Establish `hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0`. Introduce `τ i h0`. Establish `h1` using `(hd' τ).2 i`.

Rewrite `h1` using `[h0]`. Simplify using `at h1`. Establish `hp : 0 < X.pnorm Xa.L (Xa.w k) x`. Unfold `Data.pnorm`. Apply `mul_pos (norm_pos_iff.mpr hk)` to reduce the goal to its premises.

Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `τ _`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises.

Conclude with `norm_pos_iff.mpr (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem S_pos (X : Data E r) (Xa : ArchInM X) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  obtain ⟨k, hk⟩ := Xa.w_nz x hx
  have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  have hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  have hp : 0 < X.pnorm Xa.L (Xa.w k) x := by
    unfold Data.pnorm
    apply mul_pos (norm_pos_iff.mpr hk)
    apply Finset.prod_pos
    intro τ _
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    exact norm_pos_iff.mpr (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))
  calc (0 : ℝ) < X.pnorm Xa.L (Xa.w k) x ^ 2 := by positivity
    _ ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
      Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Xa.w k) x ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
private theorem gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G N = Matrix.transpose N * G.map τ * N.map (starRingEnd ℂ) := by
  ext a c
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use `symm`. Conclude with `Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ f (fun k hk => hf k (by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hk ⟨⟨k, h⟩, rfl⟩)) (fun _ => rfl)`.
-/
private theorem sum_eq_sum_castLE_of_eq_zero {i : ℕ} (hi : i ≤ r) (f : Fin r → ℂ)
    (hf : ∀ k : Fin r, i ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin i, f (Fin.castLE hi k) := by
  symm
  exact Fintype.sum_of_injective (Fin.castLE hi) (Fin.castLE_injective hi) _ f
    (fun k hk => hf k (by
      by_contra h
      push_neg at h
      exact hk ⟨⟨k, h⟩, rfl⟩)) (fun _ => rfl)

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]`. Rewrite using `[sum_eq_sum_castLE_of_eq_zero hi]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[sum_eq_sum_castLE_of_eq_zero hi]`.

Introduce `k hk`. Establish `ha` using `a.isLt`. Rewrite using `[hB k (Fin.castLE hi a) (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]`. Introduce `l hl`. Establish `hc` using `c.isLt`.

Rewrite using `[hC l (Fin.castLE hi c) (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]`.
-/
private theorem submatrix_castLE_transpose_mul_mul_of_triangular {i : ℕ} (hi : i ≤ r) (B A C : Matrix (Fin r) (Fin r) ℂ)
    (hB : ∀ k c : Fin r, c < k → B k c = 0) (hC : ∀ k c : Fin r, c < k → C k c = 0) :
    (Matrix.transpose B * A * C).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      Matrix.transpose (B.submatrix (Fin.castLE hi) (Fin.castLE hi)) *
        A.submatrix (Fin.castLE hi) (Fin.castLE hi) * C.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [sum_eq_sum_castLE_of_eq_zero hi]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_eq_sum_castLE_of_eq_zero hi]
    intro k hk
    have ha := a.isLt
    rw [hB k (Fin.castLE hi a) (by rw [Fin.lt_def, Fin.coe_castLE]; omega), zero_mul]
  · intro l hl
    have hc := c.isLt
    rw [hC l (Fin.castLE hi c) (by rw [Fin.lt_def, Fin.coe_castLE]; omega), mul_zero]

/- English proof (translation)
Establish `hB : ∀ k c : Fin r, c < k → mat b τ k c = 0` using `fun k c h => (hb τ).2 k c h`. Establish `hC : ∀ k c : Fin r, c < k → (mat b τ).map (starRingEnd ℂ) k c = 0` using `fun k c h => by`. Simplify using `[Matrix.map_apply, hB k c h]`. Establish `hm : mat (rmul x b) τ = mat x τ * mat b τ` using `rfl`. Establish `hdc : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det` using `fun M => (RingHom.map_det _ M).symm`.

Unfold `dmin lminor`. Rewrite using `[hm, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]`. Rewrite using `[show Matrix.transpose (mat b τ) * Matrix.transpose (mat x τ) * X.Gm.map τ.1 * ((mat x τ).map (starRingEnd ℂ) * (mat b τ).map (starRingEnd ℂ)) = Matrix.transpose (mat b τ) * (Matrix.transpose (mat x τ) * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) * (mat b τ).map (starRingEnd ℂ …`. Rewrite using `[submatrix_castLE_transpose_mul_mul_of_triangular _ _ _ _ hB hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.submatrix_map, hdc, ← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dmin_rmul_eq_normSq_lminor_mul (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) :
    dmin X.Gm (rmul x b) τ i = ((Complex.normSq (lminor (mat b τ) i) : ℝ) : ℂ) * dmin X.Gm x τ i := by
  have hB : ∀ k c : Fin r, c < k → mat b τ k c = 0 := fun k c h => (hb τ).2 k c h
  have hC : ∀ k c : Fin r, c < k → (mat b τ).map (starRingEnd ℂ) k c = 0 := fun k c h => by
    simp [Matrix.map_apply, hB k c h]
  have hm : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  have hdc : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ),
      (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := fun M => (RingHom.map_det _ M).symm
  unfold dmin lminor
  rw [hm, gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  rw [show Matrix.transpose (mat b τ) * Matrix.transpose (mat x τ) * X.Gm.map τ.1 *
      ((mat x τ).map (starRingEnd ℂ) * (mat b τ).map (starRingEnd ℂ)) =
      Matrix.transpose (mat b τ) * (Matrix.transpose (mat x τ) * X.Gm.map τ.1 *
        (mat x τ).map (starRingEnd ℂ)) * (mat b τ).map (starRingEnd ℂ) by simp only [Matrix.mul_assoc]]
  rw [submatrix_castLE_transpose_mul_mul_of_triangular _ _ _ _ hB hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.submatrix_map, hdc, ← Complex.mul_conj]
  ring

/- English proof (translation)
Establish `hd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re` using `hx`. Use `show ∀ τ : X.Ψ, (mat (rmul x b) τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (rmul x b) τ i).re`. Introduce `τ`. Establish `hBt : (mat b τ).BlockTriangular id` using `fun k c h => (hb τ).2 k c h`. Establish `hdetB : (mat b τ).det ≠ 0` using `(hb τ).1`.

Establish `hdiag : ∀ j : Fin r, mat b τ j j ≠ 0`. Introduce `j hj`. Apply `hdetB` to reduce the goal to its premises. Rewrite using `[Matrix.det_of_upperTriangular hBt]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) hj`.

Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `show (mat x τ * mat b τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hd τ).1 hdetB`. Rewrite using `[dmin_rmul_eq_normSq_lminor_mul X hb τ i, Complex.re_ofReal_mul]`.

Establish `hpos : 0 < Complex.normSq (lminor (mat b τ) i)`. Rewrite using `[Complex.normSq_pos]`. Unfold `lminor`. Establish `hBs : ((mat b τ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt))).BlockTriangular id` using `fun k c h => hBt (by exact h)`. Rewrite using `[Matrix.det_of_upperTriangular hBs]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => hdiag _`. Establish `h1` using `(hd τ).2 i`. Use polynomial arithmetic with `[mul_pos hpos h1]`.
-/
private theorem rmul_mem_dom_of_mem_bor' (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ X.dom := by
  have hd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (rmul x b) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (rmul x b) τ i).re
  intro τ
  have hBt : (mat b τ).BlockTriangular id := fun k c h => (hb τ).2 k c h
  have hdetB : (mat b τ).det ≠ 0 := (hb τ).1
  have hdiag : ∀ j : Fin r, mat b τ j j ≠ 0 := by
    intro j hj
    apply hdetB
    rw [Matrix.det_of_upperTriangular hBt]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hd τ).1 hdetB
  · rw [dmin_rmul_eq_normSq_lminor_mul X hb τ i, Complex.re_ofReal_mul]
    have hpos : 0 < Complex.normSq (lminor (mat b τ) i) := by
      rw [Complex.normSq_pos]
      unfold lminor
      have hBs : ((mat b τ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
          (Fin.castLE (Nat.le_of_lt_succ i.isLt))).BlockTriangular id := fun k c h => hBt (by exact h)
      rw [Matrix.det_of_upperTriangular hBs]
      exact Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have h1 := (hd τ).2 i
    nlinarith [mul_pos hpos h1]

/- English proof (translation)
Unfold `cc`. Use `first`. Consider the case `exact NumberField.IsCMField.complexEmbedding_complexConj τ a`. Consider the case `exact IsCMField.complexEmbedding_complexConj τ a`. Consider the case `simp`.
-/
private theorem ringHom_cc_eq_starRingEnd (τ : E →+* ℂ) (a : E) : τ (cc a) = starRingEnd ℂ (τ a) := by
  unfold cc
  first
  | exact NumberField.IsCMField.complexEmbedding_complexConj τ a
  | exact IsCMField.complexEmbedding_complexConj τ a
  | simp

/- English proof (translation)
Establish `h1` using `h (Pi.single a 1) (Pi.single b 1)`. Establish `hs : ∀ c : Fin r, Matrix.mulVec g (Pi.single c (1 : E)) = fun k => g k c` using `fun c => by`. Use function extensionality and compare the values at `k`. Use `first`. Consider the case `simp [Matrix.mulVec_single]`.

Consider the case `simp [Matrix.mulVec, Pi.single_apply]`. Simplify using `only [hs] at h1`. Unfold `herm at h1`. Rewrite using `[h1]`. Establish `hcs : ∀ l : Fin r, cc ((Pi.single b (1 : E) : Fin r → E) l) = (Pi.single b (1 : E) : Fin r → E) l` using `fun l => by`.

Distinguish the cases in `hl : l = b`. Rewrite using `[Pi.single_apply, if_pos hl]`. Unfold `cc`. Conclude with `map_one (IsCMField.complexConj E)`. Rewrite using `[Pi.single_apply, if_neg hl]`.

Unfold `cc`. Conclude with `map_zero (IsCMField.complexConj E)`. Simplify using `only [hcs]`. Rewrite using `[Fintype.sum_eq_single a, Fintype.sum_eq_single b]`. Simplify using the standard rewrite rules.

Introduce `l hl`. Simplify using `[Pi.single_apply, hl]`. Introduce `k hk`. Simplify using `[Pi.single_apply, hk]`.
-/
private theorem sum_mul_mul_cc_eq_of_herm_mulVec {G g : Matrix (Fin r) (Fin r) E}
    (h : ∀ x y, herm G (Matrix.mulVec g x) (Matrix.mulVec g y) = herm G x y) (a b : Fin r) :
    ∑ k, ∑ l, g k a * G k l * cc (g l b) = G a b := by
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have hs : ∀ c : Fin r, Matrix.mulVec g (Pi.single c (1 : E)) = fun k => g k c := fun c => by
    funext k
    first
    | simp [Matrix.mulVec_single]
    | simp [Matrix.mulVec, Pi.single_apply]
  simp only [hs] at h1
  unfold herm at h1
  rw [h1]
  have hcs : ∀ l : Fin r, cc ((Pi.single b (1 : E) : Fin r → E) l) = (Pi.single b (1 : E) : Fin r → E) l :=
    fun l => by
    by_cases hl : l = b
    · rw [Pi.single_apply, if_pos hl]
      unfold cc
      exact map_one (IsCMField.complexConj E)
    · rw [Pi.single_apply, if_neg hl]
      unfold cc
      exact map_zero (IsCMField.complexConj E)
  simp only [hcs]
  rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp
  · intro l hl
    simp [Pi.single_apply, hl]
  · intro k hk
    simp [Pi.single_apply, hk]

/- English proof (translation)
Establish `hM : Matrix.transpose (g.map τ) * G.map τ * (g.map τ).map (starRingEnd ℂ) = G.map τ`. Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[← hg a b]`. Simplify using `only [map_sum, map_mul, ringHom_cc_eq_starRingEnd]`.

Conclude with `Finset.sum_comm`. Establish `hE : ∀ u w : Fin r → ℂ, hermC τ G u w = u ⬝ᵥ (Matrix.mulVec (G.map τ) (starRingEnd ℂ ∘ w))`. Introduce `u w`. Simplify using `only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, Finset.mul_sum, mul_assoc]`. Establish `hc : starRingEnd ℂ ∘ (Matrix.mulVec (g.map τ) w) = Matrix.mulVec ((g.map τ).map (starRingEnd ℂ)) (starRingEnd ℂ ∘ w)`.

Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (starRingEnd ℂ) (g.map τ) w i`. Rewrite using `[hE, hE, hc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM, Matrix.dotProduct_mulVec]`.
-/
private theorem hermC_mulVec_map_of_gram_invariant (τ : E →+* ℂ) (G g : Matrix (Fin r) (Fin r) E)
    (hg : ∀ a b, ∑ k, ∑ l, g k a * G k l * cc (g l b) = G a b) (u w : Fin r → ℂ) :
    hermC τ G (Matrix.mulVec (g.map τ) u) (Matrix.mulVec (g.map τ) w) = hermC τ G u w := by
  have hM : Matrix.transpose (g.map τ) * G.map τ * (g.map τ).map (starRingEnd ℂ) = G.map τ := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [← hg a b]
    simp only [map_sum, map_mul, ringHom_cc_eq_starRingEnd]
    exact Finset.sum_comm
  have hE : ∀ u w : Fin r → ℂ, hermC τ G u w = u ⬝ᵥ (Matrix.mulVec (G.map τ) (starRingEnd ℂ ∘ w)) := by
    intro u w
    simp only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, Finset.mul_sum,
      mul_assoc]
  have hc : starRingEnd ℂ ∘ (Matrix.mulVec (g.map τ) w) =
      Matrix.mulVec ((g.map τ).map (starRingEnd ℂ)) (starRingEnd ℂ ∘ w) := by
    funext i
    exact RingHom.map_mulVec (starRingEnd ℂ) (g.map τ) w i
  rw [hE, hE, hc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hM, Matrix.dotProduct_mulVec]

/- English proof (translation)
Establish `hK` using `sum_mul_mul_cc_eq_of_herm_mulVec (X.Γ_stab γ hγ).1`. Establish `hcol : ∀ a, col (mat (lact γ y) τ) a = Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (col (mat y τ) a)` using `fun a => rfl`. Establish `hgr : gram τ.1 X.Gm (mat (lact γ y) τ) = gram τ.1 X.Gm (mat y τ)`. Use extensionality with `a c`. Simplify using `only [gram, Matrix.of_apply, hcol, hermC_mulVec_map_of_gram_invariant τ.1 X.Gm _ hK]`.

Unfold `dmin`. Rewrite using `[hgr]`.
-/
private theorem dmin_lact_eq_of_mem_Γ (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y : Frame X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm (lact γ y) τ i = dmin X.Gm y τ i := by
  have hK := sum_mul_mul_cc_eq_of_herm_mulVec (X.Γ_stab γ hγ).1
  have hcol : ∀ a, col (mat (lact γ y) τ) a =
      Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (col (mat y τ) a) := fun a => rfl
  have hgr : gram τ.1 X.Gm (mat (lact γ y) τ) = gram τ.1 X.Gm (mat y τ) := by
    ext a c
    simp only [gram, Matrix.of_apply, hcol, hermC_mulVec_map_of_gram_invariant τ.1 X.Gm _ hK]
  unfold dmin
  rw [hgr]

/- English proof (translation)
Establish `hxb` using `rmul_mem_dom_of_mem_bor' X hx hb`. Establish `hPv : P (lact γ (rmul x b)) = X.χ la γ * (bchar la b * P x)`. Rewrite using `[hP.2.2 γ hγ _ hxb, hP.2.1 x hx b hb]`. Establish `hχ : ‖X.χ la γ‖ = 1`. Take `⟨n, hn, h⟩` from `X.χ_fin la`.

Establish `h1` using `congrArg norm (h γ hγ)`. Rewrite `h1` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1`. Establish `hBt : ∀ τ : X.Ψ, (mat b τ).BlockTriangular id` using `fun τ k c h => (hb τ).2 k c h`. Establish `hdiag : ∀ (τ : X.Ψ) (j : Fin r), b τ j j ≠ 0`.

Introduce `τ j hj`. Apply `(hb τ).1` to reduce the goal to its premises. Rewrite using `[Matrix.det_of_upperTriangular (hBt τ)]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) hj`. Establish `hsub : ∀ (τ : X.Ψ) (n : ℕ) (h : n ≤ r), ((mat b τ).submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id` using `fun τ n h k c hkc => hBt τ (by exact hkc)`.

Establish `hlm0 : ∀ (τ : X.Ψ) (j : Fin (r + 1)), lminor (mat b τ) j ≠ 0`. Introduce `τ j`. Unfold `lminor`. Rewrite using `[Matrix.det_of_upperTriangular (hsub τ _ _)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => hdiag τ _`.

Establish `key : ∀ (τ : X.Ψ) (n : ℕ) (hn : n + 1 ≤ r), (∏ j : Fin (n + 1), b τ (Fin.castLE hn j) (Fin.castLE hn j)) = (∏ j : Fin n, b τ (Fin.castLE (Nat.le_of_succ_le hn) j) (Fin.castLE (Nat.le_of_succ_le hn) j)) * b τ ⟨n, hn⟩ ⟨n, hn⟩`. Introduce `τ n hn`. Rewrite using `[Fin.prod_univ_castSucc]`. Both sides reduce to the same expression. Establish `hlm : ∀ (τ : X.Ψ) (i : Fin r), lminor (mat b τ) i.succ = lminor (mat b τ) i.castSucc * b τ i i`.

Introduce `τ i`. Unfold `lminor`. Rewrite using `[Matrix.det_of_upperTriangular (hsub τ _ _), Matrix.det_of_upperTriangular (hsub τ _ _)]`. Conclude with `key τ i i.isLt`. Establish `hratio : ∀ (τ : X.Ψ) (i : Fin r), ‖dmin X.Gm (lact γ (rmul x b)) τ i.succ / dmin X.Gm (lact γ (rmul x b)) τ i.castSucc‖ = Complex.normSq (b τ i i) * ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖`.

Introduce `τ i`. Establish `hn0 : Complex.normSq (lminor (mat b τ) i.castSucc) ≠ 0` using `(Complex.normSq_pos.2 (hlm0 τ _)).ne'`. Rewrite using `[dmin_lact_eq_of_mem_Γ X hγ, dmin_lact_eq_of_mem_Γ X hγ, dmin_rmul_eq_normSq_lminor_mul X hb, dmin_rmul_eq_normSq_lminor_mul X hb, hlm, map_mul, Complex.ofReal_mul, mul_assoc, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.2 hn0), mul_div_assoc, norm_mul, Complex.norm_of_nonneg (Co …`. Establish `hfac : ∀ (z : ℂ) (m : ℤ), z ≠ 0 → ‖z‖ ^ m * (Complex.normSq z) ^ (-(m : ℝ) / 2) = 1`. Introduce `z m hz`.

Establish `hn : 0 < ‖z‖` using `norm_pos_iff.2 hz`. Rewrite using `[Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_intCast, ← Real.rpow_add hn, show ((m : ℝ) + ((2 : ℕ) : ℝ) * (-(m : ℝ) / 2)) = 0 by push_cast; ring, Real.rpow_zero]`. Establish `hbc : ‖bchar la b‖ * ∏ τ, ∏ i : Fin r, Complex.normSq (b τ i i) ^ (-(la τ i : ℝ) / 2) = 1`. Unfold `bchar`. Rewrite using `[norm_prod, ← Finset.prod_mul_distrib]`.

Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `τ _`. Rewrite using `[norm_prod, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[norm_zpow]`. Conclude with `hfac _ _ (hdiag τ i)`. Unfold `Data.pnorm`. Rewrite using `[hPv]`. Simplify using `only [hratio]`.

Rewrite using `[norm_mul, norm_mul, hχ, one_mul]`. Simplify using `only [Real.mul_rpow (Complex.normSq_nonneg _) (norm_nonneg _), Finset.prod_mul_distrib]`. Take the linear combination `(‖P x‖ * ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) * hbc`.
-/
private theorem pnorm_lact_rmul_of_isSec (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x := by
  have hxb := rmul_mem_dom_of_mem_bor' X hx hb
  have hPv : P (lact γ (rmul x b)) = X.χ la γ * (bchar la b * P x) := by
    rw [hP.2.2 γ hγ _ hxb, hP.2.1 x hx b hb]
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have h1 := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
  have hBt : ∀ τ : X.Ψ, (mat b τ).BlockTriangular id := fun τ k c h => (hb τ).2 k c h
  have hdiag : ∀ (τ : X.Ψ) (j : Fin r), b τ j j ≠ 0 := by
    intro τ j hj
    apply (hb τ).1
    rw [Matrix.det_of_upperTriangular (hBt τ)]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  have hsub : ∀ (τ : X.Ψ) (n : ℕ) (h : n ≤ r),
      ((mat b τ).submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id :=
    fun τ n h k c hkc => hBt τ (by exact hkc)
  have hlm0 : ∀ (τ : X.Ψ) (j : Fin (r + 1)), lminor (mat b τ) j ≠ 0 := by
    intro τ j
    unfold lminor
    rw [Matrix.det_of_upperTriangular (hsub τ _ _)]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hdiag τ _
  have key : ∀ (τ : X.Ψ) (n : ℕ) (hn : n + 1 ≤ r),
      (∏ j : Fin (n + 1), b τ (Fin.castLE hn j) (Fin.castLE hn j)) =
        (∏ j : Fin n, b τ (Fin.castLE (Nat.le_of_succ_le hn) j) (Fin.castLE (Nat.le_of_succ_le hn) j)) *
          b τ ⟨n, hn⟩ ⟨n, hn⟩ := by
    intro τ n hn
    rw [Fin.prod_univ_castSucc]
    rfl
  have hlm : ∀ (τ : X.Ψ) (i : Fin r),
      lminor (mat b τ) i.succ = lminor (mat b τ) i.castSucc * b τ i i := by
    intro τ i
    unfold lminor
    rw [Matrix.det_of_upperTriangular (hsub τ _ _), Matrix.det_of_upperTriangular (hsub τ _ _)]
    exact key τ i i.isLt
  have hratio : ∀ (τ : X.Ψ) (i : Fin r),
      ‖dmin X.Gm (lact γ (rmul x b)) τ i.succ / dmin X.Gm (lact γ (rmul x b)) τ i.castSucc‖ =
        Complex.normSq (b τ i i) * ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ := by
    intro τ i
    have hn0 : Complex.normSq (lminor (mat b τ) i.castSucc) ≠ 0 :=
      (Complex.normSq_pos.2 (hlm0 τ _)).ne'
    rw [dmin_lact_eq_of_mem_Γ X hγ, dmin_lact_eq_of_mem_Γ X hγ, dmin_rmul_eq_normSq_lminor_mul X hb, dmin_rmul_eq_normSq_lminor_mul X hb, hlm, map_mul,
      Complex.ofReal_mul, mul_assoc, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.2 hn0), mul_div_assoc, norm_mul,
      Complex.norm_of_nonneg (Complex.normSq_nonneg _)]
  have hfac : ∀ (z : ℂ) (m : ℤ), z ≠ 0 → ‖z‖ ^ m * (Complex.normSq z) ^ (-(m : ℝ) / 2) = 1 := by
    intro z m hz
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_intCast,
      ← Real.rpow_add hn, show ((m : ℝ) + ((2 : ℕ) : ℝ) * (-(m : ℝ) / 2)) = 0 by push_cast; ring,
      Real.rpow_zero]
  have hbc : ‖bchar la b‖ * ∏ τ, ∏ i : Fin r, Complex.normSq (b τ i i) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    rw [norm_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    rw [norm_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    rw [norm_zpow]
    exact hfac _ _ (hdiag τ i)
  unfold Data.pnorm
  rw [hPv]
  simp only [hratio]
  rw [norm_mul, norm_mul, hχ, one_mul]
  simp only [Real.mul_rpow (Complex.normSq_nonneg _) (norm_nonneg _), Finset.prod_mul_distrib]
  linear_combination (‖P x‖ * ∏ τ, ∏ i : Fin r,
    ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) * hbc

/- English proof (translation)
Establish `hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ (rmul x b)) = X.pnorm Xa.L (Xa.w k) x` using `fun k => pnorm_lact_rmul_of_isSec X Xa.L (w_sec X Xa k) hγ hx hb`. Unfold `Hf`. Rewrite using `[pnorm_lact_rmul_of_isSec X _ Xa.et_sec hγ hx hb]`. Simplify using `only [hw]`.
-/
theorem Hf_inv (X : Data E r) (Xa : ArchInM X) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    Hf X Xa (lact γ (rmul x b)) = Hf X Xa x := by
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ (rmul x b)) = X.pnorm Xa.L (Xa.w k) x :=
    fun k => pnorm_lact_rmul_of_isSec X Xa.L (w_sec X Xa k) hγ hx hb
  unfold Hf
  rw [pnorm_lact_rmul_of_isSec X _ Xa.et_sec hγ hx hb]
  simp only [hw]

/- English proof (translation)
Establish `hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i`. Introduce `τ i`. Unfold `dmin lminor`. Apply `Continuous.matrix_det` to reduce the goal to its premises. Apply `continuous_pi` to reduce the goal to its premises.

Introduce `a`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `b`. Simplify using `only [Matrix.submatrix_apply, gram, hermC, Matrix.of_apply, mat, col]`. Use `fun_prop`.

Establish `hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0`. Introduce `x hx τ i h0`. Establish `hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re` using `hx`. Establish `h1` using `(hd' τ).2 i`. Rewrite `h1` using `[h0]`.

Simplify using `at h1`. Unfold `Data.pnorm`. Apply `ContinuousOn.mul` to reduce the goal to its premises. Conclude with `continuous_norm.comp_continuousOn hP.1.continuousOn`. Apply `continuousOn_finset_prod` to reduce the goal to its premises.

Introduce `τ _`. Apply `continuousOn_finset_prod` to reduce the goal to its premises. Introduce `i _`. Apply `ContinuousOn.rpow_const` to reduce the goal to its premises. Conclude with `(((hd τ i.succ).continuousOn).div (hd τ i.castSucc).continuousOn (fun x hx => hne x hx τ i.castSucc)).norm`.

Introduce `x hx left`. Conclude with `norm_ne_zero_iff.mpr (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))`.
-/
theorem pnorm_contOn (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    apply Continuous.matrix_det
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    simp only [Matrix.submatrix_apply, gram, hermC, Matrix.of_apply, mat, col]
    fun_prop
  have hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro x hx τ i h0
    have hd' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
    have h1 := (hd' τ).2 i
    rw [h0] at h1
    simp at h1
  unfold Data.pnorm
  apply ContinuousOn.mul
  · exact continuous_norm.comp_continuousOn hP.1.continuousOn
  · apply continuousOn_finset_prod
    intro τ _
    apply continuousOn_finset_prod
    intro i _
    apply ContinuousOn.rpow_const
    · exact (((hd τ i.succ).continuousOn).div (hd τ i.castSucc).continuousOn
        (fun x hx => hne x hx τ i.castSucc)).norm
    · intro x hx
      left
      exact norm_ne_zero_iff.mpr (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))

/- English proof (translation)
Establish `hw : ∀ k, ContinuousOn (X.pnorm Xa.L (Xa.w k)) X.dom` using `fun k => pnorm_contOn X Xa.L (w_sec X Xa k)`. Establish `he : ContinuousOn (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et) X.dom` using `pnorm_contOn X _ Xa.et_sec`. Unfold `Hf`. Apply `ContinuousOn.div` to reduce the goal to its premises. Apply `ContinuousOn.rpow_const (he.pow 2)` to reduce the goal to its premises.

Introduce `x _`. Use `right`. Check the signs of the components of the expression. Conclude with `(continuousOn_finset_sum _ fun k _ => (hw k).pow 2).pow 2`. Introduce `x hx`.

Conclude with `pow_ne_zero _ (S_pos X Xa hx).ne'`.
-/
theorem Hf_contOn (X : Data E r) (Xa : ArchInM X) : ContinuousOn (Hf X Xa) X.dom := by
  have hw : ∀ k, ContinuousOn (X.pnorm Xa.L (Xa.w k)) X.dom :=
    fun k => pnorm_contOn X Xa.L (w_sec X Xa k)
  have he : ContinuousOn (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et) X.dom :=
    pnorm_contOn X _ Xa.et_sec
  unfold Hf
  apply ContinuousOn.div
  · apply ContinuousOn.rpow_const (he.pow 2)
    intro x _
    right
    positivity
  · exact (continuousOn_finset_sum _ fun k _ => (hw k).pow 2).pow 2
  · intro x hx
    exact pow_ne_zero _ (S_pos X Xa hx).ne'

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. It suffices to derive a contradiction. Substitute `hr` using the available equality. Establish `h` using `Xa.n_ge`. Establish `h0 : nd X = 0`.

Unfold `nd`. Rewrite using `[Fintype.card_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨⟨a, _⟩, _⟩⟩`. Conclude with `a.elim0`.

Use linear arithmetic over natural numbers and integers. Conclude with `hr`.
-/
theorem r_pos (X : Data E r) (Xa : ArchInM X) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h := Xa.n_ge
    have h0 : nd X = 0 := by
      unfold nd
      rw [Fintype.card_eq_zero_iff]
      constructor
      rintro ⟨_, ⟨⟨a, _⟩, _⟩⟩
      exact a.elim0
    omega
  · exact hr

/- English proof (translation)
Establish `hr` using `r_pos X Xa`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥`. Rewrite using `[Submodule.span_le]`.

Introduce `v hv`. Simplify using `[h v hv]`. Rewrite `h1` using `[X.Λ_span, top_le_iff]`. Establish `hm : (fun _ => (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E))` using `Submodule.mem_top`. Rewrite `hm` using `[← h1, Submodule.mem_bot]`.

Conclude with `one_ne_zero (congrFun hm ⟨0, hr⟩)`.
-/
theorem lam_ne (X : Data E r) (Xa : ArchInM X) : ∃ v ∈ X.Λ, v ≠ 0 := by
  have hr := r_pos X Xa
  by_contra h
  push_neg at h
  have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
    rw [Submodule.span_le]
    intro v hv
    simp [h v hv]
  rw [X.Λ_span, top_le_iff] at h1
  have hm : (fun _ => (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
  rw [← h1, Submodule.mem_bot] at hm
  exact one_ne_zero (congrFun hm ⟨0, hr⟩)

/- English proof (translation)
Take `⟨K4, hK4⟩` from `Xa.p4`. Take `⟨K3, hK3⟩` from `Xa.p3`. Take `⟨ca, ε0, hca, hε0, hp1⟩` from `Xa.p1`. Take `⟨g2, hg2⟩` from `Xa.genus_even`. Establish `hg0 : Xa.g0 = 2 * g2` using `by omega`.

Establish `hg2p : 1 ≤ g2` using `by have := Xa.genus_pos; omega`. Establish `hdiv : Xa.g0 / 2 = g2` using `by omega`. Use `set k0 : ℝ := ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) with hk0`. Establish `hi : (1 : ℝ) ≤ Xa.i` using `by exact_mod_cast Xa.i_pos`. Establish `hg2r : (1 : ℝ) ≤ g2` using `by exact_mod_cast hg2p`.

Establish `hg : (2 : ℝ) ≤ Xa.g0` using `by rw [hg0]; push_cast; linarith`. Establish `hk0e : k0 = Xa.i * ((Xa.g0 : ℝ) / 2)` using `by rw [hk0, hdiv, hg0]; push_cast; ring`. Establish `hk0p : 0 < k0` using `by rw [hk0e]; positivity`. Establish `hc` using `Xa.c_pos`. Establish `hT : (44 : ℝ) ≤ Xa.T`.

Establish `h1` using `Xa.T_ge`. Establish `h2` using `Xa.n_ge`. Establish `: 44 ≤ Xa.T` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Establish `hcg : Xa.c * Xa.g0 < 1`.

Use `Xa.Tcg0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hcl : Xa.c < 1 / (Xa.g0 : ℝ)` using `by rw [lt_div_iff₀ (by linarith)]; linarith`. Use `set β : ℝ := 4 * (1 / (Xa.g0 : ℝ) - Xa.c) * ca with hβ`. Establish `hβ0 : 0 < β`.

Establish `: 0 < 1 / (Xa.g0 : ℝ) - Xa.c` using `by linarith`. Check the signs of the components of the expression. Use `set K : ℝ := max ((max K4 0) ^ (1 / k0) * (max K3 0) ^ 2) 1 with hK`. Establish `hK1 : 1 ≤ K` using `le_max_right _ _`. Use `set M : ℝ := max (Real.log (K / h1)) 0 + 1 with hM`.

Establish `hM0 : 0 < M` using `by positivity`. Use `⟨min ε0 (Real.sqrt (β / M)), lt_min hε0 (Real.sqrt_pos.mpr (by positivity)), fun x hx hl => ?_⟩` and prove the remaining obligations. Establish `hlpos : 0 < X.la1 x` using `ModeHalfC.first_minimum_pos X hx (lam_ne X Xa)`. Establish `hl0 : X.la1 x < ε0` using `lt_of_lt_of_le hl (min_le_left _ _)`. Establish `hl1 : X.la1 x < Real.sqrt (β / M)` using `lt_of_lt_of_le hl (min_le_right _ _)`.

Establish `hph : ca / X.la1 x ^ 2 ≤ Xa.ph x` using `hp1 x hx hl0`. Establish `hS` using `S_pos X Xa hx`. Establish `hA : (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ (1 / k0) ≤ (max K4 0) ^ (1 / k0) * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)`. Establish `h1` using `(hK4 x hx).trans (mul_le_mul_of_nonneg_right (le_max_left K4 0) (Real.exp_pos _).le)`. Establish `h2` using `Real.rpow_le_rpow (sq_nonneg _) h1 (by positivity : (0 : ℝ) ≤ 1 / k0)`.

Rewrite `h2` using `[Real.mul_rpow (le_max_right _ _) (Real.exp_pos _).le, ← Real.exp_mul]`. Use `h2 using 3` and compare the differences between its conclusion and the goal. Rewrite using `[hk0e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hS' : Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ max K3 0 * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2` using `(hK3 x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS.le)`. Establish `hK3p : 0 < max K3 0`. Assume the negation of the conclusion as `h0`. Establish `: max K3 0 = 0` using `le_antisymm (not_lt.mp h0) (le_max_right _ _)`. Rewrite `hS'` using `[this, zero_mul]`.

Conclude with `absurd hS' (not_le.mpr (Real.exp_pos _))`. Establish `hS2 : Real.exp (-(4 * Xa.c * Xa.ph x)) ≤ (max K3 0) ^ 2 * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2`. Establish `e : Real.exp (-(4 * Xa.c * Xa.ph x)) = Real.exp (-(2 * Xa.c * Xa.ph x)) ^ 2`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (Real.exp_pos _).le hS' 2`. Establish `hexp : Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) ≤ Real.exp (-(β / X.la1 x ^ 2)) * Real.exp (-(4 * Xa.c * Xa.ph x))`.

Rewrite using `[← Real.exp_add]`. Use `Real.exp_le_exp.mpr ?_` and prove the remaining obligations. Establish `h4 : β / X.la1 x ^ 2 = 4 * (1 / (Xa.g0 : ℝ) - Xa.c) * (ca / X.la1 x ^ 2)`. Rewrite using `[hβ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Establish `h6` using `mul_le_mul_of_nonneg_left hph (by`. Establish `: 0 ≤ 1 / (Xa.g0 : ℝ) - Xa.c` using `by linarith`. Use `positivity : (0 : ℝ) ≤ 4 * (1 / (Xa.g0 : ℝ) - Xa.c))`. Establish `h7 : -(4 / (Xa.g0 : ℝ)) * Xa.ph x = -(4 * (1 / (Xa.g0 : ℝ) - Xa.c)) * Xa.ph x - 4 * Xa.c * Xa.ph x`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h7]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hH : Hf X Xa x ≤ K * Real.exp (-(β / X.la1 x ^ 2))`. Unfold `Hf`.

Establish `hS2p : 0 < (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2` using `by positivity`. Rewrite using `[div_le_iff₀ hS2p]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hexp.trans (mul_le_mul_of_nonneg_left hS2 (Real.exp_pos _).le)`. Use `_ = ((max K4 0) ^ (1 / k0) * (max K3 0) ^ 2) * Real.exp (-(β / X.la1 x ^ 2)) * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2 := by ring`.

Use `_ ≤ K * Real.exp (-(β / X.la1 x ^ 2)) * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2 := by gcongr`. Conclude with `le_max_left _ _`. Establish `hl2 : X.la1 x ^ 2 < β / M`. Use `Real.sq_sqrt (show 0 ≤ β / M by positivity)` as an intermediate fact. Use polynomial arithmetic with `[Real.sqrt_nonneg (β / M)]`.

Establish `hbig : M < β / X.la1 x ^ 2`. Rewrite using `[lt_div_iff₀ (by positivity)]`. Rewrite `hl2` using `[lt_div_iff₀ hM0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : Real.log (K / h1) < β / X.la1 x ^ 2`.

Establish `: Real.log (K / h1) ≤ M - 1` using `by rw [hM]; simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin : K * Real.exp (-(β / X.la1 x ^ 2)) < h1`. Establish `h1' : Real.exp (-(β / X.la1 x ^ 2)) < h1 / K`. Rewrite using `[show h1 / K = Real.exp (-Real.log (K / h1)) by`.

Rewrite using `[Real.exp_neg, Real.exp_log (by positivity), inv_div]]`. Conclude with `Real.exp_lt_exp.mpr (by linarith)`. Rewrite `h1'` using `[lt_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Hf_small (X : Data E r) (Xa : ArchInM X) {h1 : ℝ} (hh1 : 0 < h1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, X.la1 x < ε → Hf X Xa x < h1 := by
  obtain ⟨K4, hK4⟩ := Xa.p4
  obtain ⟨K3, hK3⟩ := Xa.p3
  obtain ⟨ca, ε0, hca, hε0, hp1⟩ := Xa.p1
  obtain ⟨g2, hg2⟩ := Xa.genus_even
  have hg0 : Xa.g0 = 2 * g2 := by omega
  have hg2p : 1 ≤ g2 := by have := Xa.genus_pos; omega
  have hdiv : Xa.g0 / 2 = g2 := by omega
  set k0 : ℝ := ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) with hk0
  have hi : (1 : ℝ) ≤ Xa.i := by exact_mod_cast Xa.i_pos
  have hg2r : (1 : ℝ) ≤ g2 := by exact_mod_cast hg2p
  have hg : (2 : ℝ) ≤ Xa.g0 := by rw [hg0]; push_cast; linarith
  have hk0e : k0 = Xa.i * ((Xa.g0 : ℝ) / 2) := by rw [hk0, hdiv, hg0]; push_cast; ring
  have hk0p : 0 < k0 := by rw [hk0e]; positivity
  have hc := Xa.c_pos
  have hT : (44 : ℝ) ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    have : 44 ≤ Xa.T := by nlinarith
    exact_mod_cast this
  have hcg : Xa.c * Xa.g0 < 1 := by
    have := Xa.Tcg0
    nlinarith
  have hcl : Xa.c < 1 / (Xa.g0 : ℝ) := by rw [lt_div_iff₀ (by linarith)]; linarith
  set β : ℝ := 4 * (1 / (Xa.g0 : ℝ) - Xa.c) * ca with hβ
  have hβ0 : 0 < β := by
    have : 0 < 1 / (Xa.g0 : ℝ) - Xa.c := by linarith
    positivity
  set K : ℝ := max ((max K4 0) ^ (1 / k0) * (max K3 0) ^ 2) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  set M : ℝ := max (Real.log (K / h1)) 0 + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨min ε0 (Real.sqrt (β / M)), lt_min hε0 (Real.sqrt_pos.mpr (by positivity)), fun x hx hl => ?_⟩
  have hlpos : 0 < X.la1 x := ModeHalfC.first_minimum_pos X hx (lam_ne X Xa)
  have hl0 : X.la1 x < ε0 := lt_of_lt_of_le hl (min_le_left _ _)
  have hl1 : X.la1 x < Real.sqrt (β / M) := lt_of_lt_of_le hl (min_le_right _ _)
  have hph : ca / X.la1 x ^ 2 ≤ Xa.ph x := hp1 x hx hl0
  have hS := S_pos X Xa hx
  have hA : (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ (1 / k0) ≤
      (max K4 0) ^ (1 / k0) * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) := by
    have h1 := (hK4 x hx).trans (mul_le_mul_of_nonneg_right (le_max_left K4 0) (Real.exp_pos _).le)
    have h2 := Real.rpow_le_rpow (sq_nonneg _) h1 (by positivity : (0 : ℝ) ≤ 1 / k0)
    rw [Real.mul_rpow (le_max_right _ _) (Real.exp_pos _).le, ← Real.exp_mul] at h2
    convert h2 using 3
    rw [hk0e]; field_simp; ring
  have hS' : Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ max K3 0 * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    (hK3 x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS.le)
  have hK3p : 0 < max K3 0 := by
    by_contra h0
    have : max K3 0 = 0 := le_antisymm (not_lt.mp h0) (le_max_right _ _)
    rw [this, zero_mul] at hS'
    exact absurd hS' (not_le.mpr (Real.exp_pos _))
  have hS2 : Real.exp (-(4 * Xa.c * Xa.ph x)) ≤ (max K3 0) ^ 2 * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2 := by
    have e : Real.exp (-(4 * Xa.c * Xa.ph x)) = Real.exp (-(2 * Xa.c * Xa.ph x)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hS' 2
  have hexp : Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) ≤
      Real.exp (-(β / X.la1 x ^ 2)) * Real.exp (-(4 * Xa.c * Xa.ph x)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h4 : β / X.la1 x ^ 2 = 4 * (1 / (Xa.g0 : ℝ) - Xa.c) * (ca / X.la1 x ^ 2) := by
      rw [hβ]; ring
    rw [h4]
    have h6 := mul_le_mul_of_nonneg_left hph (by
      have : 0 ≤ 1 / (Xa.g0 : ℝ) - Xa.c := by linarith
      positivity : (0 : ℝ) ≤ 4 * (1 / (Xa.g0 : ℝ) - Xa.c))
    have h7 : -(4 / (Xa.g0 : ℝ)) * Xa.ph x = -(4 * (1 / (Xa.g0 : ℝ) - Xa.c)) * Xa.ph x - 4 * Xa.c * Xa.ph x := by
      ring
    rw [h7]; linarith
  have hH : Hf X Xa x ≤ K * Real.exp (-(β / X.la1 x ^ 2)) := by
    unfold Hf
    have hS2p : 0 < (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2 := by positivity
    rw [div_le_iff₀ hS2p]
    calc (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ (1 / k0)
        ≤ (max K4 0) ^ (1 / k0) * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) := hA
      _ ≤ (max K4 0) ^ (1 / k0) * (Real.exp (-(β / X.la1 x ^ 2)) *
            ((max K3 0) ^ 2 * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2)) := by
          gcongr
          exact hexp.trans (mul_le_mul_of_nonneg_left hS2 (Real.exp_pos _).le)
      _ = ((max K4 0) ^ (1 / k0) * (max K3 0) ^ 2) * Real.exp (-(β / X.la1 x ^ 2)) *
            (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2 := by ring
      _ ≤ K * Real.exp (-(β / X.la1 x ^ 2)) * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ 2 := by
          gcongr
          exact le_max_left _ _
  have hl2 : X.la1 x ^ 2 < β / M := by
    have := Real.sq_sqrt (show 0 ≤ β / M by positivity)
    nlinarith [Real.sqrt_nonneg (β / M)]
  have hbig : M < β / X.la1 x ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ hM0] at hl2
    linarith
  have hlog : Real.log (K / h1) < β / X.la1 x ^ 2 := by
    have : Real.log (K / h1) ≤ M - 1 := by rw [hM]; simp
    linarith
  have hfin : K * Real.exp (-(β / X.la1 x ^ 2)) < h1 := by
    have h1' : Real.exp (-(β / X.la1 x ^ 2)) < h1 / K := by
      rw [show h1 / K = Real.exp (-Real.log (K / h1)) by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]]
      exact Real.exp_lt_exp.mpr (by linarith)
    rw [lt_div_iff₀ (by linarith)] at h1'
    linarith
  linarith

/- English proof (translation)
Take `⟨x1, hx1, he1⟩` from `Xa.et_ne`. Establish `hH1 : 0 < Hf X Xa x1`. Unfold `Hf`. Establish `hp : 0 < X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x1` using `mul_pos (norm_pos_iff.mpr he1) (BoundedSectionAlgebra.nfac_pos X hx1 _)`. Conclude with `div_pos (Real.rpow_pos_of_pos (by positivity) _) (pow_pos (S_pos X Xa hx1) 2)`.

Take `⟨ε, hε, hsmall⟩` from `Hf_small X Xa hH1`. Take `⟨Kc, hKc, hKsub, hrep⟩` from `reductionTheory_holds r X ε hε`. Establish `hl1 : ε ≤ X.la1 x1`. Assume the negation of the conclusion as `h`. Conclude with `lt_irrefl _ (hsmall x1 hx1 (not_le.mp h))`.

Take `⟨γ1, hγ1, b1, hb1, hy1⟩` from `hrep x1 hx1 hl1`. Take `⟨xs, hxs, hmax⟩` from `hKc.exists_isMaxOn ⟨_, hy1⟩ ((Hf_contOn X Xa).mono hKsub)`. Establish `hy1H : Hf X Xa (lact γ1 (rmul x1 b1)) = Hf X Xa x1` using `Hf_inv X Xa hγ1 hx1 hb1`. Establish `hge : Hf X Xa x1 ≤ Hf X Xa xs` using `hy1H ▸ hmax hy1`. Use `⟨xs, hKsub hxs, lt_of_lt_of_le hH1 hge, fun x hx => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hl : ε ≤ X.la1 x`. Take `⟨γ, hγ, b, hb, hy⟩` from `hrep x hx hl`. Rewrite using `[← Hf_inv X Xa hγ hx hb]`. Conclude with `hmax hy`. Conclude with `((hsmall x hx (not_le.mp hl)).trans_le hge).le`.
-/
theorem exists_max (X : Data E r) (Xa : ArchInM X) :
    ∃ xs ∈ X.dom, 0 < Hf X Xa xs ∧ ∀ x ∈ X.dom, Hf X Xa x ≤ Hf X Xa xs := by
  obtain ⟨x1, hx1, he1⟩ := Xa.et_ne
  have hH1 : 0 < Hf X Xa x1 := by
    unfold Hf
    have hp : 0 < X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x1 :=
      mul_pos (norm_pos_iff.mpr he1) (BoundedSectionAlgebra.nfac_pos X hx1 _)
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (pow_pos (S_pos X Xa hx1) 2)
  obtain ⟨ε, hε, hsmall⟩ := Hf_small X Xa hH1
  obtain ⟨Kc, hKc, hKsub, hrep⟩ := reductionTheory_holds r X ε hε
  have hl1 : ε ≤ X.la1 x1 := by
    by_contra h
    exact lt_irrefl _ (hsmall x1 hx1 (not_le.mp h))
  obtain ⟨γ1, hγ1, b1, hb1, hy1⟩ := hrep x1 hx1 hl1
  obtain ⟨xs, hxs, hmax⟩ := hKc.exists_isMaxOn ⟨_, hy1⟩ ((Hf_contOn X Xa).mono hKsub)
  have hy1H : Hf X Xa (lact γ1 (rmul x1 b1)) = Hf X Xa x1 := Hf_inv X Xa hγ1 hx1 hb1
  have hge : Hf X Xa x1 ≤ Hf X Xa xs := hy1H ▸ hmax hy1
  refine ⟨xs, hKsub hxs, lt_of_lt_of_le hH1 hge, fun x hx => ?_⟩
  by_cases hl : ε ≤ X.la1 x
  · obtain ⟨γ, hγ, b, hb, hy⟩ := hrep x hx hl
    rw [← Hf_inv X Xa hγ hx hb]
    exact hmax hy
  · exact ((hsmall x hx (not_le.mp hl)).trans_le hge).le

end BigB

end ReciprocityTheory.ChartRestriction.G.AR.Up
