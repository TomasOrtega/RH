import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfN

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def bmul (a b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (mat a τ * mat b τ : Matrix (Fin r) (Fin r) ℂ)

def binv (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `first`. Consider the case `exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)`. Consider the case `(ext i j; simp [rmul, bmul, mat, Matrix.mul_assoc])`.
-/
theorem rmul_rmul (x a b : Frame X.Ψ r) : rmul (rmul x a) b = rmul x (bmul X a b) := by
  funext τ
  first
    | exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)
    | (ext i j; simp [rmul, bmul, mat, Matrix.mul_assoc])

/- English proof (translation)
Simplify using `only [Bor, Set.mem_setOf_eq] at ha hb ⊢`. Introduce `τ`. Take `⟨ha1, ha2⟩` from `ha τ`. Take `⟨hb1, hb2⟩` from `hb τ`. Establish `hA : Matrix.BlockTriangular (mat a τ) id`.

Introduce `i j h`. Conclude with `ha2 i j h`. Establish `hB : Matrix.BlockTriangular (mat b τ) id`. Introduce `i j h`. Conclude with `hb2 i j h`.

Use `⟨?_, fun i j h => hA.mul hB h⟩` and prove the remaining obligations. Use `show (mat a τ * mat b τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero ha1 hb1`.
-/
theorem bmul_mem {a b : Frame X.Ψ r} (ha : a ∈ Bor X.Ψ r) (hb : b ∈ Bor X.Ψ r) :
    bmul X a b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1

/- English proof (translation)
Simplify using `only [Bor, Set.mem_setOf_eq] at hb ⊢`. Introduce `τ`. Take `⟨hb1, hb2⟩` from `hb τ`. Establish `hB : Matrix.BlockTriangular (mat b τ) id`. Introduce `i j h`.

Conclude with `hb2 i j h`. Use `haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)`. Establish `hI : Matrix.BlockTriangular (mat b τ)⁻¹ id` using `Matrix.blockTriangular_inv_of_blockTriangular hB`. Use `⟨?_, fun i j h => hI h⟩` and prove the remaining obligations. Use `show ((mat b τ)⁻¹).det ≠ 0`.

Conclude with `(Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero`.
-/
theorem binv_mem {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : binv X b ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => hI h⟩
  show ((mat b τ)⁻¹).det ≠ 0
  exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero

/- English proof (translation)
Simplify using `only [Bor, Set.mem_setOf_eq] at hb`. Use function extensionality and compare the values at `τ`. Establish `h` using `isUnit_iff_ne_zero.mpr (hb τ).1`. Use `show mat x τ * mat b τ * (mat b τ)⁻¹ = x τ`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ h]`.

Both sides reduce to the same expression.
-/
theorem rmul_binv (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (rmul x b) (binv X b) = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * (mat b τ)⁻¹ = x τ
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Conclude with `(Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm`.
-/
theorem lact_rmul (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ`. Rewrite using `[Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem lact_lact (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[lact_lact, inv_mul_cancel]`. Use function extensionality and compare the values at `τ`. Use `show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ`. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]`. Apply the tactic sequence `try rfl`.
-/
theorem lact_inv (γ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact, inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl

/- English proof (translation)
Introduce `z hz b hb h1`. Establish `hbc : ∀ c ∈ Bor X.Ψ r, bchar Xa.L c ≠ 0`. Introduce `c hc`. Simplify using `only [Bor, Set.mem_setOf_eq] at hc`. Unfold `bchar`.

Use `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_` and prove the remaining obligations. Take `⟨hd, ht⟩` from `hc τ`. Establish `hT : Matrix.BlockTriangular (mat c τ) id`. Introduce `a e h`. Conclude with `ht a e h`.

Rewrite `hd` using `[Matrix.det_of_upperTriangular hT]`. Conclude with `(Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ _)`. Establish `hzdom : cpt X x0 z ∈ X.dom` using `hball hz`. Establish `hsz : ∀ k, Fl.s k (cpt X x0 z) = 0`. Introduce `k`.

Establish `hv` using `Fl.s_van k`. Simplify using `only [Data.SSgt, Data.SS, Data.IsBddSec, Data.IsSec, Set.mem_setOf_eq] at hv`. Establish `hsec` using `hv.1.1.1.2.1 (cpt X x0 z) hzdom b hb`. Establish `h0` using `hs1 k`. Rewrite `h0` using `[h1, hsec]`.

Conclude with `(mul_eq_zero.mp h0).resolve_left (hbc b hb)`. Establish `hz0 : z = 0` using `hiso z hz hsz`. Establish `hc0 : cpt X x0 0 = x0`. Use function extensionality and compare the values at `τ`. Establish `hm : mat (nmat X 0) τ = 1`.

Use extensionality with `a e`. Distinguish the cases in `h : e < a`. Establish `hne : a ≠ e` using `ne_of_gt h`. Simplify using `only [mat, nmat, Matrix.of_apply, dif_pos h, Matrix.one_apply_ne hne]`. Apply the tactic sequence `all_goals first | rfl | simp`.

Simplify using `only [mat, nmat, Matrix.of_apply, dif_neg h, Matrix.one_apply]`. Use `show mat x0 τ * mat (nmat X 0) τ = x0 τ`. Rewrite using `[hm, Matrix.mul_one]`. Both sides reduce to the same expression. Establish `hx0 : rmul (Fl.xs j) (binv X b0) = x0`.

Rewrite using `[hx]`. Conclude with `rmul_binv X x0 hb0`. Establish `hcB : bmul X (binv X b0) (bmul X b b1) ∈ Bor X.Ψ r` using `bmul_mem X (binv_mem X hb0) (bmul_mem X hb hb1)`. Establish `hy' : lact γ (Fl.xs j') = rmul (Fl.xs j) (bmul X (binv X b0) (bmul X b b1))`. Rewrite using `[hy, h1, hz0, hc0, ← hx0, rmul_rmul X, rmul_rmul X]`.

Establish `hj` using `congrArg (lact γ⁻¹) hy'`. Rewrite `hj` using `[lact_inv]`. Establish `hjj : j = j'` using `Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hcB hj`. Substitute `hjj` using the available equality. Establish `hγ1 : γ = 1` using `X.Γ_free γ hγ (Fl.xs j) (Fl.xs_mem j) _ hcB hy'`.

Break down `hne with h | h` into its components or cases. Conclude with `h hγ1`. Conclude with `h rfl`.
-/
theorem avoid_base (Xa : ArchInM X) (Fl : FlatM X Xa) (j j' : Fin Fl.δ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (hne : γ ≠ 1 ∨ j' ≠ j) (x0 b0 : Frame X.Ψ r) (hb0 : b0 ∈ Bor X.Ψ r)
    (hx : Fl.xs j = rmul x0 b0) (x1 b1 : Frame X.Ψ r) (hb1 : b1 ∈ Bor X.Ψ r)
    (hy : lact γ (Fl.xs j') = rmul x1 b1) (ε : ℝ)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hs1 : ∀ k, Fl.s k x1 = 0) :
    ∀ z ∈ closedBall (0 : V (nd X)) (2 * ε), ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b := by
  intro z hz b hb h1
  have hbc : ∀ c ∈ Bor X.Ψ r, bchar Xa.L c ≠ 0 := by
    intro c hc
    simp only [Bor, Set.mem_setOf_eq] at hc
    unfold bchar
    refine Finset.prod_ne_zero_iff.mpr fun τ _ =>
      Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_
    obtain ⟨hd, ht⟩ := hc τ
    have hT : Matrix.BlockTriangular (mat c τ) id := by
      intro a e h
      exact ht a e h
    rw [Matrix.det_of_upperTriangular hT] at hd
    exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ _)
  have hzdom : cpt X x0 z ∈ X.dom := hball hz
  have hsz : ∀ k, Fl.s k (cpt X x0 z) = 0 := by
    intro k
    have hv := Fl.s_van k
    simp only [Data.SSgt, Data.SS, Data.IsBddSec, Data.IsSec, Set.mem_setOf_eq] at hv
    have hsec := hv.1.1.1.2.1 (cpt X x0 z) hzdom b hb
    have h0 := hs1 k
    rw [h1, hsec] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hbc b hb)
  have hz0 : z = 0 := hiso z hz hsz
  have hc0 : cpt X x0 0 = x0 := by
    funext τ
    have hm : mat (nmat X 0) τ = 1 := by
      ext a e
      by_cases h : e < a
      · have hne : a ≠ e := ne_of_gt h
        simp only [mat, nmat, Matrix.of_apply, dif_pos h, Matrix.one_apply_ne hne]
        all_goals first | rfl | simp
      · simp only [mat, nmat, Matrix.of_apply, dif_neg h, Matrix.one_apply]
    show mat x0 τ * mat (nmat X 0) τ = x0 τ
    rw [hm, Matrix.mul_one]
    rfl
  have hx0 : rmul (Fl.xs j) (binv X b0) = x0 := by
    rw [hx]
    exact rmul_binv X x0 hb0
  have hcB : bmul X (binv X b0) (bmul X b b1) ∈ Bor X.Ψ r :=
    bmul_mem X (binv_mem X hb0) (bmul_mem X hb hb1)
  have hy' : lact γ (Fl.xs j') = rmul (Fl.xs j) (bmul X (binv X b0) (bmul X b b1)) := by
    rw [hy, h1, hz0, hc0, ← hx0, rmul_rmul X, rmul_rmul X]
  have hj := congrArg (lact γ⁻¹) hy'
  rw [lact_inv] at hj
  have hjj : j = j' := Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hcB hj
  subst hjj
  have hγ1 : γ = 1 := X.Γ_free γ hγ (Fl.xs j) (Fl.xs_mem j) _ hcB hy'
  rcases hne with h | h
  · exact h hγ1
  · exact h rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
