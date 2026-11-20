import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfG

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

namespace SchubertCoordinates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Conclude with `(EuclideanSpace.proj (𝕜 := ℂ) i).differentiable`.
-/
theorem diff_coord {n : ℕ} (i : Fin n) : Differentiable ℂ fun v : V n => v i := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable

/- English proof (translation)
Unfold `nmat`. Use `split_ifs`. Conclude with `diff_coord _`. Conclude with `differentiable_const _`. Conclude with `differentiable_const _`.
-/
theorem diff_nmat (X : FD.Data E r) (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  split_ifs
  · exact diff_coord _
  · exact differentiable_const _
  · exact differentiable_const _

/- English proof (translation)
Unfold `cpt rmul`. Use `differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [mat, Matrix.mul_apply, Matrix.of_apply]`. Conclude with `Differentiable.fun_sum fun k _ => (differentiable_const _).mul (diff_nmat X τ k b)`.
-/
theorem diff_cpt (X : FD.Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  unfold cpt rmul
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [mat, Matrix.mul_apply, Matrix.of_apply]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (diff_nmat X τ k b)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [mat, nmat, Matrix.of_apply, Matrix.one_apply]`. Distinguish the cases in `h1 : b < a`. Establish `h2 : a ≠ b` using `fun h => by subst h; exact lt_irrefl _ h1`. Simplify using `[h1, h2]`.

Both sides reduce to the same expression. Simplify using `[h1]`.
-/
theorem nmat_zero (X : FD.Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : b < a
  · have h2 : a ≠ b := fun h => by subst h; exact lt_irrefl _ h1
    simp [h1, h2]
    rfl
  · simp [h1]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (mat x τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x τ`. Rewrite using `[nmat_zero, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem cpt_zero (X : FD.Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  funext τ
  show (mat x τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [nmat_zero, Matrix.mul_one]
  rfl

/- English proof (translation)
Apply `continuous_pi` to reduce the goal to its premises. Introduce `a`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `b`. Simplify using `only [gram, hermC, col, mat, Matrix.of_apply]`.

Use `fun_prop`.
-/
theorem cont_gram (X : FD.Data E r) (τ : X.Ψ) :
    Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Establish `hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det` using `fun τ => Continuous.matrix_det (continuous_apply τ)`. Establish `hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re`. Introduce `τ i`. Use `Complex.continuous_re.comp ?_` and prove the remaining obligations. Unfold `dmin lminor`.

Conclude with `Continuous.matrix_det ((cont_gram X τ).matrix_submatrix _ _)`. Establish `hset : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩ ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re})`. Use extensionality with `x`. Simplify using `[FD.Data.dom, GG, Set.mem_iInter]`. Rewrite using `[hset]`.

Use `isOpen_iInter_of_finite fun τ => IsOpen.inter (isOpen_ne_fun (hdet τ) continuous_const) (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))` and prove the remaining obligations.
-/
theorem isOpen_dom (X : FD.Data E r) : IsOpen X.dom := by
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
    intro τ i
    refine Complex.continuous_re.comp ?_
    unfold dmin lminor
    exact Continuous.matrix_det ((cont_gram X τ).matrix_submatrix _ _)
  have hset : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [FD.Data.dom, GG, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter (isOpen_ne_fun (hdet τ) continuous_const)
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))

end SchubertCoordinates

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `d c r X sg R Xa hD e t hH x hx hs hw0`. Take `⟨hd, -, -, ht, -⟩` from `hH`. Take `⟨j0, jj, hj0, hJ⟩` from `R.coordAt x hx`. Take `⟨W, hWdef⟩ : ∃ W : Fin (d.N + 1) → Frame X.Ψ r → ℂ, W = fun j => R.rd ⟨d.w j c, R.w_mem j⟩` from `⟨_, rfl⟩`. Establish `hsW : ∀ i y, sR d c R t hD i y = ∑ j, t ((Fin.cast hD i).succ, j) * W j y` using `fun i y => by`.

Rewrite using `[hWdef]`. Both sides reduce to the same expression. Establish `hw0W : ∀ y, w0R d c R t y = ∑ j, t (0, j) * W j y` using `fun y => by rw [hWdef]; rfl`. Establish `hWd : ∀ j, DifferentiableOn ℂ (W j) X.dom` using `fun j => by`. Rewrite using `[hWdef]`.

Conclude with `(R.sec d.wL R.wL_mem _ (R.w_mem j) (hd.w_mem j c)).1`. Establish `hw0ne : d.w j0 c ≠ 0`. Introduce `h`. Apply `hj0` to reduce the goal to its premises. Establish `h0 : (⟨d.w j0 c, R.w_mem j0⟩ : R.Rg) = 0` using `Subtype.ext h`.

Rewrite using `[h0, map_zero]`. Both sides reduce to the same expression. Establish `hWu : ∀ y ∈ R.Gen, ∀ j, W j y = R.pt y (ratio (Ω` using `Ω c) (d.w j c) (d.w j0 c)) * W j0 y := fun y hy j => by`. Rewrite using `[hWdef]`. Conclude with `R.ratio_rd d.wL _ (R.w_mem j) _ (R.w_mem j0) (hd.w_mem j c) (hd.w_mem j0 c) hw0ne y hy`.

Establish `hpt : ∀ y ∈ R.Gen, (R.pt y).comp (algebraMap K (Ω c)) = sg` using `fun y hy => R.pt_mem y hy`. Establish `hx0 : W j0 x ≠ 0` using `by rw [hWdef]; exact hj0`. Establish `hJ' : (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => W (jj k) (cpt X x z) / W j0 (cpt X x z) : V (nd X))) 0).det ≠ 0`. Rewrite using `[hWdef]`. Conclude with `hJ`.

Establish `hfun : (fun z : V (nd X) => (WithLp.toLp 2 fun i => sR d c R t hD i (cpt X x z) / w0R d c R t (cpt X x z) : V (nd X))) = fun z : V (nd X) => (WithLp.toLp 2 fun i => (∑ j, t ((Fin.cast hD i).succ, j) * W j (cpt X x z)) / (∑ j, t (0, j) * W j (cpt X x z)) : V (nd X))`. Use function extensionality and compare the values at `z`. Simplify using `only [hsW, hw0W]`. Rewrite using `[hfun]`. Conclude with `SCoF.core hD sg (SchubertCoordinates.isOpen_dom X) R.Gen_sub R.Gen_dense R.pt hpt (hd.trdeg c) W hWd (fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) j0 hWu (cpt X x) (SchubertCoordinates.diff_cpt X x) (SchubertCoordinates.cpt_zero X x) hx hx0 jj hJ' t ht (fun i => by rw [← hsW]; …`.
-/
theorem SCoordStatement_holds :
    SCoordStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) (E := E) := by
  intro d c r X sg R Xa hD e t hH x hx hs hw0
  obtain ⟨hd, -, -, ht, -⟩ := hH
  obtain ⟨j0, jj, hj0, hJ⟩ := R.coordAt x hx
  obtain ⟨W, hWdef⟩ : ∃ W : Fin (d.N + 1) → Frame X.Ψ r → ℂ,
      W = fun j => R.rd ⟨d.w j c, R.w_mem j⟩ := ⟨_, rfl⟩
  have hsW : ∀ i y, sR d c R t hD i y = ∑ j, t ((Fin.cast hD i).succ, j) * W j y := fun i y => by
    rw [hWdef]; rfl
  have hw0W : ∀ y, w0R d c R t y = ∑ j, t (0, j) * W j y := fun y => by rw [hWdef]; rfl
  have hWd : ∀ j, DifferentiableOn ℂ (W j) X.dom := fun j => by
    rw [hWdef]; exact (R.sec d.wL R.wL_mem _ (R.w_mem j) (hd.w_mem j c)).1
  have hw0ne : d.w j0 c ≠ 0 := by
    intro h
    apply hj0
    have h0 : (⟨d.w j0 c, R.w_mem j0⟩ : R.Rg) = 0 := Subtype.ext h
    rw [h0, map_zero]
    rfl
  have hWu : ∀ y ∈ R.Gen, ∀ j, W j y = R.pt y (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) * W j0 y :=
    fun y hy j => by
      rw [hWdef]
      exact R.ratio_rd d.wL _ (R.w_mem j) _ (R.w_mem j0) (hd.w_mem j c) (hd.w_mem j0 c) hw0ne y hy
  have hpt : ∀ y ∈ R.Gen, (R.pt y).comp (algebraMap K (Ω c)) = sg := fun y hy => R.pt_mem y hy
  have hx0 : W j0 x ≠ 0 := by rw [hWdef]; exact hj0
  have hJ' : (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      W (jj k) (cpt X x z) / W j0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    rw [hWdef]; exact hJ
  have hfun : (fun z : V (nd X) => (WithLp.toLp 2 fun i =>
      sR d c R t hD i (cpt X x z) / w0R d c R t (cpt X x z) : V (nd X))) =
      fun z : V (nd X) => (WithLp.toLp 2 fun i =>
        (∑ j, t ((Fin.cast hD i).succ, j) * W j (cpt X x z)) / (∑ j, t (0, j) * W j (cpt X x z)) :
          V (nd X)) := by
    funext z
    simp only [hsW, hw0W]
  rw [hfun]
  exact SCoF.core hD sg (SchubertCoordinates.isOpen_dom X) R.Gen_sub R.Gen_dense R.pt hpt (hd.trdeg c) W hWd
    (fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) j0 hWu (cpt X x) (SchubertCoordinates.diff_cpt X x)
    (SchubertCoordinates.cpt_zero X x) hx hx0 jj hJ' t ht (fun i => by rw [← hsW]; exact hs i)
    (by rw [← hw0W]; exact hw0)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
