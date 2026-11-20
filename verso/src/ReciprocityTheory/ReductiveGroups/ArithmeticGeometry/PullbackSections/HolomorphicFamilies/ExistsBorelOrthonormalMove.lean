import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

/- English proof (translation)
Unfold `dmin`. Rewrite using `[hx τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal]`. Simplify using `[psgn, Finset.prod_range]`.
-/
theorem diagonal_minor_orthonormal {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin
  rw [hx τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal]
  simp [psgn, Finset.prod_range]

/- English proof (translation)
Rewrite using `[diagonal_minor_orthonormal X hx, Complex.norm_real, Real.norm_eq_abs]`. Unfold `psgn`. Rewrite using `[Finset.abs_prod]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`.

Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_diagonal_minor_one {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  rw [diagonal_minor_orthonormal X hx, Complex.norm_real, Real.norm_eq_abs]
  unfold psgn
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro a _
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Use `⟨ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, fun τ => ⟨?_, fun i => ?_⟩, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx⟩` and prove the remaining obligations. Use `show (mat x τ * mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hx τ).1 ((ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx) τ).1`. Rewrite using `[diagonal_minor_orthonormal X (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx) τ i, Complex.ofReal_re]`.

Establish `h : psgn X.p0 i ≠ 0`. Unfold `psgn`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `a _`. Unfold `sgn`.

Apply the tactic sequence `split_ifs <;> norm_num`. Conclude with `mul_self_pos.2 h`.
-/
theorem exists_borel_orthonormal_move {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ X.IsOrtho (rmul x b) := by
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, fun τ => ⟨?_, fun i => ?_⟩,
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx⟩
  · show (mat x τ * mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 ((ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx) τ).1
  · rw [diagonal_minor_orthonormal X (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx) τ i, Complex.ofReal_re]
    have h : psgn X.p0 i ≠ 0 := by
      unfold psgn
      rw [Finset.prod_ne_zero_iff]
      intro a _
      unfold sgn
      split_ifs <;> norm_num
    exact mul_self_pos.2 h

end Frames

section Act

variable {dim : (E →+* ℂ) → ℕ}

end Act

end ReciprocityTheory.ChartRestriction.G.PullbackSections
