import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntegralAgainstPositive
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

namespace IntegralAgainstPositive

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `h0 : 0 ≤ ∑ᶠ x, -f x` using `finsum_nonneg fun x => neg_nonneg.2 (h x)`. Rewrite `h0` using `[finsum_neg_distrib]`. Conclude with `neg_nonneg.1 h0`.
-/
theorem finsum_nonpos_of {α : Sort*} {f : α → ℝ} (h : ∀ x, f x ≤ 0) : ∑ᶠ x, f x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -f x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

/- English proof (translation)
Introduce `f hf`. Use `set F := map (Int.castRingHom ℂ) f`. Establish `hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ)` using `by filter_upwards [hpts] with w hw`. Conclude with `hw.2 f (hP0 hf)`. Establish `hd` using `(ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y hγ.differentiableAt.hasFDerivAt`.

Establish `h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y` using `(hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero`. Use `congrArg (fun T => T ξ) (hd.unique h0)` as an intermediate fact. Simplify `this` using `[smul_eq_mul]`.
-/
theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun T => T ξ) (hd.unique h0)
  simpa [smul_eq_mul] using this

/- English proof (translation)
Establish `hA : AnalyticAt ℂ γ y` using `sheet_analyticAt osgood h`. Establish `hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P` using `h.2.mono fun _ hy' => hy'.2.1`. Establish `hy : γ y ∈ mcPts P` using `hpts.self_of_nhds`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]`. Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j => ?_` and prove the remaining obligations.

Establish `hh : ContDiffAt ℝ 2 (L j).h (γ y)` using `((hsp j).1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hlog : ContDiffAt ℝ 2 (fun z => Real.log ((L j).h z)) (γ y)` using `hh.log ((L j).pos _ hy.1).ne'`. Establish `h2 : ContDiffAt ℝ 2 (fun y' => Real.log ((L j).h (γ y'))) y` using `hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)`. Use `ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_` and prove the remaining obligations. Establish `hl` using `ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log ((L j).h z)) ξ hA hlog`.

Express the relevant statement in the definitionally equal form `0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log ((L j).h z)) ∘ γ) y ξ`. Rewrite using `[hl]`. Conclude with `(hsp j).2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)`.
-/
theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {L : Fin e → HermLine ι} (hsp : ∀ j, IsSemipositiveRel P0 P (L j))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun j y' => Real.log ((L j).h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j => ?_
  have hh : ContDiffAt ℝ 2 (L j).h (γ y) :=
    ((hsp j).1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log ((L j).h z)) (γ y) :=
    hh.log ((L j).pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log ((L j).h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log ((L j).h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log ((L j).h z)) ∘ γ) y ξ
  rw [hl]
  exact (hsp j).2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

/- English proof (translation)
Introduce `K _ ι _ P P0 e L g hP0 hsp hg`. Unfold `ptsIntegral`. Use `split_ifs with hΨ`. Unfold `ptsIntegralAt`. Use `integral_nonpos fun y => ?_` and prove the remaining obligations.

Establish `key : ∀ w, sheetDensity P hΨ.choose (pot L) g y w ≤ 0`. Introduce `w`. Unfold `sheetDensity`. Use `split_ifs with hγ`. Establish `hsh` using `hγ.choose_spec`.

Establish `hz : hγ.choose y ∈ mcPts P` using `hsh.2.self_of_nhds.2.1`. Conclude with `mul_nonpos_of_nonpos_of_nonneg (hg _ hz) (maDensity_nonneg_of_sheet hP0 hsp hsh)`. Conclude with `le_rfl`. Conclude with `finsum_nonpos_of fun w => finsum_nonpos_of fun _ => key w`. Conclude with `le_rfl`.
-/
theorem proof : IntegralAgainstPositive.Statement := by
  intro K _ ι _ P P0 e L g hP0 hsp hg
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (pot L) g y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        exact mul_nonpos_of_nonpos_of_nonneg (hg _ hz) (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos_of fun w => finsum_nonpos_of fun _ => key w
  · exact le_rfl

end IntegralAgainstPositive

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
