import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq

set_option autoImplicit false

open Set MeasureTheory Filter
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique

/- English proof (translation)
Establish `h : dbarAt (fun _ : V n => (0 : Alt n)) = fun _ => 0`. Use function extensionality and compare the values at `w`. Simplify using `[dbarAt, coefwise]`. Rewrite using `[h]`. Simplify using `[delAt, coefwise]`.
-/
theorem delAt_dbarAt_zero_field {n : ℕ} (v : V n) : delAt (dbarAt (fun _ : V n => (0 : Alt n))) v = 0 := by
  have h : dbarAt (fun _ : V n => (0 : Alt n)) = fun _ => 0 := by
    funext w
    simp [dbarAt, coefwise]
  rw [h]
  simp [delAt, coefwise]

/- English proof (translation)
Introduce `M _ A φ hφ x hx`. Establish `hK : IsClosed (((↑) : ℂ → OnePoint ℂ) '' tsupport φ)` using `(hφ.isCompact.image OnePoint.continuous_coe).isClosed`. Establish `hz : ∀ t : OnePoint ℂ, t ∉ ((↑) : ℂ → OnePoint ℂ) '' tsupport φ → (t.elim 0 φ : ℝ) = 0`. Introduce `t ht`. Proceed by induction on `t using OnePoint.rec with`.

Consider the case `infty => rfl`. Consider the case `coe w => exact image_eq_zero_of_notMem_tsupport (f := φ) (x := w) fun hw => ht ⟨w, hw, rfl⟩`. Establish `hm : x.crd ∈ ((famAtlas A).e x.1.1).target` using `((famAtlas A).e x.1.1).map_source x.2`. Establish `ht : ((famAtlas A).e x.1.1).target ∈ 𝓝 x.crd` using `((famAtlas A).e x.1.1).open_target.mem_nhds hm`. Establish `hc : ContinuousAt (fun v => (((famAtlas A).e x.1.1).symm v).2) x.crd` using `continuousAt_snd.comp (((famAtlas A).e x.1.1).continuousAt_symm hm)`.

Establish `hs : ((famAtlas A).e x.1.1).symm x.crd = x.pt` using `((famAtlas A).e x.1.1).left_inv x.2`. Establish `hev : ∀ᶠ v in 𝓝 x.crd, (((famAtlas A).e x.1.1).symm v).2 ∈ (((↑) : ℂ → OnePoint ℂ) '' tsupport φ)ᶜ` using `hc.eventually (hK.isOpen_compl.mem_nhds (by beta_reduce; rw [hs]; exact hx))`. Rewrite using `[GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq (famAtlas A) _ x (fun _ => 0), delAt_dbarAt_zero_field, smul_zero]`. Use `filter_upwards [ht, hev] with v hv hv'`. Rewrite using `[HolAtlas.loc, dif_pos hv]`.

Express the relevant statement in the definitionally equal form `algebraMap ℂ _ (((((famAtlas A).e x.1.1).symm v).2.elim 0 φ : ℝ) : ℂ) = 0`. Rewrite using `[hz _ hv', Complex.ofReal_zero, map_zero]`.
-/
theorem ddc_elim_eq_zero_off_support : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (φ : ℂ → ℝ),
    HasCompactSupport φ → ∀ x : (famAtlas A).Pt, x.pt.2 ∉ ((↑) : ℂ → OnePoint ℂ) '' tsupport φ →
      (famAtlas A).ddc ((famAtlas A).fn fun y => y.2.elim 0 φ) x = 0 := by
  intro M _ A φ hφ x hx
  have hK : IsClosed (((↑) : ℂ → OnePoint ℂ) '' tsupport φ) :=
    (hφ.isCompact.image OnePoint.continuous_coe).isClosed
  have hz : ∀ t : OnePoint ℂ, t ∉ ((↑) : ℂ → OnePoint ℂ) '' tsupport φ → (t.elim 0 φ : ℝ) = 0 := by
    intro t ht
    induction t using OnePoint.rec with
    | infty => rfl
    | coe w => exact image_eq_zero_of_notMem_tsupport (f := φ) (x := w) fun hw => ht ⟨w, hw, rfl⟩
  have hm : x.crd ∈ ((famAtlas A).e x.1.1).target := ((famAtlas A).e x.1.1).map_source x.2
  have ht : ((famAtlas A).e x.1.1).target ∈ 𝓝 x.crd := ((famAtlas A).e x.1.1).open_target.mem_nhds hm
  have hc : ContinuousAt (fun v => (((famAtlas A).e x.1.1).symm v).2) x.crd :=
    continuousAt_snd.comp (((famAtlas A).e x.1.1).continuousAt_symm hm)
  have hs : ((famAtlas A).e x.1.1).symm x.crd = x.pt := ((famAtlas A).e x.1.1).left_inv x.2
  have hev : ∀ᶠ v in 𝓝 x.crd, (((famAtlas A).e x.1.1).symm v).2 ∈ (((↑) : ℂ → OnePoint ℂ) '' tsupport φ)ᶜ :=
    hc.eventually (hK.isOpen_compl.mem_nhds (by beta_reduce; rw [hs]; exact hx))
  rw [GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq (famAtlas A) _ x (fun _ => 0), delAt_dbarAt_zero_field, smul_zero]
  filter_upwards [ht, hev] with v hv hv'
  rw [HolAtlas.loc, dif_pos hv]
  change algebraMap ℂ _ (((((famAtlas A).e x.1.1).symm v).2.elim 0 φ : ℝ) : ℂ) = 0
  rw [hz _ hv', Complex.ofReal_zero, map_zero]

end GlobalTheory.BcUnique
