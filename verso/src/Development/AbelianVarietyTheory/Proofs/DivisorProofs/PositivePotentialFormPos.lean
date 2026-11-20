import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Use `set x := ψ.symm z with hxdef`. Take `⟨j, hj⟩` from `A.cover x`. Use `set c := A.chart j with hc`. Use `set τ : (Fin e → ℂ) → (Fin e → ℂ) := c ∘ ψ.symm with hτdef`. Establish `hxψ : x ∈ ψ.source` using `ψ.map_target hz`.

Establish `hτa : AnalyticAt ℂ τ z` using `(hψ j).2 z ⟨hz, hj⟩`. Establish `hnear : ∀ᶠ y in 𝓝 z, y ∈ ψ.target ∧ ψ.symm y ∈ c.source`. Establish `h1 : ψ.target ∈ 𝓝 z` using `ψ.open_target.mem_nhds hz`. Establish `h2 : ψ.symm ⁻¹' c.source ∈ 𝓝 z` using `(ψ.continuousAt_symm hz).preimage_mem_nhds (c.open_source.mem_nhds hj)`. Use `filter_upwards [h1, h2] with y hy1 hy2`.

Conclude with `⟨hy1, hy2⟩`. Establish `hgerm : (P.φ x ∘ ψ.symm) =ᶠ[𝓝 z] ((P.φ x ∘ c.symm) ∘ τ)` using `by filter_upwards [hnear] with y hy`. Simplify using `[hτdef, c.left_inv hy.2]`. Establish `hτz : τ z = c x` using `rfl`. Establish `hτt : τ z ∈ c.target` using `c.map_source hj`.

Establish `hsymm : c.symm (τ z) = x` using `c.left_inv hj`. Establish `hS : IsOpen (c.target ∩ c.symm ⁻¹' P.U x)` using `c.isOpen_inter_preimage_symm (P.isOpen_U x)`. Establish `hmemS : τ z ∈ c.target ∩ c.symm ⁻¹' P.U x` using `⟨hτt, by simp [hsymm, P.mem_U x]⟩`. Establish `hsm : ContDiffAt ℝ 2 (P.φ x ∘ c.symm) (τ z)` using `(((hP.1 x j).contDiffAt (hS.mem_nhds hmemS))).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hlevi : levi (P.φ x ∘ ψ.symm) z w = levi (P.φ x ∘ c.symm) (τ z) (fderiv ℂ τ z w)`.

Rewrite using `[levi_congr hgerm w]`. Conclude with `levi_comp w hτa hsm`. Use `set σ : (Fin e → ℂ) → (Fin e → ℂ) := ψ ∘ c.symm with hσdef`. Establish `hσa : AnalyticAt ℂ σ (τ z)` using `(hψ j).1 (τ z) ⟨hτt, show c.symm (τ z) ∈ ψ.source by rw [hsymm]; exact hxψ⟩`. Establish `hid : (σ ∘ τ) =ᶠ[𝓝 z] id` using `by filter_upwards [hnear] with y hy`.

Simplify using `[hσdef, hτdef, c.left_inv hy.2, ψ.right_inv hy.1]`. Establish `hD : (fderiv ℂ σ (τ z)).comp (fderiv ℂ τ z) = ContinuousLinearMap.id ℂ _`. Rewrite using `[← fderiv_comp z hσa.differentiableAt hτa.differentiableAt, hid.fderiv_eq, fderiv_id]`. Establish `hne : fderiv ℂ τ z w ≠ 0`. Introduce `h0`.

Apply `hw` to reduce the goal to its premises. Use `congrArg (fun L => L w) hD` as an intermediate fact. Simplify `this.symm` using `[h0]`. Establish `hlp : 0 < levi (P.φ x ∘ c.symm) (τ z) (fderiv ℂ τ z w)` using `hpos x j (τ z) hmemS _ hne`. Unfold `formAt`.

Rewrite using `[← hxdef, hlevi]`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem formAt_pos_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hP : IsPotential A P)
    (hpos : IsPosPot A P) (hψ : IsCompatChart A ψ) (z : Fin e → ℂ) (hz : z ∈ ψ.target)
    (w : Fin e → ℂ) (hw : w ≠ 0) : 0 < formAt ψ P z w := by
  set x := ψ.symm z with hxdef
  obtain ⟨j, hj⟩ := A.cover x
  set c := A.chart j with hc
  set τ : (Fin e → ℂ) → (Fin e → ℂ) := c ∘ ψ.symm with hτdef
  have hxψ : x ∈ ψ.source := ψ.map_target hz
  have hτa : AnalyticAt ℂ τ z := (hψ j).2 z ⟨hz, hj⟩

  have hnear : ∀ᶠ y in 𝓝 z, y ∈ ψ.target ∧ ψ.symm y ∈ c.source := by
    have h1 : ψ.target ∈ 𝓝 z := ψ.open_target.mem_nhds hz
    have h2 : ψ.symm ⁻¹' c.source ∈ 𝓝 z :=
      (ψ.continuousAt_symm hz).preimage_mem_nhds (c.open_source.mem_nhds hj)
    filter_upwards [h1, h2] with y hy1 hy2
    exact ⟨hy1, hy2⟩
  have hgerm : (P.φ x ∘ ψ.symm) =ᶠ[𝓝 z] ((P.φ x ∘ c.symm) ∘ τ) := by
    filter_upwards [hnear] with y hy
    simp [hτdef, c.left_inv hy.2]
  have hτz : τ z = c x := rfl
  have hτt : τ z ∈ c.target := c.map_source hj
  have hsymm : c.symm (τ z) = x := c.left_inv hj
  have hS : IsOpen (c.target ∩ c.symm ⁻¹' P.U x) := c.isOpen_inter_preimage_symm (P.isOpen_U x)
  have hmemS : τ z ∈ c.target ∩ c.symm ⁻¹' P.U x := ⟨hτt, by simp [hsymm, P.mem_U x]⟩
  have hsm : ContDiffAt ℝ 2 (P.φ x ∘ c.symm) (τ z) :=
    (((hP.1 x j).contDiffAt (hS.mem_nhds hmemS))).of_le (WithTop.coe_le_coe.2 le_top)
  have hlevi : levi (P.φ x ∘ ψ.symm) z w = levi (P.φ x ∘ c.symm) (τ z) (fderiv ℂ τ z w) := by
    rw [levi_congr hgerm w]
    exact levi_comp w hτa hsm

  set σ : (Fin e → ℂ) → (Fin e → ℂ) := ψ ∘ c.symm with hσdef
  have hσa : AnalyticAt ℂ σ (τ z) := (hψ j).1 (τ z) ⟨hτt, show c.symm (τ z) ∈ ψ.source by rw [hsymm]; exact hxψ⟩
  have hid : (σ ∘ τ) =ᶠ[𝓝 z] id := by
    filter_upwards [hnear] with y hy
    simp [hσdef, hτdef, c.left_inv hy.2, ψ.right_inv hy.1]
  have hD : (fderiv ℂ σ (τ z)).comp (fderiv ℂ τ z) = ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp z hσa.differentiableAt hτa.differentiableAt, hid.fderiv_eq, fderiv_id]
  have hne : fderiv ℂ τ z w ≠ 0 := by
    intro h0
    apply hw
    have := congrArg (fun L => L w) hD
    simpa [h0] using this.symm
  have hlp : 0 < levi (P.φ x ∘ c.symm) (τ z) (fderiv ℂ τ z w) :=
    hpos x j (τ z) hmemS _ hne
  unfold formAt
  rw [← hxdef, hlevi]
  have := Real.pi_pos
  positivity

end GlobalTheory
