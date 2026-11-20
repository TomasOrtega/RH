import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailRest

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OpEx

open PositivityTheory.Rg.BcB.E1

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yxa1.main s g`.
-/
theorem coeFn_sum_ae {α : Type} [MeasurableSpace α] {ν : Measure α} {ι : Type} (s : Finset ι)
    (g : ι → Lp ℂ 2 ν) :
    ((∑ j ∈ s, g j : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∑ j ∈ s, (g j : α → ℂ) x :=
  _root_.UpperTheory.Reformulated.B.Yxa1.main s g

/- English proof (translation)
Introduce `hK hR hS X ι _ Φ hΦ`. Use `haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance`. Establish `hex : ∀ i j, ∃ T : Lp ℂ 2 X.ν →L[ℂ] Lp ℂ 2 X.ν, ∀ f, (T f : X.G → ℂ) =ᵐ[X.ν] fun x => ∫ y, ker X.Γ (Φ i j) x y * (f : X.G → ℂ) y ∂X.ν`. Introduce `i j`. Take `⟨A, hA, h1, h2⟩` from `hR X (Φ i j) (hΦ i j)`.

Establish `hc` using `(hK X (Φ i j) (hΦ i j)).2.1`. Conclude with `hS X.G X.ν (ker X.Γ (Φ i j)) A hc.measurable hA h1 h2`. Use `choose S hSop using hex`. Set `T : X.Hs ι →L[ℂ] X.Hs ι` to `((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 X.ν)).symm : (ι → Lp ℂ 2 X.ν) →L[ℂ] X.Hs ι) ∘L ContinuousLinearMap.pi fun i => ∑ j, (S i j).comp (PiLp.proj 2 (fun _ : ι => Lp ℂ 2 X.ν) j)`. Establish `hT : ∀ f i, T f i = ∑ j, S i j (f j)`.

Introduce `f i`. Simplify using `[T, ContinuousLinearMap.sum_apply]`. Establish `hIs : X.IsOp Φ T`. Introduce `f i`. Rewrite using `[hT]`.

Establish `hall : ∀ᵐ x ∂X.ν, ∀ j, (S i j (f j) : X.G → ℂ) x = ∫ y, ker X.Γ (Φ i j) x y * (f j : X.G → ℂ) y ∂X.ν` using `ae_all_iff.2 fun j => hSop i j (f j)`. Use `filter_upwards [coeFn_sum_ae Finset.univ (fun j => S i j (f j)), hall] with x h1 h2`. Rewrite using `[h1]`. Conclude with `Finset.sum_congr rfl fun j _ => h2 j`. Use `⟨T, hIs, ?_⟩` and prove the remaining obligations.

Introduce `T' hT'`. Use extensionality with `f : 1`. Use `PiLp.ext fun i => Lp.ext ?_` and prove the remaining obligations. Conclude with `(hT' f i).trans (hIs f i).symm`.
-/
theorem opExA : KerBasic → RowInt → SchurOp → OpExA := by
  intro hK hR hS X ι _ Φ hΦ
  classical
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hex : ∀ i j, ∃ T : Lp ℂ 2 X.ν →L[ℂ] Lp ℂ 2 X.ν, ∀ f, (T f : X.G → ℂ) =ᵐ[X.ν]
      fun x => ∫ y, ker X.Γ (Φ i j) x y * (f : X.G → ℂ) y ∂X.ν := by
    intro i j
    obtain ⟨A, hA, h1, h2⟩ := hR X (Φ i j) (hΦ i j)
    have hc := (hK X (Φ i j) (hΦ i j)).2.1
    exact hS X.G X.ν (ker X.Γ (Φ i j)) A hc.measurable hA h1 h2
  choose S hSop using hex
  let T : X.Hs ι →L[ℂ] X.Hs ι :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 X.ν)).symm :
        (ι → Lp ℂ 2 X.ν) →L[ℂ] X.Hs ι) ∘L
      ContinuousLinearMap.pi fun i => ∑ j, (S i j).comp (PiLp.proj 2 (fun _ : ι => Lp ℂ 2 X.ν) j)
  have hT : ∀ f i, T f i = ∑ j, S i j (f j) := by
    intro f i
    simp [T, ContinuousLinearMap.sum_apply]
  have hIs : X.IsOp Φ T := by
    intro f i
    rw [hT]
    have hall : ∀ᵐ x ∂X.ν, ∀ j, (S i j (f j) : X.G → ℂ) x =
        ∫ y, ker X.Γ (Φ i j) x y * (f j : X.G → ℂ) y ∂X.ν :=
      ae_all_iff.2 fun j => hSop i j (f j)
    filter_upwards [coeFn_sum_ae Finset.univ (fun j => S i j (f j)), hall] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  refine ⟨T, hIs, ?_⟩
  intro T' hT'
  ext f : 1
  refine PiLp.ext fun i => Lp.ext ?_
  exact (hT' f i).trans (hIs f i).symm

end GlobalTheory.CompanionTheory.OpEx
