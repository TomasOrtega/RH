import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ComapIrreducible
import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `K _ _ n μ _ V hV`. Take `⟨hcs, hI, hirr⟩` from `sumT K n μ V hV`. Establish `hc : IsClosed ((V.comap (toLp μ).toLinearMap : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ))` using `hV.closed.preimage (toLp μ).continuous`. Establish `e : formsIn μ V = summandCuspForms (V.comap (toLp μ).toLinearMap)`. Rewrite using `[formsIn, clsL, Submodule.comap_comp, summandCuspForms]`.

Establish `hne` using `summandCuspForms_ne_bot μ _ hI hirr`. Establish `hcl` using `topologicalClosure_map_summandCuspForms hc hI hirr hne`. Establish `h1` using `summandCuspForms_stable_ρ hc hI`. Establish `h2` using `summandCuspForms_stable_σ hI`. Establish `h3` using `summandCuspForms_stable_τ hI`.

Establish `h4` using `fun W hW a b c d => eq_summandCuspForms (W := W) hc hI hirr hW a b c d`. Rewrite `hne`, `hcl`, `h1`, `h2`, `h3`, `h4` using `[← e]`. Use `⟨⟨h1, h2, h3⟩, hne, fun W hW hs => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(em (W = ⊥)).imp_right fun h0 => h4 W hW hs.ρ hs.σ hs.τ h0`. Use `le_antisymm (Submodule.topologicalClosure_minimal _ ?_ hV.closed) fun v hv => ?_` and prove the remaining obligations.

Conclude with `Submodule.map_le_iff_le_comap.2 inf_le_right`. Take `⟨u, rfl⟩ : ∃ u : CuspL2 μ, toLp μ u = v` from `⟨(⟨v, hV.le hv⟩ : cuspidalL2 μ), rfl⟩`. Establish `hu : u ∈ closure (((formsIn μ V).map (cuspVecL μ) : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ))`. Rewrite using `[← Submodule.topologicalClosure_coe, hcl]`. Conclude with `hv`.

Rewrite using `[← SetLike.mem_coe, Submodule.topologicalClosure_coe]`. Use `map_mem_closure (toLp μ).continuous hu fun x hx => ?_` and prove the remaining obligations. Take `⟨φ, hφ, rfl⟩` from `Submodule.mem_map.1 hx`. Conclude with `Submodule.mem_map_of_mem (f := clsL μ) hφ`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.formsIrr :
    UpperTheory.ConvolutionTheory.Dp.FormsIrr := by
  intro K _ _ n μ _ V hV
  obtain ⟨hcs, hI, hirr⟩ := sumT K n μ V hV
  have hc : IsClosed ((V.comap (toLp μ).toLinearMap : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) :=
    hV.closed.preimage (toLp μ).continuous
  have e : formsIn μ V = summandCuspForms (V.comap (toLp μ).toLinearMap) := by
    rw [formsIn, clsL, Submodule.comap_comp, summandCuspForms]
  have hne := summandCuspForms_ne_bot μ _ hI hirr
  have hcl := topologicalClosure_map_summandCuspForms hc hI hirr hne
  have h1 := summandCuspForms_stable_ρ hc hI
  have h2 := summandCuspForms_stable_σ hI
  have h3 := summandCuspForms_stable_τ hI
  have h4 := fun W hW a b c d => eq_summandCuspForms (W := W) hc hI hirr hW a b c d
  rw [← e] at hne hcl h1 h2 h3 h4
  refine ⟨⟨h1, h2, h3⟩, hne, fun W hW hs => ?_, ?_⟩
  · exact (em (W = ⊥)).imp_right fun h0 => h4 W hW hs.ρ hs.σ hs.τ h0
  · refine le_antisymm (Submodule.topologicalClosure_minimal _ ?_ hV.closed) fun v hv => ?_
    · exact Submodule.map_le_iff_le_comap.2 inf_le_right
    · obtain ⟨u, rfl⟩ : ∃ u : CuspL2 μ, toLp μ u = v := ⟨(⟨v, hV.le hv⟩ : cuspidalL2 μ), rfl⟩
      have hu : u ∈ closure (((formsIn μ V).map (cuspVecL μ) : Submodule ℂ (CuspL2 μ)) : Set (CuspL2 μ)) := by
        rw [← Submodule.topologicalClosure_coe, hcl]
        exact hv
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      refine map_mem_closure (toLp μ).continuous hu fun x hx => ?_
      obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hx
      exact Submodule.mem_map_of_mem (f := clsL μ) hφ
