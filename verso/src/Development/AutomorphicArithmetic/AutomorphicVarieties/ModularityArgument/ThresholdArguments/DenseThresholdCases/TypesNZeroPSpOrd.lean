import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroSDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spOrd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end UpperTheory.TNZ.Grp.P_spOrd
namespace UpperTheory.TNZ.Grp
open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
/- English proof (translation)
Introduce `hL V _ _ π hs hi c hc σ h`. Take `⟨Z, Ψ, -, hΨ, -⟩` from `hL.loc.zel k`. Take `⟨hp1, e1⟩` from `multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n) (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i))) (fun i => hasFiniteLength_detRep1 (c (σ i)))`. Take `⟨hp2, e2⟩` from `multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n) (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i)) (fun i => hasFiniteLength_detRep1 (c i))`. Establish `hcl : clsGL _ hp1 = clsGL _ hp2`.

Apply `Ψ.injective` to reduce the goal to its premises. Rewrite using `[e1, e2]`. Conclude with `Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))`. Establish `h1` using `h.trans (prin_sub_multi (fun i => c (σ i)))`. Establish `h2` using `clsGL_of_pos hp1 hs hi h1`.

Rewrite `h2` using `[hcl]`. Conclude with `(isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)`.
-/
theorem step_spOrd_alt : _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)
end UpperTheory.TNZ.Grp
end
end
