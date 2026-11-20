import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspApproxCompact

/- English proof (translation)
Establish `hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarM …`. Introduce `φ hc hl W hW μ hμ 𝓕 h𝓕 g`. Rewrite `hl` using `[GlobalTheory.AutFunCompare.GQ_eq]`. Conclude with `GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g`. Rewrite using `[GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]`.

Introduce `W hW μ hμ 𝓕 h𝓕 g`. Take `⟨K, hK, hKc⟩` from `GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW`. Establish `hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g`. Establish `: IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) _`.

Establish `: IsTopologicalGroup (GA D V)` using `inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))`. Conclude with `continuous_subtype_val.mul continuous_const`. Establish `hC : IsCompact ((fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g) '' K)` using `hK.image hcont`. Establish `h1` using `hint (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl) W hW μ hμ 𝓕 h𝓕 g`. Establish `hfin : μ 𝓕 < ⊤`.

Break down `(integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h | h` into its components or cases. Conclude with `absurd h (by simp)`. Conclude with `h`. Establish `hM0 : 0 ≤ μ.real 𝓕` using `measureReal_nonneg`. Establish `key : ∀ δ : ℝ, 0 < δ → ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ ≤ δ * μ.real 𝓕`.

Introduce `δ hδ`. Take `⟨ψ, hψc, hψl, hψcusp, hψ⟩` from `ha _ hC δ hδ`. Establish `h0` using `(GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V ψ).1 hψcusp W hW μ hμ 𝓕 h𝓕 g`. Establish `hfi` using `hint f hf hl W hW μ hμ 𝓕 h𝓕 g`. Establish `hψi` using `hint ψ hψc hψl W hW μ hμ 𝓕 h𝓕 g`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm at h0 ⊢`. Establish `e : ∫ n in 𝓕, f ((n : GA D V) * g) ∂μ = ∫ n in 𝓕, (f ((n : GA D V) * g) - ψ ((n : GA D V) * g)) ∂μ`. Rewrite using `[integral_sub hfi hψi, h0, sub_zero]`. Rewrite using `[e]`. Use `norm_setIntegral_le_of_norm_le_const hfin fun n _ => ?_` and prove the remaining obligations.

Take `⟨γ, hγ, hk⟩` from `hKc n`. Establish `hγ' : ((γ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) ∈ GQ V`. Rewrite using `[GlobalTheory.AutFunCompare.GQ_eq]`. Conclude with `Subgroup.mem_subgroupOf.1 hγ`. Establish `ee : f ((n : GA D V) * g) - ψ ((n : GA D V) * g) = f (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) - ψ (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) …`.

Rewrite using `[Subgroup.coe_mul, mul_assoc, hl _ hγ', hψl _ hγ']`. Rewrite using `[ee]`. Conclude with `(hψ _ ⟨_, hk, rfl⟩).le`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖` using `norm_pos_iff.2 hne`.

Use `key (‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ / (μ.real 𝓕 + 1)) (div_pos hpos (by linarith))` as an intermediate fact. Rewrite `this` using `[div_mul_eq_mul_div, le_div_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem isCuspFun_of_approx (D : D7) (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g)
    (ha : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ : GA D V → ℂ, Continuous ψ ∧
      (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧ ∀ h ∈ C, ‖f h - ψ h‖ < δ) :
    IsCuspFun V f := by
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.AutFunCompare.unipRad_cocompact D.sp.cm V W hW
  have hcont : Continuous fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g := by
    have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    have : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    exact continuous_subtype_val.mul continuous_const
  have hC : IsCompact ((fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => (n : GA D V) * g) '' K) :=
    hK.image hcont
  have h1 := hint (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl) W hW μ hμ 𝓕 h𝓕 g
  have hfin : μ 𝓕 < ⊤ := by
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h | h
    · exact absurd h (by simp)
    · exact h
  have hM0 : 0 ≤ μ.real 𝓕 := measureReal_nonneg
  have key : ∀ δ : ℝ, 0 < δ → ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ ≤ δ * μ.real 𝓕 := by
    intro δ hδ
    obtain ⟨ψ, hψc, hψl, hψcusp, hψ⟩ := ha _ hC δ hδ
    have h0 := (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V ψ).1 hψcusp W hW μ hμ 𝓕 h𝓕 g
    have hfi := hint f hf hl W hW μ hμ 𝓕 h𝓕 g
    have hψi := hint ψ hψc hψl W hW μ hμ 𝓕 h𝓕 g
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm at h0 ⊢
    have e : ∫ n in 𝓕, f ((n : GA D V) * g) ∂μ = ∫ n in 𝓕, (f ((n : GA D V) * g) - ψ ((n : GA D V) * g)) ∂μ := by
      rw [integral_sub hfi hψi, h0, sub_zero]
    rw [e]
    refine norm_setIntegral_le_of_norm_le_const hfin fun n _ => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc n
    have hγ' : ((γ : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) ∈ GQ V := by
      rw [GlobalTheory.AutFunCompare.GQ_eq]
      exact Subgroup.mem_subgroupOf.1 hγ
    have ee : f ((n : GA D V) * g) - ψ ((n : GA D V) * g) =
        f (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) -
          ψ (((γ * n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W) : GA D V) * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hl _ hγ', hψl _ hγ']
    rw [ee]
    exact (hψ _ ⟨_, hk, rfl⟩).le
  by_contra hne
  have hpos : 0 < ‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ := norm_pos_iff.2 hne
  have := key (‖GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.constTerm D.sp.cm V W μ 𝓕 f g‖ / (μ.real 𝓕 + 1)) (div_pos hpos (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at this
  nlinarith

end GlobalTheory.CuspApproxCompact
