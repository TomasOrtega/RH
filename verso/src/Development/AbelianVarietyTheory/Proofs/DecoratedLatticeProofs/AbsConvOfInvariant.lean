import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.BesInt

/- English proof (translation)
Introduce `D σ B f hf hinv h`. Take `⟨_, _, _, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A`. Take `⟨_, _, _, _, _, -, _⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V`. Take `⟨hemb, -, hconj, -, hrat⟩` from `GlobalTheory.Unf.besSemi D σ B`. Take `⟨KA, hKA, hcovA⟩` from `B.cpt`.

Take `⟨⟨KN, hKN, hcovN⟩, -⟩` from `GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V σ B.d.e (isIsoSub_e B.d)`. Set `Φ : NFlag B.V B.d.e × GA D B.A → GA D B.V` to `fun p => p.1.1 * embA B.d B.o p.2 * h`. Establish `hΦ : Continuous Φ` using `((continuous_subtype_val.comp continuous_fst).mul (hemb.comp continuous_snd)).mul continuous_const`. Establish `hΩ : IsCompact (Φ '' (KN ×ˢ KA))` using `(hKN.prod hKA).image hΦ`. Take `⟨C, hC⟩` from `hΩ.exists_bound_of_continuousOn hf.continuousOn`.

Establish `hbd : ∀ (h₁ : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h₁ * h)‖ ≤ C`. Introduce `h₁ n`. Take `⟨γ, hγ, hγK⟩` from `hcovA h₁`. Take `⟨δ, hδ, k, hk, hnk⟩` from `hcovN ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hconj n.1 n.2 γ⟩`. Establish `heq : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = δ.1 * k.1` using `congrArg Subtype.val hnk`.

Establish `hγV : embA B.d B.o γ ∈ GQ B.V`. Use `(hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩` as an intermediate fact. Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Establish `hδQ : (δ.1 : GA D B.V) ∈ GQ B.V` using `Subgroup.mem_subgroupOf.1 hδ`. Establish `hηQ : (embA B.d B.o γ)⁻¹ * δ.1 ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V))` using `Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hγV) hδQ, mul_mem (inv_mem (Subgroup.mem_sup_right ⟨γ, rfl⟩)) (Subgroup.mem_sup_left δ.2)⟩`.

Establish `e1 : n.1 = (embA B.d B.o γ)⁻¹ * (δ.1 * k.1) * embA B.d B.o γ` using `by rw [← heq]; group`. Establish `e2 : n.1 * embA B.d B.o h₁ * h = ((embA B.d B.o γ)⁻¹ * δ.1) * (k.1 * embA B.d B.o (γ * h₁) * h)`. Rewrite using `[e1, map_mul]`. Use `group`. Rewrite using `[e2, hinv _ hηQ]`.

Conclude with `hC _ ⟨(k, γ * h₁), ⟨hk, hγK⟩, rfl⟩`. Establish `hfinA : B.vA.μ B.vA.𝓕 < ⊤`. Establish `hcov' : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ c ∈ KA, g = γ * c` using `fun g => by`. Take `⟨γ, hγ, hc⟩` from `hcovA g`. Conclude with `⟨γ⁻¹, inv_mem hγ, γ * g, hc, by rw [inv_mul_cancel_left]⟩`.

Establish `h1` using `GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain B.A B.vA.μ B.vA.𝓕 KA B.vA.haar B.vA.fund hKA hcov' (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl`. Simplify using `using (integrableOn_const_iff (C := (1 : ℂ))).1 h1`. Establish `hfinN : B.vN.ν B.vN.𝓝 < ⊤` using `by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top`. Use `haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfinA.ne`. Use `haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hfinN.ne`.

Establish `hK : Continuous (Function.uncurry fun (h₁ : GA D B.A) (n : flagN B.d) => f (n.1 * embA B.d B.o h₁ * h))` using `hf.comp (((continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)).mul continuous_const)`. Conclude with `Integrable.of_bound hK.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hbd p.1 p.2)`.
-/
theorem absConv_of_invariant : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∀ f : GA D B.V → ℂ, Continuous f →
    (∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, f (γ * h) = f h) →
    ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h₁ n => f (n.1 * embA B.d B.o h₁ * h) := by
  intro D σ B f hf hinv h
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨hemb, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  obtain ⟨KA, hKA, hcovA⟩ := B.cpt
  obtain ⟨⟨KN, hKN, hcovN⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V σ B.d.e (isIsoSub_e B.d)

  let Φ : NFlag B.V B.d.e × GA D B.A → GA D B.V := fun p => p.1.1 * embA B.d B.o p.2 * h
  have hΦ : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_fst).mul (hemb.comp continuous_snd)).mul continuous_const
  have hΩ : IsCompact (Φ '' (KN ×ˢ KA)) := (hKN.prod hKA).image hΦ
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn

  have hbd : ∀ (h₁ : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h₁ * h)‖ ≤ C := by
    intro h₁ n
    obtain ⟨γ, hγ, hγK⟩ := hcovA h₁
    obtain ⟨δ, hδ, k, hk, hnk⟩ :=
      hcovN ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hconj n.1 n.2 γ⟩
    have heq : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = δ.1 * k.1 := congrArg Subtype.val hnk
    have hγV : embA B.d B.o γ ∈ GQ B.V := by
      have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
      rwa [one_mul] at this
    have hδQ : (δ.1 : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hδ
    have hηQ : (embA B.d B.o γ)⁻¹ * δ.1 ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hγV) hδQ,
        mul_mem (inv_mem (Subgroup.mem_sup_right ⟨γ, rfl⟩)) (Subgroup.mem_sup_left δ.2)⟩
    have e1 : n.1 = (embA B.d B.o γ)⁻¹ * (δ.1 * k.1) * embA B.d B.o γ := by rw [← heq]; group
    have e2 : n.1 * embA B.d B.o h₁ * h =
        ((embA B.d B.o γ)⁻¹ * δ.1) * (k.1 * embA B.d B.o (γ * h₁) * h) := by
      rw [e1, map_mul]; group
    rw [e2, hinv _ hηQ]
    exact hC _ ⟨(k, γ * h₁), ⟨hk, hγK⟩, rfl⟩

  have hfinA : B.vA.μ B.vA.𝓕 < ⊤ := by
    have hcov' : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ c ∈ KA, g = γ * c := fun g => by
      obtain ⟨γ, hγ, hc⟩ := hcovA g
      exact ⟨γ⁻¹, inv_mem hγ, γ * g, hc, by rw [inv_mul_cancel_left]⟩
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain B.A B.vA.μ B.vA.𝓕 KA B.vA.haar B.vA.fund hKA
      hcov' (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hfinN : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfinA.ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hfinN.ne
  have hK : Continuous (Function.uncurry fun (h₁ : GA D B.A) (n : flagN B.d) => f (n.1 * embA B.d B.o h₁ * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)).mul continuous_const)
  exact Integrable.of_bound hK.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hbd p.1 p.2)

end GlobalTheory.Unf.BesInt

end
