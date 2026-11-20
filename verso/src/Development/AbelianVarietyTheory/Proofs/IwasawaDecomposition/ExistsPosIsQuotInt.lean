import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Mem.QuotHaar

/- English proof (translation)
Introduce `D V hV ν hν`. Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Take `⟨μ₀, hμ₀, huniq⟩` from `GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV`. Use `haveI := hμ₀.1`. Take `⟨-, 𝓕₀, h𝓕₀⟩` from `GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ₀ hμ₀.1`.

Establish `e : ν = Measure.haarScalarFactor ν μ₀ • μ₀` using `Measure.isMulLeftInvariant_eq_smul ν μ₀`. Establish `cpos : 0 < Measure.haarScalarFactor ν μ₀` using `Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ₀`. Use `set c := Measure.haarScalarFactor ν μ₀`. Use `⟨c, by exact_mod_cast cpos, ?_⟩` and prove the remaining obligations. Introduce `𝓕 h𝓕 φ hφ hint`.

Use `⟨⟨(μ₀, 𝓕₀), hμ₀, h𝓕₀⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨m, F'⟩ ⟨hm, hF'⟩`. Take `rfl : m = μ₀` from `huniq m hm`. Establish `e' : m = c⁻¹ • ν` using `by rw [e, smul_smul, inv_mul_cancel₀ cpos.ne', one_smul]`. Establish `hac : m ≪ ν`.

Rewrite using `[e']`. Conclude with `Measure.smul_absolutelyContinuous`. Establish `h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m` using `h𝓕.mono hac`. Establish `hinv : ∀ (γ : GQ V) (g : GA D V), φ (γ • g) = φ g` using `fun γ g => hφ γ γ.2 g`. Establish `hint' : IntegrableOn φ 𝓕 m`.

Rewrite using `[e', IntegrableOn, Measure.restrict_smul, ENNReal.smul_def]`. Conclude with `hint.smul_measure ENNReal.coe_ne_top`. Use `⟨(h𝓕'.integrableOn_iff hF' hinv).1 hint', ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← h𝓕'.setIntegral_eq hF' hinv]`.

Use `conv_lhs => rw [e]`. Rewrite using `[Measure.restrict_smul, integral_smul_nnreal_measure]`. Simplify using `[NNReal.smul_def, Complex.real_smul]`.
-/
theorem exists_pos_isQuotInt : ∀ (D : D7) (V : HSp D), V.SigOK → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ r : ℝ, 0 < r ∧
    ∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → IntegrableOn φ 𝓕 ν →
      GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V r φ (∫ g in 𝓕, φ g ∂ν) := by
  intro D V hV ν hν
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ₀, hμ₀, huniq⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  haveI := hμ₀.1
  obtain ⟨-, 𝓕₀, h𝓕₀⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ₀ hμ₀.1
  have e : ν = Measure.haarScalarFactor ν μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul ν μ₀
  have cpos : 0 < Measure.haarScalarFactor ν μ₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ₀
  set c := Measure.haarScalarFactor ν μ₀
  refine ⟨c, by exact_mod_cast cpos, ?_⟩
  intro 𝓕 h𝓕 φ hφ hint
  refine ⟨⟨(μ₀, 𝓕₀), hμ₀, h𝓕₀⟩, ?_⟩
  rintro ⟨m, F'⟩ ⟨hm, hF'⟩
  obtain rfl : m = μ₀ := huniq m hm
  have e' : m = c⁻¹ • ν := by rw [e, smul_smul, inv_mul_cancel₀ cpos.ne', one_smul]
  have hac : m ≪ ν := by
    rw [e']
    exact Measure.smul_absolutelyContinuous
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m := h𝓕.mono hac
  have hinv : ∀ (γ : GQ V) (g : GA D V), φ (γ • g) = φ g := fun γ g => hφ γ γ.2 g
  have hint' : IntegrableOn φ 𝓕 m := by
    rw [e', IntegrableOn, Measure.restrict_smul, ENNReal.smul_def]
    exact hint.smul_measure ENNReal.coe_ne_top
  refine ⟨(h𝓕'.integrableOn_iff hF' hinv).1 hint', ?_⟩
  simp only
  rw [← h𝓕'.setIntegral_eq hF' hinv]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure]
  simp [NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Mem.QuotHaar

end
