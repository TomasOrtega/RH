import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNhdsOneUnitaryGroupRationalPointEqOneStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

/- English proof (translation)
Take `⟨U, hU, h⟩` from `h`. Use `discreteTopology_of_isOpen_singleton_one ?_` and prove the remaining obligations. Take `⟨V, hVU, hV, h1⟩` from `mem_nhds_iff.1 hU`. Establish `e : ({1} : Set Γ) = Subtype.val ⁻¹' V`. Use extensionality with `γ`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `h1`. Introduce `hγ`. Conclude with `Subtype.ext (h _ (hVU hγ) ⟨γ, by simp [Subgroup.smul_def]⟩)`.

Rewrite using `[e]`. Conclude with `hV.preimage continuous_subtype_val`.
-/
theorem discreteTopology_subgroup_of_nhds_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) (h : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, (∃ γ : Γ, γ • (1 : G) = g) → g = 1) :
    DiscreteTopology Γ := by
  obtain ⟨U, hU, h⟩ := h
  refine discreteTopology_of_isOpen_singleton_one ?_
  obtain ⟨V, hVU, hV, h1⟩ := mem_nhds_iff.1 hU
  have e : ({1} : Set Γ) = Subtype.val ⁻¹' V := by
    ext γ
    constructor
    · rintro rfl
      exact h1
    · intro hγ
      exact Subtype.ext (h _ (hVU hγ) ⟨γ, by simp [Subgroup.smul_def]⟩)
  rw [e]
  exact hV.preimage continuous_subtype_val

/- English proof (translation)
Use `GlobalTheory.countable_of_discrete_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ` as an intermediate fact. Take `⟨D, -, -, hD⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup Γ`. Conclude with `⟨⟨D, hD μ⟩, fun 𝓕 𝓕' h h' => ⟨h.measure_eq h', h.measure_ne_zero (NeZero.ne μ)⟩⟩`.
-/
theorem fundamentalDomain_exists_measure_eq_of_discrete {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] :
    (∃ 𝓕, IsFundamentalDomain Γ 𝓕 μ) ∧
      ∀ 𝓕 𝓕', IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  exact ⟨⟨D, hD μ⟩, fun 𝓕 𝓕' h h' => ⟨h.measure_eq h', h.measure_ne_zero (NeZero.ne μ)⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J μ hμ`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J` as an intermediate fact. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J` as an intermediate fact. Use `(GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1` as an intermediate fact. Set `Γ : Subgroup (HA (AF F) σ J)` to `HFinIn (AF F) σ J`.

Establish `: DiscreteTopology Γ` using `discreteTopology_subgroup_of_nhds_one Γ (GlobalTheory.T.exists_nhds_one_unitaryGroup_rationalPoint_eq_one F E σ M J)`. Conclude with `fundamentalDomain_exists_measure_eq_of_discrete Γ μ`.
-/
theorem fundamentalDomain_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ M J μ hμ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : DiscreteTopology Γ := discreteTopology_subgroup_of_nhds_one Γ (GlobalTheory.T.exists_nhds_one_unitaryGroup_rationalPoint_eq_one F E σ M J)
  exact fundamentalDomain_exists_measure_eq_of_discrete Γ μ

end GlobalTheory.Mem.Vol
