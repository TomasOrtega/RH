import Mathlib
import GroundTheory.AutomorphicForms.Reduction

open MeasureTheory Set

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

/- English proof (translation)
Use `IsFundamentalDomain.mk' ((measurableSet_fundamentalDomain Γ).preimage (measurable_mul_const g)).nullMeasurableSet fun x => ?_` and prove the remaining obligations. Take `⟨γ, hγ, huniq⟩` from `existsUnique_smul_mem_fundamentalDomain Γ (x * g)`. Use `⟨γ, ?_, fun δ hδ => huniq δ ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `γ • x * g ∈ fundamentalDomain Γ`. Rewrite using `[Subgroup.smul_def, smul_eq_mul, mul_assoc]` and apply the resulting hypothesis.

Express the relevant statement in the definitionally equal form `δ • x * g ∈ fundamentalDomain Γ at hδ`. Rewrite `hδ` using `[Subgroup.smul_def, smul_eq_mul, mul_assoc]`. Then use the resulting hypothesis.
-/
theorem isFundamentalDomain_preimage_mulRight (μ : Measure G) (g : G) :
    IsFundamentalDomain Γ ((· * g) ⁻¹' fundamentalDomain Γ) μ := by
  refine IsFundamentalDomain.mk'
    ((measurableSet_fundamentalDomain Γ).preimage (measurable_mul_const g)).nullMeasurableSet
    fun x => ?_
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_smul_mem_fundamentalDomain Γ (x * g)
  refine ⟨γ, ?_, fun δ hδ => huniq δ ?_⟩
  · change γ • x * g ∈ fundamentalDomain Γ
    rwa [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  · change δ • x * g ∈ fundamentalDomain Γ at hδ
    rwa [Subgroup.smul_def, smul_eq_mul, mul_assoc] at hδ

/- English proof (translation)
Establish `hq : quotientMeasure Γ μ univ = μ (fundamentalDomain Γ)`. Rewrite using `[quotientMeasure, Measure.map_apply (measurable_mk Γ) MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]`. Rewrite using `[← hq]`. Use `⟨?_, measure_lt_top _ _⟩` and prove the remaining obligations. Take `⟨x⟩ : Nonempty (RightCosetSpace Γ)` from `⟨mk Γ 1⟩`.

Conclude with `(isOpen_univ.measure_pos (quotientMeasure Γ μ) ⟨x, mem_univ x⟩)`.
-/
theorem measure_fundamentalDomain_pos_lt_top (μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasure (quotientMeasure Γ μ)] :
    0 < μ (fundamentalDomain Γ) ∧ μ (fundamentalDomain Γ) < ⊤ := by
  have hq : quotientMeasure Γ μ univ = μ (fundamentalDomain Γ) := by
    rw [quotientMeasure, Measure.map_apply (measurable_mk Γ) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
  rw [← hq]
  refine ⟨?_, measure_lt_top _ _⟩
  obtain ⟨x⟩ : Nonempty (RightCosetSpace Γ) := ⟨mk Γ 1⟩
  exact (isOpen_univ.measure_pos (quotientMeasure Γ μ) ⟨x, mem_univ x⟩)

/- English proof (translation)
Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `hmap : Measure.map (· * g) μ = Measure.modularCharacterFun g • μ` using `Measure.map_right_mul_eq_modularCharacterFun_smul μ g`. Take `⟨hpos, hfin⟩` from `measure_fundamentalDomain_pos_lt_top Γ μ`. Establish `hF` using `isFundamentalDomain_fundamentalDomain Γ μ`. Establish `hF'` using `isFundamentalDomain_preimage_mulRight Γ μ g`.

Establish `heq : Measure.map (· * g) μ (fundamentalDomain Γ) = μ (fundamentalDomain Γ)`. Rewrite using `[Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain Γ)]`. Conclude with `hF'.measure_eq hF`. Rewrite `heq` using `[hmap, Measure.smul_apply]`. Establish `hc : (Measure.modularCharacterFun g : ENNReal) = 1`.

Establish `h1 : (Measure.modularCharacterFun g : ENNReal) * μ (fundamentalDomain Γ) = 1 * μ (fundamentalDomain Γ)`. Rewrite using `[one_mul]`. Simplify `heq` using `[ENNReal.smul_def]`. Conclude with `(ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h1`. Rewrite using `[hmap]`.

Establish `: Measure.modularCharacterFun g = 1` using `by exact_mod_cast hc`. Rewrite using `[this, one_smul]`.
-/
theorem isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasure (quotientMeasure Γ μ)] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hmap : Measure.map (· * g) μ = Measure.modularCharacterFun g • μ :=
    Measure.map_right_mul_eq_modularCharacterFun_smul μ g
  obtain ⟨hpos, hfin⟩ := measure_fundamentalDomain_pos_lt_top Γ μ
  have hF := isFundamentalDomain_fundamentalDomain Γ μ
  have hF' := isFundamentalDomain_preimage_mulRight Γ μ g
  have heq : Measure.map (· * g) μ (fundamentalDomain Γ) = μ (fundamentalDomain Γ) := by
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain Γ)]
    exact hF'.measure_eq hF
  rw [hmap, Measure.smul_apply] at heq
  have hc : (Measure.modularCharacterFun g : ENNReal) = 1 := by
    have h1 : (Measure.modularCharacterFun g : ENNReal) * μ (fundamentalDomain Γ) =
        1 * μ (fundamentalDomain Γ) := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using heq
    exact (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 h1
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]

end RightCosetSpace

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Conclude with `RightCosetSpace.isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (rationalGLOne K n) μ`.
-/
theorem isMulRightInvariant_normOneGL (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  exact RightCosetSpace.isMulRightInvariant_of_isFiniteMeasure_quotientMeasure (rationalGLOne K n) μ

end Reduction

end

end GroundTheory.Automorphic
