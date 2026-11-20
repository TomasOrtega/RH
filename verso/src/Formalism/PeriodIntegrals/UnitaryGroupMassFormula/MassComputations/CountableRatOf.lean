import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NVolAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Unimod

noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

/- English proof (translation)
Use `haveI := PI.VolStabSW.um_countable_HFinIn F E σ M J`. Use `Function.Injective.countable (f := fun x : ratOf (K := K) => (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_comap.1 x.2⟩ : HFinIn (AF F) σ J)) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `e` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (Subtype.ext e)`.
-/
theorem countable_ratOf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (K : Subgroup (HA (AF F) σ J)) :
    Countable (ratOf (K := K)) := by
  haveI := PI.VolStabSW.um_countable_HFinIn F E σ M J
  refine Function.Injective.countable (f := fun x : ratOf (K := K) =>
    (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_comap.1 x.2⟩ : HFinIn (AF F) σ J)) ?_
  intro x y hxy
  have e := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext e)

/- English proof (translation)
Use `first`. Consider the case `exact inferInstance`. Consider the case `exact ⟨fun c s _ => by show μ ((fun x : K => (c : K) * x) ⁻¹' s) = μ s`. Conclude with `measure_preimage_mul μ (c : K) s⟩`.
-/
theorem smulInv_ratOf {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (K : Subgroup G)
    (Γ : Subgroup K) (μ : Measure K) [μ.IsMulLeftInvariant] : SMulInvariantMeasure Γ K μ := by
  first
  | exact inferInstance
  | exact ⟨fun c s _ => by
      show μ ((fun x : K => (c : K) * x) ⁻¹' s) = μ s
      exact measure_preimage_mul μ (c : K) s⟩

/- English proof (translation)
Use `haveI := hμ`. Use `haveI := countable_ratOf σ J K`. Use `haveI := smulInv_ratOf K (ratOf (K := K)) μ`. Unfold `covol`. Use `split_ifs with h`.

Use `congr 1`. Conclude with `h.choose_spec.measure_eq h𝓕`. Conclude with `absurd ⟨𝓕, h𝓕⟩ h`.
-/
theorem covol_eq_of_fd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [MeasurableMul (HA (AF F) σ J)]
    (K : Subgroup (HA (AF F) σ J)) (μ : Measure K) (hμ : μ.IsMulLeftInvariant) (𝓕 : Set K)
    (h𝓕 : IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) : covol μ = (μ 𝓕).toReal := by
  haveI := hμ
  haveI := countable_ratOf σ J K
  haveI := smulInv_ratOf K (ratOf (K := K)) μ
  unfold covol
  split_ifs with h
  · congr 1
    exact h.choose_spec.measure_eq h𝓕
  · exact absurd ⟨𝓕, h𝓕⟩ h

/- English proof (translation)
Introduce `D X u 𝓕 hN h𝓕`. Conclude with `covol_eq_of_fd _ _ _ _ hN.2.2.2.1.toIsMulLeftInvariant 𝓕 h𝓕`.
-/
theorem n4cov_holds : UnipotentCoveringCount := by
  intro D X u 𝓕 hN h𝓕
  exact covol_eq_of_fd _ _ _ _ hN.2.2.2.1.toIsMulLeftInvariant 𝓕 h𝓕

end MassDataMassesW
