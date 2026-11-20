import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Measurability

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem countable_submodule (A : Type) [Ring A] (Λ : Type) [AddCommGroup Λ] [Module A Λ]
    [Module.Free ℤ Λ] [Module.Finite ℤ Λ] : Countable (Submodule A Λ) := by
  have hΛ : Countable Λ :=
    (Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable
  have hZ : Countable (Submodule ℤ Λ) := by
    have hs : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ)) := by
      intro N
      obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
      exact ⟨s, hs⟩
    exact hs.countable
  exact (Submodule.restrictScalars_injective ℤ A Λ).countable

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem measurable_cuspW (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [MeasurableSpace X] (R : X → RiemLat E g Λ)
    (σ : Ψ → (𝓞 E →+* ℂ)) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hform : ∀ x, (R x).form = form)
    (hnz : ∀ I, Measurable fun x => (R x).nz σ I)
    (_hbdd : ∀ x, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)}) :
    Measurable fun x => (R x).cuspW σ := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact measurable_of_empty _
  haveI := (R x₀).free
  haveI := (R x₀).fin
  haveI : Countable (Submodule (𝓞 E) Λ) := countable_submodule (𝓞 E) Λ
  let C : Submodule (𝓞 E) Λ → Prop := fun I => I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧
    GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I
  have hC : ∀ x I, (R x).IsCusp I ↔ C I := by
    intro x I
    simp only [RiemLat.IsCusp, C, hform x]
  have hset : ∀ x, {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} =
      Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1) := by
    intro x
    ext y
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨I, (hC x I).1 hI⟩, rfl⟩
    · rintro ⟨I, rfl⟩
      exact ⟨I.1, (hC x I.1).2 I.2, rfl⟩
  have hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1) :=
    Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg
  have heq : (fun x => (R x).cuspW σ) = fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)) := by
    funext x
    simp only [RiemLat.cuspW, hset x, iSup]
  rw [heq]
  exact measurable_const.max hsup

end GlobalTheory.CompanionTheory.Ar.Cusp.Measurability
