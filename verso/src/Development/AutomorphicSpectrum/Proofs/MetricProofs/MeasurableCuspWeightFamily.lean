import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Measurability

/- English proof (translation)
Establish `hΛ : Countable Λ` using `(Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable`. Establish `hZ : Countable (Submodule ℤ Λ)`. Establish `hs : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ))`. Introduce `N`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian N : N.FG)`.

Conclude with `⟨s, hs⟩`. Conclude with `hs.countable`. Conclude with `(Submodule.restrictScalars_injective ℤ A Λ).countable`.
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
Break down `isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩` into its components or cases. Conclude with `measurable_of_empty _`. Use `haveI := (R x₀).free`. Use `haveI := (R x₀).fin`. Use `haveI : Countable (Submodule (𝓞 E) Λ) := countable_submodule (𝓞 E) Λ`.

Set `C : Submodule (𝓞 E) Λ → Prop` to `fun I => I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I`. Establish `hC : ∀ x I, (R x).IsCusp I ↔ C I`. Introduce `x I`. Simplify using `only [RiemLat.IsCusp, C, hform x]`. Establish `hset : ∀ x, {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} = Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1)`.

Introduce `x`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨I, hI, rfl⟩`. Conclude with `⟨⟨I, (hC x I).1 hI⟩, rfl⟩`.

Introduce and unpack `⟨I, rfl⟩`. Conclude with `⟨I.1, (hC x I.1).2 I.2, rfl⟩`. Establish `hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)` using `Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg`. Establish `heq : (fun x => (R x).cuspW σ) = fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1))`. Use function extensionality and compare the values at `x`.

Simplify using `only [RiemLat.cuspW, hset x, iSup]`. Rewrite using `[heq]`. Conclude with `measurable_const.max hsup`.
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
