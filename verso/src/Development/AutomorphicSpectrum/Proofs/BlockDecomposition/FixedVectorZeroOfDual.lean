import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjectionStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

/- English proof (translation)
Introduce `G _ _ _ J hJ V _ _ π hπ u hu hl`. Take `⟨E, -, hfix, -, hinv, -⟩` from `GlobalTheory.T.compact_fixed_vector_projection G J hJ V π hπ`. Assume the negation of the conclusion as `hne`. Establish `hex : ∃ l0 : Module.Dual ℂ V, l0 u ≠ 0`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Conclude with `hne ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 hall)`. Take `⟨l0, hl0⟩` from `hex`. Establish `hzero : (l0 ∘ₗ E) u = 0`. Use `hl (l0 ∘ₗ E) fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_assoc, hinv x hx]`. Apply `hl0` to reduce the goal to its premises. Simplify `hzero` using `[hfix u hu]`.
-/
theorem invariant_forms_separate_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J,
      (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  intro G _ _ _ J hJ V _ _ π hπ u hu hl
  obtain ⟨E, -, hfix, -, hinv, -⟩ := GlobalTheory.T.compact_fixed_vector_projection G J hJ V π hπ
  by_contra hne
  have hex : ∃ l0 : Module.Dual ℂ V, l0 u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 hall)
  obtain ⟨l0, hl0⟩ := hex
  have hzero : (l0 ∘ₗ E) u = 0 := by
    refine hl (l0 ∘ₗ E) fun x hx => ?_
    rw [LinearMap.comp_assoc, hinv x hx]
  apply hl0
  simpa [hfix u hu] using hzero

end GlobalTheory.CompanionTheory.CompactAvg
