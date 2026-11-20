import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
private lemma span_add_le {H : Type} [Group H] (K : Subgroup H) (f f' : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (f + f') (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} ⊔
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f' (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, _,
    Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, ?_⟩
  funext g; simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma span_smul_le {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (f : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (c • f) (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  have : (fun g => (c • f) (k * g * k')) = c • fun g => f (k * g * k') := by funext g; simp
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, k', hk', rfl⟩)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private lemma span_zero_le {H : Type} [Group H] (K : Subgroup H) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (0 : H → ℂ) (k * g * k')} ≤ ⊥ := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions.

A detailed English derivation is pending.
-/
theorem isBiFinite_subspace : ∀ (H : Type) [Group H] (K : Subgroup H), IsBiFinite K (0 : H → ℂ) ∧
    (∀ f f' : H → ℂ, IsBiFinite K f → IsBiFinite K f' → IsBiFinite K (f + f')) ∧
    ∀ (c : ℂ) (f : H → ℂ), IsBiFinite K f → IsBiFinite K (c • f) := by
  intro H _ K
  refine ⟨?_, fun f f' hf hf' => ?_, fun c f hf => ?_⟩
  · unfold IsBiFinite
    exact Submodule.finiteDimensional_of_le (span_zero_le K)
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_add_le K f f')
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_smul_le K c f)

end GlobalTheory
