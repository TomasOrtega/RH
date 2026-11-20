import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecThrough

/- English proof (translation)
Introduce `E _ _ _ S₀ hS₀`. Set `f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E))` to `fun w => w.under (𝓞 (maximalRealSubfield E))`. Establish `hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w`. Introduce and unpack `⟨_, w₀, rfl⟩`. Distinguish the cases in `h : ∃ w ∈ S₀, f w = f w₀`.

Take `⟨w, hw, hfw⟩` from `h`. Conclude with `⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩`. Conclude with `⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩`. Set `g : Set.range f → Pl E` to `fun y => (hex y).choose`. Establish `hg : ∀ y, f (g y) = y.1` using `fun y => (hex y).choose_spec.1`.

Establish `hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w` using `fun y => (hex y).choose_spec.2`. Use `⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨y, rfl⟩, hy⟩`. Conclude with `congrArg g (Subtype.ext ((hg y).symm.trans hy))`. Introduce `w hw`.

Conclude with `⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩`. Introduce `w hw`. Use `⟨⟨f w, w, rfl⟩, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hw ⟨_, hne, hg _⟩`.
-/
theorem secEx : SecEx := by
  intro E _ _ _ S₀ hS₀
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under (𝓞 (maximalRealSubfield E))
  have hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w := by
    rintro ⟨_, w₀, rfl⟩
    by_cases h : ∃ w ∈ S₀, f w = f w₀
    · obtain ⟨w, hw, hfw⟩ := h
      exact ⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩
    · exact ⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩
  let g : Set.range f → Pl E := fun y => (hex y).choose
  have hg : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.1
  have hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w := fun y => (hex y).choose_spec.2
  refine ⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg g (Subtype.ext ((hg y).symm.trans hy))
  · intro w hw
    exact ⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩
  · intro w hw
    refine ⟨⟨f w, w, rfl⟩, ?_⟩
    by_contra hne
    exact hw ⟨_, hne, hg _⟩

end GlobalTheory.CompanionTheory.SecThrough

end
