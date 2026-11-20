import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeoUnder

/- English proof (translation)
Introduce `D χ w hg hχ`. Establish `hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot`. Establish `hint : IsIntegral ℤ x` using `Algebra.IsIntegral.isIntegral x`. Conclude with `Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)`.

Set `v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))` to `{ asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) isPrime := Ideal.comap_isPrime _ _ ne_bot := hne }`. Use `⟨v, rfl, ?_, w, rfl, hχ⟩` and prove the remaining obligations. Introduce and unpack `⟨w', hw', k, hk⟩`. Apply `hg k` to reduce the goal to its premises. Establish `h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal`.

Rewrite using `[← hw']`. Use `show algebraMap _ _ _ ∈ w'.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hk`. Use `show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal`.

Establish `h2` using `h1`. Express the relevant statement in the definitionally equal form `algebraMap _ _ _ ∈ w.asIdeal at h2`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis.
-/
theorem exists_under_in_qPl : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  intro D χ w hg hχ
  have hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := hne }
  refine ⟨v, rfl, ?_, w, rfl, hχ⟩
  rintro ⟨w', hw', k, hk⟩
  apply hg k
  have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw']
    show algebraMap _ _ _ ∈ w'.asIdeal
    rw [map_natCast]; exact hk
  show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  have h2 := h1
  change algebraMap _ _ _ ∈ w.asIdeal at h2
  rwa [map_natCast] at h2

end GlobalTheory.GeoUnder
