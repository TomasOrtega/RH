import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `H _ K f hf`. Take `⟨hbi, S, hS⟩` from `hf`. Establish `hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g` using `fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g`. Use `⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩` and prove the remaining obligations. Introduce and unpack `x ⟨y, hy, rfl⟩`.

Conclude with `hy`. Introduce `k hk g`. Conclude with `hinv _ (K.inv_mem hk) _ hk g`. Introduce `g hg`. Take `⟨s, hs, a, b, rfl⟩` from `hS g hg`.

Conclude with `⟨s, hs, a, a.2, b, b.2, rfl⟩`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.testOf_of :
    TestOf := by
  intro H _ K f hf
  obtain ⟨hbi, S, hS⟩ := hf
  have hinv : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g :=
    fun k hk k' hk' g => hbi ⟨k, hk⟩ ⟨k', hk'⟩ g
  refine ⟨⟨Subgroup.Commensurable.refl K, ?_, ?_, S, ?_⟩, hinv⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro k hk g
    exact hinv _ (K.inv_mem hk) _ hk g
  · intro g hg
    obtain ⟨s, hs, a, b, rfl⟩ := hS g hg
    exact ⟨s, hs, a, a.2, b, b.2, rfl⟩
