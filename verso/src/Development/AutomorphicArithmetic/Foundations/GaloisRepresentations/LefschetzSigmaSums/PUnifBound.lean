import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
open UpperTheory.Gal.LocalSmoothExtension

open scoped Classical in
/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `Set.toFinite _`. Set `i₀ : Fin n` to `⟨0, hn⟩`. Set `c : ℕ` to `∑ τ ∈ (Finset.univ.erase t₀).erase (NumberField.ComplexEmbedding.conjugate t₀), ε τ * ∑ j, lam τ j`. Set `h₁ : Fin n → ℕ` to `fun i => ((n - 1) * lam (NumberField.ComplexEmbedding.conjugate t₀) i₀ + c) + (lam t₀ i + (n - 1 - (i : ℕ)))`.

Set `h₂ : Fin n → ℕ` to `fun i => (lam t₀ i₀ + c) + (∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j + (i : ℕ))`. Use `(Set.toFinite ({h₁, h₂} : Set (Fin n → ℕ))).subset ?_` and prove the remaining obligations. Introduce and unpack `h (⟨m, hm, hh⟩ | ⟨m, hm, hh⟩)`. Use `left`. Use function extensionality and compare the values at `i`.

Rewrite using `[hh i, ← hm i₀]`. Use `right`. Use function extensionality and compare the values at `i`. Rewrite using `[hh i, ← hm i₀]`.
-/
private lemma hexp_finite {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ)
    (lam : (F →+* ℂ) → Fin n → ℕ) : {h : Fin n → ℕ | IsHExp t₀ ε lam h}.Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.toFinite _
  · let i₀ : Fin n := ⟨0, hn⟩
    let c : ℕ := ∑ τ ∈ (Finset.univ.erase t₀).erase (NumberField.ComplexEmbedding.conjugate t₀),
      ε τ * ∑ j, lam τ j
    let h₁ : Fin n → ℕ := fun i => ((n - 1) * lam (NumberField.ComplexEmbedding.conjugate t₀) i₀ + c) +
      (lam t₀ i + (n - 1 - (i : ℕ)))
    let h₂ : Fin n → ℕ := fun i => (lam t₀ i₀ + c) +
      (∑ j ∈ Finset.univ.erase i, lam (NumberField.ComplexEmbedding.conjugate t₀) j + (i : ℕ))
    refine (Set.toFinite ({h₁, h₂} : Set (Fin n → ℕ))).subset ?_
    rintro h (⟨m, hm, hh⟩ | ⟨m, hm, hh⟩)
    · left
      funext i
      rw [hh i, ← hm i₀]
    · right
      funext i
      rw [hh i, ← hm i₀]

/- English proof (translation)
Introduce `F _ _ n I _ t ε lam κ`. Establish `hb : ∀ (π : (F →+* ℂ) → (F →+* ℂ)) (i : I), ∃ b, ∀ h : Fin n → ℕ, IsHExp (t i) ε (fun τ => lam (π τ)) h → κ (fun τ => lam (π τ)) i h ≤ b`. Introduce `π i`. Take `⟨b, hb⟩` from `((hexp_finite (t i) ε (fun τ => lam (π τ))).image (κ (fun τ => lam (π τ)) i)).bddAbove`. Conclude with `⟨b, fun h hh => hb ⟨h, hh, rfl⟩⟩`.

Use `choose b hb using hb`. Take `⟨k, hk⟩` from `Finite.exists_le (fun q : ((F →+* ℂ) → (F →+* ℂ)) × I => b q.1 q.2)`. Use `⟨k, fun σ i h hh => ?_⟩` and prove the remaining obligations. Conclude with `(hb (fun τ => (σ.symm : ℂ →+* ℂ).comp τ) i h hh).trans (hk ((fun τ => (σ.symm : ℂ →+* ℂ).comp τ), i))`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.unifBound_of :
    UnifBound := by
  intro F _ _ n I _ t ε lam κ
  have hb : ∀ (π : (F →+* ℂ) → (F →+* ℂ)) (i : I), ∃ b, ∀ h : Fin n → ℕ,
      IsHExp (t i) ε (fun τ => lam (π τ)) h → κ (fun τ => lam (π τ)) i h ≤ b := by
    intro π i
    obtain ⟨b, hb⟩ := ((hexp_finite (t i) ε (fun τ => lam (π τ))).image
      (κ (fun τ => lam (π τ)) i)).bddAbove
    exact ⟨b, fun h hh => hb ⟨h, hh, rfl⟩⟩
  choose b hb using hb
  obtain ⟨k, hk⟩ := Finite.exists_le (fun q : ((F →+* ℂ) → (F →+* ℂ)) × I => b q.1 q.2)
  refine ⟨k, fun σ i h hh => ?_⟩
  exact (hb (fun τ => (σ.symm : ℂ →+* ℂ).comp τ) i h hh).trans
    (hk ((fun τ => (σ.symm : ℂ →+* ℂ).comp τ), i))
