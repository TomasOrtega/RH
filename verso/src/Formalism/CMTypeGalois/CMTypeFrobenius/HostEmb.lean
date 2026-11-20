import Mathlib
import Formalism.CMTypeGalois.StatementField

open NumberField Finset

noncomputable section

namespace Formalism.Q3

open Classical in
/- English proof (translation)
Introduce `q hq E _ _ α hα φ₀`. Take `⟨hGal, hfin, hbij, hmul⟩` from `hH q hq E α hα`. Use `hGal` as an intermediate fact. Establish `hconj` using `(hC q hq E α hα).1`. Use `set F : Gal(E/ℚ) → (E →+* ℂ) := fun σ => φ₀.comp σ.toAlgHom.toRingHom with hF`.

Establish `hinj : Function.Injective F`. Introduce `σ τ h`. Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `x`. Use `congrArg (fun f : E →+* ℂ => f x) h` as an intermediate fact.

Conclude with `φ₀.injective this`. Establish `hcard : Fintype.card Gal(E/ℚ) = Fintype.card (E →+* ℂ)`. Rewrite using `[NumberField.Embeddings.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]`. Establish `hFbij : Function.Bijective F` using `(Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩`. Establish `hcc : ∀ σ τ : Gal(E/ℚ), galSign α τ = cc → F (τ * σ) = ComplexEmbedding.conjugate (F σ)`.

Introduce `σ τ hτ`. Establish `h1` using `(hconj φ₀ τ).mpr hτ`. Use extensionality with `y`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `h1 (σ y)`.

Use `⟨hFbij, hcc, ?_⟩` and prove the remaining obligations. Introduce `Φ`. Take `⟨τc, hτc⟩` from `hbij.2 cc`. Establish `hmem : ∀ σ, F σ ∈ (univ.filter (fun σ : Gal(E/ℚ) => galSign α σ ∈ Φ)).image F ↔ galSign α σ ∈ Φ`. Introduce `σ`.

Simplify using `only [mem_image, mem_filter, mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, he⟩`. Rewrite using `[← hinj he]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `⟨σ, h, rfl⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hΦ ψ`. Take `⟨σ, rfl⟩` from `hFbij.2 ψ`. Rewrite using `[← hcc σ τc hτc, hmem, hmem, hmul, hτc]`.

Conclude with `hΦ _`. Introduce `hT g`. Take `⟨σ, rfl⟩` from `hbij.2 g`. Use `hT (F σ)` as an intermediate fact. Rewrite `this` using `[← hcc σ τc hτc, hmem, hmem, hmul, hτc]`.

Conclude with `this`.
-/
theorem hostEmb_of (hC : HostConj) (hH : HostGalois) : HostEmb := by
  intro q hq E _ _ α hα φ₀
  obtain ⟨hGal, hfin, hbij, hmul⟩ := hH q hq E α hα
  have := hGal
  have hconj := (hC q hq E α hα).1
  set F : Gal(E/ℚ) → (E →+* ℂ) := fun σ => φ₀.comp σ.toAlgHom.toRingHom with hF
  have hinj : Function.Injective F := by
    intro σ τ h
    apply AlgEquiv.ext
    intro x
    have := congrArg (fun f : E →+* ℂ => f x) h
    exact φ₀.injective this
  have hcard : Fintype.card Gal(E/ℚ) = Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩
  have hcc : ∀ σ τ : Gal(E/ℚ), galSign α τ = cc →
      F (τ * σ) = ComplexEmbedding.conjugate (F σ) := by
    intro σ τ hτ
    have h1 := (hconj φ₀ τ).mpr hτ
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1 (σ y)
  refine ⟨hFbij, hcc, ?_⟩
  intro Φ
  obtain ⟨τc, hτc⟩ := hbij.2 cc
  have hmem : ∀ σ, F σ ∈ (univ.filter (fun σ : Gal(E/ℚ) => galSign α σ ∈ Φ)).image F ↔
      galSign α σ ∈ Φ := by
    intro σ
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨s, hs, he⟩
      rwa [← hinj he]
    · intro h
      exact ⟨σ, h, rfl⟩
  constructor
  · intro hΦ ψ
    obtain ⟨σ, rfl⟩ := hFbij.2 ψ
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc]
    exact hΦ _
  · intro hT g
    obtain ⟨σ, rfl⟩ := hbij.2 g
    have := hT (F σ)
    rw [← hcc σ τc hτc, hmem, hmem, hmul, hτc] at this
    exact this

end Formalism.Q3
