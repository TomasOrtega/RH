import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.CMImag

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hconj : ∀ x, τ (σ x) = star (τ x)` using `h.2.2.2 τ`. Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => by`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hconj, hconj, star_star]`. Establish `hne : ∃ x, σ x ≠ x`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hTC` using `h.2.1`.

Apply `NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Use `hconj x` as an intermediate fact. Rewrite `this` using `[hall x]`.

Simplify `this.symm` using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Take `⟨x, hx⟩` from `hne`. Use `⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hinv, neg_sub]`.
-/
theorem exists_imag_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : ∀ x, τ (σ x) = star (τ x) := h.2.2.2 τ
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    have hTC := h.2.1
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hconj x
    rw [hall x] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMImag
