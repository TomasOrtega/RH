import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ

namespace GlobalTheory.TraceRealPartConjugateSum

open NumberField

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl`.
-/
theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl

/- English proof (translation)
Use `set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ`. Establish `hconj : ∀ τ : E →+* ℂ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x`. Introduce `τ`. Rewrite using `[map_add, ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc, IsCMField.complexEmbedding_complexConj]`. Establish `himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate`.

Use extensionality with `τ`. Simplify using `only [Finset.mem_compl, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩` and prove the remaining obligations.

Rewrite using `[X.cmType, ComplexEmbedding.involutive_conjugate E τ]`. Conclude with `h`. Introduce and unpack `⟨σ, hσ, rfl⟩`. Conclude with `(X.cmType σ).1 hσ`. Establish `hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x`.

Rewrite using `[← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg, Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h), ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun τ _ => hconj τ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]`. Use `_ = _ := by`.

Rewrite using `[hsum, ← trace_eq_sum_ringHom x]`. Simplify using the standard rewrite rules.
-/
theorem sum_re_add_conj {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : E) :
    ∑ τ : ↥(ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X),
      Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) =
      (↑((Algebra.trace ℚ E : E → ℚ) x) : ℝ) := by
  classical
  set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ
  have hconj : ∀ τ : E →+* ℂ,
      τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x := by
    intro τ
    rw [map_add, ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc,
      IsCMField.complexEmbedding_complexConj]
  have himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E τ]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x := by
    rw [← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg,
      Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => hconj τ
  calc ∑ τ : ↥Ψ, Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))
      = Complex.re (∑ τ : ↥Ψ, (↑τ : E →+* ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := (Complex.re_sum _ _).symm
    _ = Complex.re (∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := by
      rw [Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]
    _ = _ := by
      rw [hsum, ← trace_eq_sum_ringHom x]
      simp

end GlobalTheory.TraceRealPartConjugateSum
