import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianDiagonalisation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedQuadraticMemBase

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n T hT`. Take `⟨-, hC, h2, hτ⟩` from `hCM`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`.

Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hτ τ, hτ τ, star_star]`. Establish `hnr : ¬ NumberField.ComplexEmbedding.IsReal τ`. Introduce `hr`. Use `hC.isComplex (NumberField.InfinitePlace.mk τ)` as an intermediate fact.

Rewrite `this` using `[NumberField.InfinitePlace.isComplex_mk_iff]`. Conclude with `this hr`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α, σ α ≠ α := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hnr` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `x`. Simplify using `only [NumberField.ComplexEmbedding.conjugate_coe_eq]`. Use `hτ τ x` as an intermediate fact.

Rewrite `this` using `[hcon x]`. Conclude with `this.symm`. Establish `hfix` using `UpperTheory.fixed_quadratic_mem_base h2 σ α hα`. Take `⟨g, D, h⟩` from `UpperTheory.hermitian_diagonalisation σ hinv hfix n T hT.1 hT.2`. Conclude with `⟨g, D, h⟩`.
-/
theorem UpperTheory.Reformulated.B.Gka4.diag_hermitian :
    ∀ (F E : Type) [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] (σ : E →ₐ[F] E),
      HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
        ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E),
          HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ T →
            ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ),
              HeckeCharacterZeroLocus.SiegelWeilU.cT (↑σ : E →+* E) (↑g : Matrix (Fin n) (Fin n) E) * T * (↑g : Matrix (Fin n) (Fin n) E) =
                Matrix.diagonal fun (i : Fin n) ↦ (Algebra.algebraMap F E : F → E) (↑(D i) : F) := by
  intro F E _ _ _ _ _ σ hCM n T hT
  obtain ⟨-, hC, h2, hτ⟩ := hCM
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ τ, hτ τ, star_star]
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal τ := by
    intro hr
    have := hC.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at this
    exact this hr
  obtain ⟨α, hα⟩ : ∃ α, σ α ≠ α := by
    by_contra hcon
    push_neg at hcon
    apply hnr
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have := hτ τ x
    rw [hcon x] at this
    exact this.symm
  have hfix := UpperTheory.fixed_quadratic_mem_base h2 σ α hα
  obtain ⟨g, D, h⟩ := UpperTheory.hermitian_diagonalisation σ hinv hfix n T hT.1 hT.2
  exact ⟨g, D, h⟩
