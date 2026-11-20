import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.SecondCountableTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hCM.2.2.2, hCM.2.2.2, star_star]`.
-/
theorem sig_sig (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (y : E) : σ (σ y) = y := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2, hCM.2.2.2, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hc` using `hCM.2.1.isComplex (InfinitePlace.mk τ)`. Rewrite `hc` using `[← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff]`.

Apply `hc` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq]`. Use `hCM.2.2.2 τ x` as an intermediate fact. Rewrite `this` using `[h x]`.

Conclude with `this.symm`.
-/
theorem sig_nt (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra h
  push Not at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc := hCM.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  apply hc
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have := hCM.2.2.2 τ x
  rw [h x] at this
  exact this.symm

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)`. Conclude with `Formalism.L2.Fam.ThC.alg_trace_gen σ (PI.OmLocU.SdB.trace_eq_add σ (sig_sig σ hCM) (sig_nt σ hCM) hCM.2.2.1) z`.
-/
theorem trace_add (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (z : Ainf F ⊗[F] E) :
    algebraMap (Ainf F) (Ainf F ⊗[F] E) (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) = z + sigR (Ainf F) σ z := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
  exact Formalism.L2.Fam.ThC.alg_trace_gen σ
    (PI.OmLocU.SdB.trace_eq_add σ (sig_sig σ hCM) (sig_nt σ hCM) hCM.2.2.1) z

end PositivityTheory.SiegelWeilFormula.GReal
