import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ArchFourier

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Put the polynomial expressions in normal form. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem fourier_twice_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ d : ℂ, d ≠ 0 ∧ ∀ (f : SInf F κ) (a : κ → mixedEmbedding.mixedSpace F),
      ∫ y, (∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ a) : ℝ)) ∂μ =
      d * f (-a) := by
  intro F _ _ κ _ _ _ μ hμ
  classical
  obtain ⟨⟨c, hc, hinv⟩, hint⟩ := GlobalTheory.fourier_inversion_haar_symm_form (-(traceDot F κ))
    (fun x y => by simp only [LinearMap.neg_apply, traceDot_comm x y])
    (fun x hx => traceDot_nondeg x (fun y => by simpa using hx y)) μ hμ
  refine ⟨(c : ℂ), by exact_mod_cast hc.ne', fun f a => ?_⟩
  have hk : ∀ x y : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (2 * Real.pi * Complex.I * (((-(traceDot F κ)) x y : ℝ) : ℂ)) =
        Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) := by
    intro x y
    rw [LinearMap.neg_apply, LinearMap.neg_apply, traceDot_apply]
    push_cast
    ring_nf
  have h := hinv f f.continuous (hint f).1 (hint f).2 a
  simp only [hk] at h
  exact h

end GlobalTheory.ArchFourier
