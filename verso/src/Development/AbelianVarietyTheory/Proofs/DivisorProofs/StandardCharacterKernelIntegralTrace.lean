import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.DenomTrace

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem trace_int_of_psi_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (t : AF F) (a : F) (ht : evI F t = 0)
    (hv : ∀ v, evFin F v t = algebraMap F (Fv F v) a) (h1 : ψ t = 1) : ∃ z : ℤ, Algebra.trace ℚ F a = z := by
  have e : t = pairA F 0 (algebraMap F (Af F) a) := by
    refine Prod.ext ?_ ?_
    · apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
      exact ht.trans (map_zero _).symm
    · show t.2 = algebraMap F (Af F) a
      apply Subtype.ext
      funext v
      exact hv v
  rw [e, GlobalTheory.PsiNontriv.isStd_fin_rat hψ] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨n, ?_⟩
  have h2 : ((Algebra.trace ℚ F a : ℚ) : ℂ) = (n : ℂ) := by
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  exact_mod_cast h2

end GlobalTheory.DenomTrace
