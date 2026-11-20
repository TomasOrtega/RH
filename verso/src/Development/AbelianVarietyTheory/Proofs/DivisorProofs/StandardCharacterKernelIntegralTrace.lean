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
Establish `e : t = pairA F 0 (algebraMap F (Af F) a)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective` to reduce the goal to its premises. Conclude with `ht.trans (map_zero _).symm`. Use `show t.2 = algebraMap F (Af F) a`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Conclude with `hv v`. Rewrite `h1` using `[e, GlobalTheory.PsiNontriv.isStd_fin_rat hψ]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h1`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h2 : ((Algebra.trace ℚ F a : ℚ) : ℂ) = (n : ℂ)`. Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Apply `mul_left_cancel₀ hpi` to reduce the goal to its premises.

Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h2` after adjusting the coercions.
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
