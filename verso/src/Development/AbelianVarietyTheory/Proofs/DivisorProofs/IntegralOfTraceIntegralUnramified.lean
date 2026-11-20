import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
open scoped nonZeroDivisors

namespace GlobalTheory.LieDisc

/- English proof (translation)
Introduce `E _ _ _ hu w hw`. Use `set F := maximalRealSubfield E`. Establish `hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)` using `by haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu infer_instance`. Establish `hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤` using `(GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu`. Establish `h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`.

Establish `hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1`. Establish `h` using `coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)`. Rewrite `h` using `[hd, FractionalIdeal.coeIdeal_top]`. Conclude with `(inv_eq_one.1 h.symm)`. Establish `hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)`.

Rewrite using `[FractionalIdeal.mem_dual h10]`. Introduce `a ha`. Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Rewrite using `[Algebra.traceForm_apply]`. Establish `ht` using `Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)`.

Establish `hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b))`. Rewrite using `[← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective F E), ht]`. Conclude with `hw _ (RingOfIntegers.isIntegral_coe b)`. Conclude with `⟨⟨_, hi⟩, rfl⟩`. Rewrite `hmem` using `[hdual]`.

Take `⟨z, hz⟩` from `(FractionalIdeal.mem_one_iff _).1 hmem`. Rewrite using `[← hz]`. Conclude with `RingOfIntegers.isIntegral_coe z`.
-/
theorem isIntegral_of_trace_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E,
      (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  intro E _ _ _ hu w hw
  set F := maximalRealSubfield E
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu
    infer_instance
  have hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [hd, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  have hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have ht := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)
    have hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b)) := by
      rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective F E), ht]
      exact hw _ (RingOfIntegers.isIntegral_coe b)
    exact ⟨⟨_, hi⟩, rfl⟩
  rw [hdual] at hmem
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

end GlobalTheory.LieDisc
