import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

/- English proof (translation)
Introduce `E _ _ z`. Establish `h0 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0` using `one_ne_zero`. Rewrite using `[FractionalIdeal.mem_dual h0]`. Prove the components needed by the constructor for the conclusion. Introduce `h o`.

Establish `h1` using `h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)`. Rewrite `h1` using `[Algebra.traceForm_apply, mul_comm]`. Take `⟨n, hn⟩` from `h1`. Establish `h2 : Algebra.trace ℚ E ((o : E) * z) = algebraMap ℤ ℚ n` using `hn.symm`. Rewrite using `[h2]`.

Conclude with `isIntegral_algebraMap`. Introduce `h a ha`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Rewrite using `[Algebra.traceForm_apply, mul_comm]`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (h o)`.

Conclude with `⟨n, hn⟩`.
-/
theorem UpperTheory.Gal.TP.Skew.memDual :
    UpperTheory.Gal.TP.Skew.MemDual := by
  intro E _ _ z
  have h0 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h0]
  constructor
  · intro h o
    have h1 := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at h1
    obtain ⟨n, hn⟩ := h1
    have h2 : Algebra.trace ℚ E ((o : E) * z) = algebraMap ℤ ℚ n := hn.symm
    rw [h2]
    exact isIntegral_algebraMap
  · intro h a ha
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h o)
    exact ⟨n, hn⟩
