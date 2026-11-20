import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `R A _ _ _ _ _ hdepth het f hf`. Take `⟨rs, hlen, hmem, hreg⟩` from `hdepth`. Take `⟨w, hw⟩ : ∃ w, rs = [w]` from `List.length_eq_one_iff.mp hlen`. Substitute `hw` using the available equality. Establish `hwm : w ∈ maximalIdeal R` using `hmem w (by simp)`.

Establish `hwr : IsSMulRegular A w` using `((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1`. Establish `hmax : maximalIdeal R ∉ associatedPrimes R A` using `ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr`. Use `IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `ha0`. Take `⟨P, hP, hle⟩` from `exists_le_isAssociatedPrime_of_isNoetherianRing R a ha0`.

Establish `hfP : f ∈ P` using `hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))`. Take `⟨hPprime, b, hb⟩` from `Submodule.isAssociatedPrime_iff.mp hP`. Use `haveI := hPprime`. Establish `hPm : P ≠ maximalIdeal R` using `fun h => hmax (h ▸ hP)`. Use `haveI := het P hPm`.

Use `set L := Localization.AtPrime P`. Use `haveI : Module.Free L (TensorProduct R L A) := Module.free_of_flat_of_isLocalRing`. Establish `hfb : f • b = 0`. Establish `: f ∈ (⊥ : Submodule R A).colon {b}` using `hb ▸ hfP`. Simplify using `using Submodule.mem_colon_singleton.mp this`.

Establish `hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk R L A 1)` using `(isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange R A L)`. Establish `hfL : algebraMap R L f ≠ 0`. Introduce `h0`. Apply `hf` to reduce the goal to its premises. Conclude with `(IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)`.

Establish `h1 : (1 : L) ⊗ₜ[R] b = 0`. Establish `: algebraMap R L f • ((1 : L) ⊗ₜ[R] b) = 0`. Rewrite using `[algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]`. Conclude with `(smul_eq_zero.mp this).resolve_left hfL`. Take `⟨t, ht⟩` from `(IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk R L A 1)).mp h1`.

Establish `htP : (t : R) ∈ P`. Establish `: (t : R) ∈ (⊥ : Submodule R A).colon {b}` using `Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)`. Conclude with `hb ▸ this`. Conclude with `t.2 htP`.
-/
theorem isSMulRegular_of_etale_punctured_of_depth_pos :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 →
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  intro R A _ _ _ _ _ hdepth het f hf

  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal R := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal R ∉ associatedPrimes R A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr

  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal R := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Free L (TensorProduct R L A) := Module.free_of_flat_of_isLocalRing
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule R A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk R L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange R A L)
  have hfL : algebraMap R L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[R] b = 0 := by
    have : algebraMap R L f • ((1 : L) ⊗ₜ[R] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp this).resolve_left hfL
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk R L A 1)).mp h1
  have htP : (t : R) ∈ P := by
    have : (t : R) ∈ (⊥ : Submodule R A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
