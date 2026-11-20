import Mathlib

namespace GlobalTheory.TargetInequalityLemmas

open Polynomial

/- English proof (translation)
Rewrite `hz` using `[Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]`. Simplify using `only [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]`. Take `⟨p, rfl⟩` from `hz`. Take `⟨b, hbM, hb⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors R) p`. Use `⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors R) p, ?_⟩` and prove the remaining obligations.

Establish `hmap : (IsLocalization.integerNormalization (nonZeroDivisors R) p).map (algebraMap R F) = C (algebraMap R F b) * p`. Rewrite using `[hb]`. Use extensionality with `i`. Rewrite using `[coeff_smul, coeff_C_mul, Algebra.smul_def]`. Rewrite using `[← aeval_map_algebraMap F, hmap, map_mul, aeval_C, ← IsScalarTower.algebraMap_apply]`.
-/
theorem main {R F K : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K] (θ z : K)
    (hz : z ∈ Algebra.adjoin F ({θ} : Set K)) :
    ∃ d : R, d ≠ 0 ∧ (algebraMap R K d * z) ∈ Algebra.adjoin R ({θ} : Set K) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
  simp only [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors R) p, ?_⟩
  have hmap : (IsLocalization.integerNormalization (nonZeroDivisors R) p).map (algebraMap R F)
      = C (algebraMap R F b) * p := by
    rw [hb]
    ext i
    rw [coeff_smul, coeff_C_mul, Algebra.smul_def]
  rw [← aeval_map_algebraMap F, hmap, map_mul, aeval_C, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Introduce `θ z hz` and use `main θ z hz`.
-/
theorem target : ∀ {R F K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field F] [inst_3 : Algebra R F] [IsFractionRing R F] [inst_5 : Field K] [inst_6 : Algebra R K] [inst_7 : Algebra F K] [IsScalarTower R F K] (θ z : K), Membership.mem (Algebra.adjoin F (Singleton.singleton θ)) z → Exists fun (d : R) ↦ And (Ne d (0 : R)) (Membership.mem (Algebra.adjoin R (Singleton.singleton θ)) (HMul.hMul ((Algebra.algebraMap R K) d) z)) :=
  fun θ z hz => main θ z hz

end GlobalTheory.TargetInequalityLemmas
