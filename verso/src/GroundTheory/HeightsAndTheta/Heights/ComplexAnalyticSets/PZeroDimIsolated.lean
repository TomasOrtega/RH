import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroDimIsolated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Introduce `n I q hdim`. Establish `: Ring.KrullDimLE 0 (curveLocalRing I q)` using `Ring.krullDimLE_iff.2 (by simpa using hdim)`. Establish `hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I`. Introduce `i`. Establish `hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈ Ring.jacobson (curveLocalRing I q)`.

Rewrite using `[Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]`. Introduce `P hP`. Establish `hP' : Ideal.IsMaximal P` using `hP`. Set `π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q` to `Ideal.Quotient.mk _`. Establish `hPm : (Ideal.comap π P).IsMaximal` using `Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')`.

Establish `hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q)))`. Rewrite using `[IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]`. Simplify using `[RingHom.mem_ker]`. Rewrite `hL` using `[← IsLocalRing.eq_maximalIdeal hPm]`. Conclude with `hL`.

Rewrite `hmem` using `[Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical]`. Take `⟨k, hk⟩` from `hmem`. Rewrite `hk` using `[← map_pow]`. Establish `hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) ((X i - C (q i)) ^ k) ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))` using `Ideal.Quotient.eq_zero_iff_mem.1 hk`. Take `⟨m, hm, hmI⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap`.

Conclude with `⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩`. Use `choose s hs k hk using hnil`. Use `⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩` and prove the remaining obligations. Apply `(isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds` to reduce the goal to its premises. Simplify using `[map_prod, Finset.prod_ne_zero_iff, hs]`.

Introduce and unpack `x ⟨hxZ, hxN⟩`. Simplify using `only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN`. Rewrite using `[Set.mem_singleton_iff]`. Use function extensionality and compare the values at `i`. Establish `h` using `hxZ _ (hk i)`.

Simplify using `only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h`. Break down `h with h | ⟨h, -⟩` into its components or cases. Conclude with `absurd h (hxN i (Finset.mem_univ i))`. Conclude with `sub_eq_zero.1 h`.
-/
theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
