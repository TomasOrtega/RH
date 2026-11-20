import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Ideal.GoingUp

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

/- English proof (translation)
Introduce `B S _ _ _ _ _ _ v hv`. Establish `hrad : v ∈ ((maximalIdeal B).map (algebraMap B S)).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce `J hJ'`. Take `⟨hJ, hJp⟩` from `hJ'`.

Establish `hle : maximalIdeal B ≤ Ideal.comap (algebraMap B S) J`. Introduce `b hb`. Conclude with `hJ (Ideal.mem_map_of_mem _ hb)`. Establish `hc : Ideal.comap (algebraMap B S) J = maximalIdeal B` using `((IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (Ideal.comap_ne_top _ hJp.ne_top) hle).symm`. Establish `hcm : (Ideal.comap (algebraMap B S) J).IsMaximal`.

Rewrite using `[hc]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal B`. Establish `hJm : J.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap J hcm`. Rewrite using `[IsLocalRing.eq_maximalIdeal hJm]`. Conclude with `hv`.

Take `⟨n, hn⟩` from `hrad`. Establish `hN : v ^ (n + 1) ∈ (maximalIdeal B).map (algebraMap B S)`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_right _ _ hn`. Establish `hrange : LinearMap.range (Algebra.lmul B S (v ^ (n + 1))) ≤ (maximalIdeal B) • (⊤ : Submodule B S)`.

Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]`. Simplify using `using Ideal.mul_mem_right s _ hN`. Take `⟨p, hpm, -, hpc, hpa⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (R := B) (M := S) (Algebra.lmul B S (v ^ (n + 1))) (maximalIdeal B) hrange`. Use `⟨expand B (n + 1) p, ⟨hpm.expand (Nat.succ_pos n), ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Rewrite `hk` using `[natDegree_expand]`. Rewrite using `[coeff_expand (Nat.succ_pos n)]`. Use `split_ifs with hd`. Establish `hlt : k / (n + 1) < p.natDegree`.

Rewrite using `[Nat.div_lt_iff_lt_mul (Nat.succ_pos n)]`. Conclude with `hk`. Conclude with `Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) (hpc _)`. Conclude with `zero_mem _`. Rewrite using `[expand_aeval]`.

Rewrite `hpa` using `[Polynomial.aeval_algHom_apply]`. Establish `h1` using `LinearMap.congr_fun hpa 1`. Simplify using `using h1`.
-/
theorem UpperTheory.V.Ws.Pp.nilPoly :
    ∀ {B S : Type} [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Algebra B S] [Module.Finite B S] (v : S), v ∈ maximalIdeal S → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro B S _ _ _ _ _ _ v hv
  have hrad : v ∈ ((maximalIdeal B).map (algebraMap B S)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro J hJ'
    obtain ⟨hJ, hJp⟩ := hJ'
    have hle : maximalIdeal B ≤ Ideal.comap (algebraMap B S) J := by
      intro b hb
      exact hJ (Ideal.mem_map_of_mem _ hb)
    have hc : Ideal.comap (algebraMap B S) J = maximalIdeal B :=
      ((IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (Ideal.comap_ne_top _ hJp.ne_top) hle).symm
    have hcm : (Ideal.comap (algebraMap B S) J).IsMaximal := by
      rw [hc]
      exact IsLocalRing.maximalIdeal.isMaximal B
    have hJm : J.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap J hcm
    rw [IsLocalRing.eq_maximalIdeal hJm]
    exact hv
  obtain ⟨n, hn⟩ := hrad
  have hN : v ^ (n + 1) ∈ (maximalIdeal B).map (algebraMap B S) := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  have hrange : LinearMap.range (Algebra.lmul B S (v ^ (n + 1))) ≤
      (maximalIdeal B) • (⊤ : Submodule B S) := by
    rintro _ ⟨s, rfl⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    simpa using Ideal.mul_mem_right s _ hN
  obtain ⟨p, hpm, -, hpc, hpa⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (R := B) (M := S) (Algebra.lmul B S (v ^ (n + 1))) (maximalIdeal B) hrange
  refine ⟨expand B (n + 1) p, ⟨hpm.expand (Nat.succ_pos n), ?_⟩, ?_⟩
  · intro k hk
    rw [natDegree_expand] at hk
    rw [coeff_expand (Nat.succ_pos n)]
    split_ifs with hd
    · have hlt : k / (n + 1) < p.natDegree := by
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos n)]
        exact hk
      exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) (hpc _)
    · exact zero_mem _
  · rw [expand_aeval]
    rw [Polynomial.aeval_algHom_apply] at hpa
    have h1 := LinearMap.congr_fun hpa 1
    simpa using h1
