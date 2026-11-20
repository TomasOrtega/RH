import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Introduce `L F _ _ _ _ _ 𝔡 b₀ hb₀`. Use `⟨b₀ * ∏ P ∈ 𝔡.support, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L), ?_, dvd_mul_right _ _, ?_⟩` and prove the remaining obligations. Use `mul_ne_zero hb₀ (Finset.prod_ne_zero_iff.mpr fun P _ => ?_)` and prove the remaining obligations. Establish `h : Ideal.absNorm P.asIdeal ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot`. Conclude with `h` after adjusting the coercions.

Introduce `P hP`. Rewrite using `[map_mul, map_prod]`. Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun Q : HeightOneSpectrum (𝓞 F) => algebraMap (𝓞 L) (𝓞 F) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 L)) (Finsupp.mem_support_iff.mpr hP)`. Rewrite using `[hc]`.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Rewrite using `[map_natCast]`. Conclude with `Ideal.absNorm_mem P.asIdeal`.
-/
theorem UpperTheory.V.ZK.Cl.cSupp :
    UpperTheory.V.ZK.Cl.CSupp := by
  intro L F _ _ _ _ _ 𝔡 b₀ hb₀
  refine ⟨b₀ * ∏ P ∈ 𝔡.support, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L), ?_, dvd_mul_right _ _, ?_⟩
  · refine mul_ne_zero hb₀ (Finset.prod_ne_zero_iff.mpr fun P _ => ?_)
    have h : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
    exact_mod_cast h
  · intro P hP
    rw [map_mul, map_prod]
    apply Ideal.mul_mem_left
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
      (fun Q : HeightOneSpectrum (𝓞 F) =>
        algebraMap (𝓞 L) (𝓞 F) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 L))
      (Finsupp.mem_support_iff.mpr hP)
    rw [hc]
    apply Ideal.mul_mem_right
    rw [map_natCast]
    exact Ideal.absNorm_mem P.asIdeal
