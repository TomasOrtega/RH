import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsOfGOrbNe

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.gVanish : UpperTheory.V.Z.Sym.Loc.GVanish := by
  intro O K _ _ _ _ _ Δ τ hL j hj χ z hz hne
  haveI := hL.frac
  obtain ⟨s, u, t, hn, ht⟩ := exists_of_gOrb_ne (O := O) hj hne
  have hu : algebraMap O K ↑u⁻¹ * algebraMap O K ↑u = 1 := by
    rw [← map_mul]
    simp
  rcases hz with h | h
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have h2 : (s : K) ^ 2 = algebraMap O K ↑u⁻¹ := by
      calc (s : K) ^ 2 = algebraMap O K ↑u⁻¹ * (algebraMap O K ↑u * s ^ 2) := by
            rw [← mul_assoc, hu, one_mul]
        _ = _ := by rw [← hn, mul_one]
    have hi : IsIntegral O (s : K) :=
      IsIntegral.of_pow two_pos (h2 ▸ isIntegral_algebraMap)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨y * t, by rw [map_mul, hy, ht]⟩
  · rw [h] at hn ht
    simp [trace, QuadraticAlgebra.norm] at hn ht
    have e : algebraMap O K t = algebraMap O K ↑u * s := by
      apply mul_left_cancel₀ s.ne_zero
      linear_combination hn - ht
    have hs : (s : K) = algebraMap O K (↑u⁻¹ * t) := by
      rw [map_mul, e, ← mul_assoc, hu, one_mul]
    refine ⟨↑u⁻¹ * t * t - 2, ?_⟩
    rw [map_sub, map_mul, ← hs, map_ofNat]
    linear_combination -ht
