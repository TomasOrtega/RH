import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

/- English proof (translation)
Introduce `R _ _ _ J b hb`. Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (maximalIdeal R) (IsLocalRing.maximalIdeal.isMaximal R).ne_top`. Establish `hx : Ideal.Quotient.mk J b ∈ (⨅ i : ℕ, (maximalIdeal R) ^ i • ⊤ : Submodule R (R ⧸ J))`. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`.

Break down `i with _ | N` into its components or cases. Simplify using the standard rewrite rules. Take `⟨j, hj, y, hy, rfl⟩` from `Submodule.mem_sup.mp (hb N)`. Establish `he : Ideal.Quotient.mk J (j + y) = y • (Ideal.Quotient.mk J 1 : R ⧸ J)`. Rewrite using `[map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one, mul_one]`.

Rewrite using `[he]`. Conclude with `Submodule.smul_mem_smul hy Submodule.mem_top`. Rewrite `hx` using `[hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hx`.
-/
theorem UpperTheory.V.Ws.H5.closedJ :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (b : R), (∀ N : ℕ, b ∈ J ⊔ maximalIdeal R ^ (N + 1)) → b ∈ J := by
  intro R _ _ _ J b hb
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hx : Ideal.Quotient.mk J b ∈ (⨅ i : ℕ, (maximalIdeal R) ^ i • ⊤ : Submodule R (R ⧸ J)) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | N
    · simp
    · obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.mp (hb N)
      have he : Ideal.Quotient.mk J (j + y) = y • (Ideal.Quotient.mk J 1 : R ⧸ J) := by
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq, map_one, mul_one]
      rw [he]
      exact Submodule.smul_mem_smul hy Submodule.mem_top
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx
