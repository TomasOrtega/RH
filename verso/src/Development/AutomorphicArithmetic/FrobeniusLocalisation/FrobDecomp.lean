import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.HF.frob_decomp :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P ↔ H.galE σ ∈ Subgroup.zpowers (H.frobG p)) ∧
      Nat.card (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P) = orderOf (H.frobG p) ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard * orderOf (H.frobG p) = 4 * φ.ord := by
  intro φ H p hpf hp P _ _
  have hpp : p.Prime := Fact.out
  have hco : Nat.Coprime p H.condN := hpp.coprime_iff_not_dvd.2 hp
  have hoc : ordCompl[p] H.condN = H.condN := by
    rw [Nat.factorization_eq_zero_of_not_dvd hp, pow_zero, Nat.div_one]
  have h1 : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P ↔
      H.galE σ ∈ Subgroup.zpowers (H.frobG p) := by
    intro σ
    rw [H.der.decomp p P σ, hoc, ← mem_powers_iff_mem_zpowers, H.frobG_of_coprime hco]
    constructor
    · rintro ⟨u, k, hu, hσ⟩
      refine ⟨k, ?_⟩
      have hu' : u = ZMod.unitOfCoprime p hco ^ k := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow,
          ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hu, ZMod.natCast_zmod_val]
      show H.art (ZMod.unitOfCoprime p hco) ^ k = H.gal σ
      rw [hσ, hu', map_pow]
    · rintro ⟨k, hk⟩
      refine ⟨ZMod.unitOfCoprime p hco ^ k, k, ?_, ?_⟩
      · rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
        exact Nat.mod_modEq _ _
      · rw [map_pow]
        exact hk.symm
  have h2 : Nat.card (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P) = orderOf (H.frobG p) := by
    rw [← Nat.card_zpowers]
    exact Nat.card_congr (H.gal.toEquiv.subtypeEquiv h1)
  refine ⟨h1, h2, ?_⟩
  have := H.galois
  have horb : MulAction.orbit (H.E ≃ₐ[ℚ] H.E) P = primesOver (span {(p : ℤ)}) (𝓞 H.E) := by
    ext Q
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨inferInstanceAs (g • P).IsPrime, inferInstanceAs ((g • P).LiesOver _)⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) P Q (H.E ≃ₐ[ℚ] H.E)
  rw [← horb, ← h2, ← MulAction.index_stabilizer, Subgroup.index_mul_card, ← φ.natCard_GG]
  exact Nat.card_congr H.gal.toEquiv
