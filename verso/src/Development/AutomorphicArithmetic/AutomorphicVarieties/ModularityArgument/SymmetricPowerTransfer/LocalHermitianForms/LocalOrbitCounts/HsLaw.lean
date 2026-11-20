import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RamUnit

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.hsLaw : UpperTheory.V.Z.Sym.Loc.HsLaw := by
  intro O K _ _ _ _ _ Δ L
  have h2 : (2 : K) ≠ 0 := L.two_ne
  haveI := L.frac
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    unfold hs
    by_cases h1 : ∃ a b : K, a ^ 2 - x * b ^ 2 = y
    · rw [if_pos h1, if_pos (nm_symm hx h2 h1 hy)]
    · have h1' : ¬ ∃ a b : K, a ^ 2 - y * b ^ 2 = x := fun h => h1 (nm_symm hy h2 h hx)
      rw [if_neg h1, if_neg h1']
  · rintro x y ⟨U, s, hs0, rfl⟩ ⟨V, t, -, rfl⟩
    obtain ⟨a, b, hab⟩ := L.nm_unit U V
    have hK := congrArg (algebraMap O K) hab
    simp only [map_sub, map_mul, map_pow] at hK
    unfold hs
    rw [if_pos]
    refine ⟨algebraMap O K a * t, algebraMap O K b * t / s, ?_⟩
    rw [← hK]
    field_simp
  · intro D hD hsq
    by_cases he : EvenVal O D
    · obtain ⟨U, s, hs0, rfl⟩ := he
      obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hUsq : ¬ IsSquare (algebraMap O K U) := by
        rintro ⟨r, hr⟩
        exact hsq ⟨r * s, by rw [hr]; ring⟩
      have hp0 : algebraMap O K p ≠ 0 := by
        intro h0
        apply hp.ne_zero
        apply IsFractionRing.injective O K
        rw [h0, map_zero]
      refine ⟨algebraMap O K p, hp0, ?_⟩
      unfold hs
      rw [if_neg]
      rintro ⟨a, b, hab⟩
      have e : a ^ 2 - algebraMap O K ↑U * (s * b) ^ 2 = algebraMap O K p := by
        rw [← hab]; ring
      apply L.not_even hp
      rw [← e]
      exact L.even_of_norm U hUsq (by rw [e]; exact hp0)
    · obtain ⟨ε, hε⟩ := ramUnit O K Δ L D hD he
      refine ⟨algebraMap O K ε, ?_, hε⟩
      intro h0
      rw [h0] at hε
      unfold hs at hε
      rw [if_pos ⟨0, 0, by ring⟩] at hε
      norm_num at hε
  · rintro D x hD ⟨r, rfl⟩
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hD
    unfold hs
    rw [if_pos]
    refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
    field_simp
    ring
