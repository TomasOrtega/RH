import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LeftMulMatrixEmbeddingDetEqNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vcount

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
private theorem vcount_one_add {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (x : Etau K τ) :
    vcount O τ (1 + x) = vcount O τ x := by
  have key : ∀ X, (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (1 + x) * y ∈ S) ∧ X = cls τ S) ↔
      (∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S) := by
    intro X
    apply exists_congr
    intro S
    constructor
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      have h2 := (Submodule.span O (s : Set (Etau K τ))).sub_mem h1 hy
      simpa [add_mul] using h2
    · rintro ⟨hL, hst, hX⟩
      refine ⟨hL, ?_, hX⟩
      obtain ⟨s, rfl⟩ := hL.fg
      intro y hy
      have h1 := hst y hy
      rw [SetLike.mem_coe] at h1 hy ⊢
      rw [add_mul, one_mul]
      exact (Submodule.span O (s : Set (Etau K τ))).add_mem hy h1
  unfold vcount
  congr 1
  funext X
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ((key X).1 h1) h2
  · exact absurd ((key X).2 h2) h1
  · rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Supply the required witnesses or components. Supply the required witnesses or components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.Loc.gVals : UpperTheory.V.Z.Sym.Loc.GVals := by
  intro O K _ _ _ _ _ Δ τ L hτ hτO j χ hj hχ a ha z hz
  obtain ⟨o, ho⟩ := hτO
  have hna : QuadraticAlgebra.norm (a : Etau K τ) = 1 := by
    rw [ha]
    simp [QuadraticAlgebra.norm]
  have hnz : QuadraticAlgebra.norm (z : Etau K τ) = 2 + τ := by
    rw [hz]
    simp [QuadraticAlgebra.norm]
    ring
  have gA : gOrb O j χ a = vcount O τ a := by
    have h1 := gLat O K Δ τ L hτ j χ hj hχ a 1 1 (by rw [hna]; simp)
    simpa using h1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hu⟩
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z 1 u (by rw [hnz, hu]; simp)
    simp only [map_one, Units.val_one, inv_one, one_mul, one_smul] at gZ
    rw [gA, gZ, hz, ← ha, vcount_one_add]
  · rintro ⟨u, hu⟩
    rw [gA, ha]
    apply vMax O K Δ τ L hτ
    · exact ⟨o, by rw [ho]; simp [trace]⟩
    · exact ⟨1, by simp [QuadraticAlgebra.norm]⟩
    · exact ⟨u, by rw [hu]; simp⟩
  · rintro ⟨u, hu⟩ s ε hs
    have gZ := gLat O K Δ τ L hτ j χ hj hχ z s ε (by rw [hnz, hs])
    haveI := L.frac
    have hsO : ∃ c : O, algebraMap O K c = (s : K) := by
      have hint : IsIntegral O ((s : K) ^ 2) := by
        have : (s : K) ^ 2 = algebraMap O K (((ε⁻¹ : Oˣ) : O) * (2 + o)) := by
          have hinv : algebraMap O K ((ε⁻¹ : Oˣ) : O) * algebraMap O K (ε : O) = 1 := by
            rw [← map_mul, Units.inv_mul, map_one]
          rw [map_mul, map_add, map_ofNat, ho]
          linear_combination (-(algebraMap O K ((ε⁻¹ : Oˣ) : O))) * hs - (s : K) ^ 2 * hinv
        rw [this]
        exact isIntegral_algebraMap
      exact IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_pow two_pos hint)
    obtain ⟨c, hc⟩ := hsO
    have hs0 := s.ne_zero
    have hv : vcount O τ (((s⁻¹ : Kˣ) : K) • (z : Etau K τ)) = 1 := by
      apply vMax O K Δ τ L hτ
      · refine ⟨ε * c, ?_⟩
        rw [hz]
        simp [trace]
        rw [hc]
        field_simp
        linear_combination -hs
      · refine ⟨ε, ?_⟩
        rw [hz]
        simp [QuadraticAlgebra.norm]
        field_simp
        linear_combination -hs
      · refine ⟨-(ε * u), ?_⟩
        rw [hz]
        simp
        rw [hu]
        field_simp
        linear_combination (2 - τ) * hs
    rw [gZ, hv, mul_one]
