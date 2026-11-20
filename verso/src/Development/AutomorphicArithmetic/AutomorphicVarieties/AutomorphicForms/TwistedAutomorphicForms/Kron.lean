import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField IsDedekindDomain in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Tw.kron :
    UpperTheory.V.Af.Tw.Kron := by
  intro K _ _
  refine ⟨NumberField.Units.torsionOrder K, ?_, ?_⟩
  · intro l hl hno
    haveI : Fact (Nat.Prime l) := ⟨hl⟩
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := NumberField.Units.torsion K) l hdvd
    have h1 : IsPrimitiveRoot (g : (𝓞 K)ˣ) l := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact IsPrimitiveRoot.orderOf _
    have h2 : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) l := IsPrimitiveRoot.coe_units_iff.mpr h1
    have h3 := h2.map_of_injective (f := algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)
    exact hno ⟨_, h3⟩
  · intro y hy hnorm
    have hy' : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((Neutral.B1.diagUnits K y : Neutral.B1.Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (y : K) (fun v => by
      rw [← GlobalTheory.UpIdeleMod.valued_algebraMap (R := 𝓞 K) v]
      exact le_of_eq (hy' v))
    have hI : IsIntegral ℤ (y : K) := by
      have := NumberField.RingOfIntegers.isIntegral_coe r
      rwa [hr] at this
    obtain ⟨m, hm, hym⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hI hnorm
    have hrm : r ^ m = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_pow, hr, hym, map_one]
    let u : (𝓞 K)ˣ := Units.ofPowEqOne r m hrm hm.ne'
    have hu : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨m, hm, Units.ext (by simp [u, hrm])⟩
    rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hu
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hr, ← map_pow]
    have hu' := congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K))) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hu'
    change (u : 𝓞 K) ^ NumberField.Units.torsionOrder K = 1 at hu'
    have hur : (u : 𝓞 K) = r := Units.val_ofPowEqOne r m hrm hm.ne'
    rw [hur] at hu'
    rw [hu', map_one]
