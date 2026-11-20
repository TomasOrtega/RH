import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField

noncomputable section

namespace GlobalTheory.ResidueFieldAlgClosed

open Polynomial

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAlgClosed_residueField {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hdeg : (P.map (algebraMap A Ω)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, hPdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral A α := ⟨P, hPmon, by rw [← Polynomial.eval_map]; exact hα⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h0 : P.eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
    exact hα
  refine ⟨IsLocalRing.residue A a, ?_⟩
  rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAlgebraic_residueField {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω)
    (hΩ : ∀ y : Ω, IsAlgebraic ℤ y) (g : ℕ) [Fact g.Prime] [Algebra (ZMod g) (IsLocalRing.ResidueField A)] :
    Algebra.IsAlgebraic (ZMod g) (IsLocalRing.ResidueField A) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨p, hp0, hpa⟩ := hΩ (a : Ω)
  have hc : (p.content : Ω) ≠ 0 := Int.cast_ne_zero.mpr (mt Polynomial.content_eq_zero_iff.mp hp0)
  have hqa : Polynomial.aeval (a : Ω) p.primPart = 0 := by
    rw [Polynomial.eq_C_content_mul_primPart p, map_mul, Polynomial.aeval_C] at hpa
    exact (mul_eq_zero.mp hpa).resolve_left (by simpa using hc)
  have hA0 : Polynomial.aeval a p.primPart = 0 := by
    apply IsFractionRing.injective A Ω
    rw [map_zero]
    calc algebraMap A Ω (Polynomial.aeval a p.primPart)
        = Polynomial.aeval (algebraMap A Ω a) p.primPart :=
          (Polynomial.aeval_algHom_apply (algebraMap A Ω).toIntAlgHom a p.primPart).symm
      _ = 0 := hqa
  have hqg : p.primPart.map (Int.castRingHom (ZMod g)) ≠ 0 := by
    intro h
    have hdvd : Polynomial.C (g : ℤ) ∣ p.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi := congrArg (fun r => Polynomial.coeff r i) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).mp hi
    have hu := Polynomial.isPrimitive_primPart p _ hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := (Fact.out : g.Prime).two_le
    omega
  refine ⟨p.primPart.map (Int.castRingHom (ZMod g)), hqg, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a p.primPart
  rw [hA0, map_zero] at h2
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [Polynomial.aeval_def] at h2
  have hφ : (algebraMap (ZMod g) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod g)) =
      algebraMap ℤ (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
  rw [hφ]
  exact h2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem residueField_equiv (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (g : ℕ) [Fact (Nat.Prime g)]
    (hg : (g : NumberField.RingOfIntegers E) ∈ v.asIdeal) :
    Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have hΩ : ∀ y : Ω, IsAlgebraic ℤ y := fun y =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  have hg0 : (g : IsLocalRing.ResidueField A) = 0 := by
    have h1 := (hA (g : NumberField.RingOfIntegers E)).mpr hg
    have h2 : A.valuation ((g : A) : Ω) < 1 := by simpa using h1
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff (g : A)).mpr h2
  have : CharP (IsLocalRing.ResidueField A) g := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hg0
  let _ : Algebra (ZMod g) (IsLocalRing.ResidueField A) := ZMod.algebra _ g
  have _ := isAlgClosed_residueField A
  have _ := isAlgebraic_residueField A hΩ g
  have : IsAlgClosure (ZMod g) (IsLocalRing.ResidueField A) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod g) (IsLocalRing.ResidueField A) (Formalism.CyclotomicNorms.Fbar g)).toRingEquiv⟩

end GlobalTheory.ResidueFieldAlgClosed

end
