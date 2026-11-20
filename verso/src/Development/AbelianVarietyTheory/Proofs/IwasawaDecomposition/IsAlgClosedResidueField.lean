import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField

noncomputable section

namespace GlobalTheory.ResidueFieldAlgClosed

open Polynomial

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_` and prove the remaining obligations. Establish `hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A)` using `Polynomial.map_surjective _ IsLocalRing.residue_surjective p`. Take `⟨P, hPmap, hPdeg, hPmon⟩` from `Polynomial.lifts_and_degree_eq_and_monic hlift hmon`. Establish `hinj : Function.Injective (algebraMap A Ω)` using `IsFractionRing.injective A Ω`. Establish `hdeg : (P.map (algebraMap A Ω)).degree ≠ 0`.

Rewrite using `[Polynomial.degree_map_eq_of_injective hinj, hPdeg]`. Conclude with `(Polynomial.degree_pos_of_irreducible hirr).ne'`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root _ hdeg`. Establish `hint : IsIntegral A α` using `⟨P, hPmon, by rw [← Polynomial.eval_map]; exact hα⟩`. Take `⟨a, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Establish `h0 : P.eval a = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]`. Conclude with `hα`. Use `⟨IsLocalRing.residue A a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]`.
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
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective x`. Take `⟨p, hp0, hpa⟩` from `hΩ (a : Ω)`. Establish `hc : (p.content : Ω) ≠ 0` using `Int.cast_ne_zero.mpr (mt Polynomial.content_eq_zero_iff.mp hp0)`. Establish `hqa : Polynomial.aeval (a : Ω) p.primPart = 0`.

Rewrite `hpa` using `[Polynomial.eq_C_content_mul_primPart p, map_mul, Polynomial.aeval_C]`. Conclude with `(mul_eq_zero.mp hpa).resolve_left (by simpa using hc)`. Establish `hA0 : Polynomial.aeval a p.primPart = 0`. Apply `IsFractionRing.injective A Ω` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hqg : p.primPart.map (Int.castRingHom (ZMod g)) ≠ 0`. Introduce `h`. Establish `hdvd : Polynomial.C (g : ℤ) ∣ p.primPart`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`.

Introduce `i`. Establish `hi` using `congrArg (fun r => Polynomial.coeff r i) h`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at hi`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ g).mp hi`. Establish `hu` using `Polynomial.isPrimitive_primPart p _ hdvd`.

Rewrite `hu` using `[Int.isUnit_iff]`. Establish `h2` using `(Fact.out : g.Prime).two_le`. Use linear arithmetic over natural numbers and integers. Use `⟨p.primPart.map (Int.castRingHom (ZMod g)), hqg, ?_⟩` and prove the remaining obligations. Establish `h2` using `Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a p.primPart`.

Rewrite `h2` using `[hA0, map_zero]`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Rewrite `h2` using `[Polynomial.aeval_def]`. Establish `hφ : (algebraMap (ZMod g) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod g)) = algebraMap ℤ (IsLocalRing.ResidueField A)` using `RingHom.ext_int _ _`. Rewrite using `[hφ]`.

Conclude with `h2`.
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
Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`. Establish `: Algebra.IsAlgebraic E Ω` using `IsAlgClosure.isAlgebraic`. Establish `: Algebra.IsAlgebraic ℚ Ω` using `Algebra.IsAlgebraic.trans ℚ E Ω`. Establish `hΩ : ∀ y : Ω, IsAlgebraic ℤ y` using `fun y => (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr (Algebra.IsAlgebraic.isAlgebraic y)`.

Establish `hg0 : (g : IsLocalRing.ResidueField A) = 0`. Establish `h1` using `(hA (g : NumberField.RingOfIntegers E)).mpr hg`. Establish `h2 : A.valuation ((g : A) : Ω) < 1` using `by simpa using h1`. Rewrite using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]`. Conclude with `(A.valuation_lt_one_iff (g : A)).mpr h2`.

Establish `: CharP (IsLocalRing.ResidueField A) g` using `(CharP.charP_iff_prime_eq_zero Fact.out).mpr hg0`. Set `_ : Algebra (ZMod g) (IsLocalRing.ResidueField A)` to `ZMod.algebra _ g`. Establish `_` using `isAlgClosed_residueField A`. Establish `_` using `isAlgebraic_residueField A hΩ g`. Establish `: IsAlgClosure (ZMod g) (IsLocalRing.ResidueField A)` using `⟨inferInstance, inferInstance⟩`.

Conclude with `⟨(IsAlgClosure.equiv (ZMod g) (IsLocalRing.ResidueField A) (Formalism.CyclotomicNorms.Fbar g)).toRingEquiv⟩`.
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
