import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsCen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Establish `hb` using `v.ne_bot`. Establish `hPb : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot hb P`. Establish `hqb : P.under (𝓞 L) ≠ ⊥` using `Ideal.under_ne_bot _ hPb`. Establish `: IsGaloisGroup L.fixingSubgroup L E` using `.of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ ↦ rfl`. Establish `: IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E)` using `IsGaloisGroup.of_isFractionRing _ _ _ L E`.

Use `v.isMaximal` as an intermediate fact. Establish `: (P.under (𝓞 L)).IsMaximal` using `Ideal.IsPrime.isMaximal inferInstance hqb`. Establish `: Finite (𝓞 K ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hb`. Establish `: Finite (𝓞 L ⧸ P.under (𝓞 L))` using `Ideal.finiteQuotientOfFreeOfNeBot _ hqb`. Establish `h1` using `Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P`.

Establish `h2` using `Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P`. Rewrite `h1` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)]`. Rewrite `h2` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup]`. Establish `h3` using `Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P`. Establish `h4 : Nat.card (P.inertia L.fixingSubgroup) = Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup)`.

Rewrite using `[← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]`. Rewrite `h3` using `[← h1, ← h2, h4]`. Establish `hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup)` using `Nat.card_pos`. Rewrite `h3`, `hpos` using `[inf_eq_left.mpr h]`. Conclude with `Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)`.
-/
private theorem ram_one {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal]
    (L : IntermediateField K E) (h : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup) :
    (P.under (𝓞 L)).ramificationIdx (𝓞 K) = 1 := by
  have hb := v.ne_bot
  have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
  have hqb : P.under (𝓞 L) ≠ ⊥ := Ideal.under_ne_bot _ hPb
  have : IsGaloisGroup L.fixingSubgroup L E :=
    .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ ↦ rfl
  have : IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ L E
  have := v.isMaximal
  have : (P.under (𝓞 L)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  have : Finite (𝓞 L ⧸ P.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P
  have h4 : Nat.card (P.inertia L.fixingSubgroup) =
      Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := by
    rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
  rw [← h1, ← h2, h4] at h3
  have hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := Nat.card_pos
  rw [inf_eq_left.mpr h] at h3 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)

/- English proof (translation)
Set `w : HeightOneSpectrum (𝓞 L)` to `⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩`. Establish `: w.asIdeal.LiesOver v.asIdeal` using `(inferInstance : Q.LiesOver v.asIdeal)`. Establish `h1` using `HeightOneSpectrum.valuation_liesOver L v w (a : K)`. Rewrite `h1` using `[show v.asIdeal.ramificationIdx' w.asIdeal = 1 from (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot).trans h, pow_one, ← hb, map_pow, ← HeightOneSpectrum.valuationOfNeZero_eq]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Rewrite `h1` using `[pow_zero, ← WithZero.coe_one, WithZero.coe_inj]`. Simplify using `[ordv, h1]`. Establish `h0 : w.valuation L b ≠ 0` using `fun e => by`. Rewrite `h1` using `[e, zero_pow hn.ne']`. Conclude with `WithZero.coe_ne_zero h1`.

Take `⟨m, hm⟩` from `WithZero.ne_zero_iff_exists.1 h0`. Rewrite `h1` using `[← hm, ← WithZero.coe_pow, WithZero.coe_inj]`. Rewrite using `[ordv, h1, toAdd_pow, dvd_neg, nsmul_eq_mul]`. Conclude with `dvd_mul_right _ _`.
-/
private theorem dvd_of_ram {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (h : Q.ramificationIdx (𝓞 K) = 1) (n : ℕ) (b : L) (a : Kˣ) (hb : b ^ n = algebraMap K L a) :
    (n : ℤ) ∣ ordv v a := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have h1 := HeightOneSpectrum.valuation_liesOver L v w (a : K)
  rw [show v.asIdeal.ramificationIdx' w.asIdeal = 1 from
    (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot).trans h, pow_one, ← hb, map_pow,
    ← HeightOneSpectrum.valuationOfNeZero_eq] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at h1
    simp [ordv, h1]
  · have h0 : w.valuation L b ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at h1
      exact WithZero.coe_ne_zero h1
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at h1
    rw [ordv, h1, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

/- English proof (translation)
Set `L : IntermediateField K E` to `IntermediateField.fixedField (P.inertia (E ≃ₐ[K] E))`. Establish `hle : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup` using `(IntermediateField.le_iff_le _ _).1 le_rfl`. Establish `hbL : b ∈ L` using `(IntermediateField.mem_fixedField_iff _ _).2 h`. Establish `: (P.under (𝓞 L)).LiesOver v.asIdeal` using `⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩`. Conclude with `dvd_of_ram v (P.under (𝓞 L)) (ram_one v P L hle) n ⟨b, hbL⟩ a (Subtype.ext hb)`.
-/
private theorem dvd_fin {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver v.asIdeal] (n : ℕ) (b : E) (a : Kˣ)
    (hb : b ^ n = algebraMap K E a) (h : ∀ τ ∈ P.inertia (E ≃ₐ[K] E), τ b = b) : (n : ℤ) ∣ ordv v a := by
  let L : IntermediateField K E := IntermediateField.fixedField (P.inertia (E ≃ₐ[K] E))
  have hle : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hbL : b ∈ L := (IntermediateField.mem_fixedField_iff _ _).2 h
  have : (P.under (𝓞 L)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  exact dvd_of_ram v (P.under (𝓞 L)) (ram_one v P L hle) n ⟨b, hbL⟩ a (Subtype.ext hb)

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ n A v β a hA hβ hI`. Establish `: IsGalois K Ω` using `IsAlgClosure.isGalois K Ω`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap K Ω).injective`. Set `L : IntermediateField K Ω` to `(FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField`. Establish `hβL : β ∈ L` using `FiniteGaloisIntermediateField.subset_adjoin K _ rfl`.

Establish `: NumberField L` using `NumberField.of_module_finite K _`. Establish `hv : (CompanionTheory.PlaceDict.cen A).under (𝓞 K) = v.asIdeal` using `Ideal.ext fun x => hA x`. Establish `: Algebra.IsIntegral (𝓞 K) (𝓞 Ω)` using `⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩`. Establish `hm : (CompanionTheory.PlaceDict.cen A).IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) _ (by`. Use `v.isMaximal` as an intermediate fact.

Rewrite using `[← hv] at this)` and apply the resulting hypothesis. Set `P : Ideal (𝓞 L)` to `(CompanionTheory.PlaceDict.cen A).under (𝓞 L)`. Establish `: P.LiesOver v.asIdeal` using `⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩`. Use `dvd_fin v P n ⟨β, hβL⟩ a (Subtype.ext hβ) fun τ hτ => ?_` and prove the remaining obligations. Take `⟨φ, h1, h2⟩` from `CompanionTheory.PlaceDict.lift L (CompanionTheory.PlaceDict.cen A) τ (RingHom.id _) fun x => by`.

Rewrite using `[RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]`. Conclude with `hτ x`. Take `⟨h3, h4⟩` from `CompanionTheory.PlaceDict.of_cong A φ one_ne_zero fun b => by`. Rewrite using `[pow_one]`. Conclude with `Ideal.Quotient.eq.1 (h2 b)`.

Establish `h5 : φ ∈ Ine (F` using `K) A := ⟨h3, fun x hx => by`. Simplify using `using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩`. Rewrite using `[← h1]`. Conclude with `Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))`.
-/
theorem UpperTheory.V.Kum.dvdOfIne :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω) (a : Kˣ), IsPlaceOver A v → β ^ n = algebraMap K Ω a → (∀ g ∈ Ine (F := K) A, g β = β) → (n : ℤ) ∣ ordv v a := by
  intro K Ω _ _ _ _ _ n A v β a hA hβ hI
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  have : NumberField L := NumberField.of_module_finite K _
  have hv : (CompanionTheory.PlaceDict.cen A).under (𝓞 K) = v.asIdeal := Ideal.ext fun x => hA x
  have : Algebra.IsIntegral (𝓞 K) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  have hm : (CompanionTheory.PlaceDict.cen A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) _ (by
      have := v.isMaximal
      rwa [← hv] at this)
  let P : Ideal (𝓞 L) := (CompanionTheory.PlaceDict.cen A).under (𝓞 L)
  have : P.LiesOver v.asIdeal := ⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩
  refine dvd_fin v P n ⟨β, hβL⟩ a (Subtype.ext hβ) fun τ hτ => ?_
  obtain ⟨φ, h1, h2⟩ := CompanionTheory.PlaceDict.lift L (CompanionTheory.PlaceDict.cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap]
    exact hτ x
  obtain ⟨h3, h4⟩ := CompanionTheory.PlaceDict.of_cong A φ one_ne_zero fun b => by
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h2 b)
  have h5 : φ ∈ Ine (F := K) A := ⟨h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩
  rw [← h1]
  exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))
