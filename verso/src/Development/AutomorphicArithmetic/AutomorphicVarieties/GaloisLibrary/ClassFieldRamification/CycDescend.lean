import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnitsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneFixQ

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `a b _ C _ _ _ ζ F hab hζ hunr`. Establish `hb0 : b ≠ 0` using `right_ne_zero_of_mul (NeZero.ne (a * b))`. Use `haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {a * b} ℚ C`. Use `set χ := IsCyclotomicExtension.Rat.galEquivZMod (a * b) C with hχ`. Establish `hcomm : ∀ σ τ : Gal(C/ℚ), τ * σ * τ⁻¹ = σ`.

Introduce `σ τ`. Apply `χ.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_inv, mul_comm (χ τ), mul_assoc, mul_inv_cancel, mul_one]`. Use `haveI : F.fixingSubgroup.Normal := ⟨fun σ hσ τ => by rw [hcomm]; exact hσ⟩`. Establish `hFF : fixedField F.fixingSubgroup = F` using `IsGalois.fixedField_fixingSubgroup F`.

Use `haveI hgF : IsGalois ℚ F := by`. Establish `h` using `IsGalois.of_fixedField_normal_subgroup F.fixingSubgroup`. Rewrite `h` using `[hFF]`. Use `h` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`.

Establish `hin : ∀ p : ℕ, p.Prime → p ∣ b → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal → w.asIdeal.inertia Gal(C/ℚ) ≤ F.fixingSubgroup`. Introduce `p hp hpb w hw σ hσ`. Establish `hk` using `(UpperTheory.V.CF.ineFixQ F C p hp).mp (hunr p hp hpb) w hw hσ`. Rewrite `hk` using `[MonoidHom.mem_ker]`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Establish `hc` using `UpperTheory.V.CF.resTo_commutes ℚ F C σ ⟨x, hx⟩`. Rewrite `hc` using `[hk, AlgEquiv.one_apply]`. Conclude with `hc.symm`. Establish `hsup : ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p ≤ F.fixingSubgroup.map χ.toMonoidHom`.

Use `iSup₂_le fun p hp => ?_` and prove the remaining obligations. Establish `hpp : p.Prime` using `Nat.prime_of_mem_primeFactors hp`. Establish `hpb : p ∣ b` using `Nat.dvd_of_mem_primeFactors hp`. Use `haveI : Fact p.Prime := ⟨hpp⟩`. Use `haveI : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible`.

Take `⟨P, hPm, hPl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 C) (Ideal.span {(p : ℤ)})`. Use `haveI := hPm`. Use `haveI := hPl`. Establish `hpP : (p : 𝓞 C) ∈ P`. Establish `h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)}` using `Ideal.mem_span_singleton_self _`.

Rewrite `h1` using `[Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.under_def, Ideal.mem_comap]`. Simplify using `using h1`. Set `w : HeightOneSpectrum (𝓞 C)` to `⟨P, hPm.isPrime, fun h => by`. Rewrite `hpP` using `[h, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.mpr hpp.ne_zero) hpP⟩`.

Rewrite using `[← KStar.Ram.map_inertia_eq p P]`. Conclude with `Subgroup.map_mono (hin p hpp hpb w hpP)`. Rewrite using `[← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ ^ b⟯, IntermediateField.le_iff_le]`. Introduce `σ hσ`. Establish `hfix : σ (ζ ^ b) = ζ ^ b` using `(IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _ (IntermediateField.mem_adjoin_simple_self ℚ _)`.

Establish `hker : χ σ ∈ (ZMod.unitsMap (Dvd.intro b rfl : a ∣ a * b)).ker`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]`. Rewrite `hfix` using `[map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (a * b) C σ hζ.pow_eq_one, ← pow_mul]`. Establish `hmod : (χ σ).val.val * b ≡ 1 * b [MOD a * b]`. Rewrite using `[one_mul]`.

Establish `h2` using `(hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod.mp hfix`. Rewrite `h2` using `[← hζ.eq_orderOf]`. Conclude with `h2`. Establish `hk` using `Nat.ModEq.mul_right_cancel' hb0 hmod`. Rewrite using `[← Nat.cast_one]`.

Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).mpr hk`. Establish `hmem` using `hsup (UpperTheory.V.CF.unitsGen a b hab hker)`. Rewrite `hmem` using `[Subgroup.mem_map]`. Take `⟨τ, hτ, hτσ⟩` from `hmem`. Establish `hτσ' : τ = σ` using `χ.injective hτσ`.

Rewrite `hτ` using `[hτσ']`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.CF.cycDescend :
    ∀ (a b : ℕ) [NeZero (a * b)] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {a * b} ℚ C] (ζ : C) (F : IntermediateField ℚ C), a.Coprime b → IsPrimitiveRoot ζ (a * b) → (∀ p : ℕ, p.Prime → p ∣ b → UnramAt F p) → F ≤ ℚ⟮ζ ^ b⟯ := by
  intro a b _ C _ _ _ ζ F hab hζ hunr
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (NeZero.ne (a * b))
  haveI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {a * b} ℚ C
  set χ := IsCyclotomicExtension.Rat.galEquivZMod (a * b) C with hχ
  have hcomm : ∀ σ τ : Gal(C/ℚ), τ * σ * τ⁻¹ = σ := by
    intro σ τ
    apply χ.injective
    rw [map_mul, map_mul, map_inv, mul_comm (χ τ), mul_assoc, mul_inv_cancel, mul_one]
  haveI : F.fixingSubgroup.Normal := ⟨fun σ hσ τ => by rw [hcomm]; exact hσ⟩
  have hFF : fixedField F.fixingSubgroup = F := IsGalois.fixedField_fixingSubgroup F
  haveI hgF : IsGalois ℚ F := by
    have h := IsGalois.of_fixedField_normal_subgroup F.fixingSubgroup
    rw [hFF] at h
    convert h
    exact Subsingleton.elim _ _
  have hin : ∀ p : ℕ, p.Prime → p ∣ b → ∀ w : HeightOneSpectrum (𝓞 C), (p : 𝓞 C) ∈ w.asIdeal →
      w.asIdeal.inertia Gal(C/ℚ) ≤ F.fixingSubgroup := by
    intro p hp hpb w hw σ hσ
    have hk := (UpperTheory.V.CF.ineFixQ F C p hp).mp (hunr p hp hpb) w hw hσ
    rw [MonoidHom.mem_ker] at hk
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hc := UpperTheory.V.CF.resTo_commutes ℚ F C σ ⟨x, hx⟩
    rw [hk, AlgEquiv.one_apply] at hc
    exact hc.symm
  have hsup : ⨆ p ∈ b.primeFactors, KStar.Ram.inertiaUnits (a * b) p ≤
      F.fixingSubgroup.map χ.toMonoidHom := by
    refine iSup₂_le fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
    obtain ⟨P, hPm, hPl⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 C) (Ideal.span {(p : ℤ)})
    haveI := hPm
    haveI := hPl
    have hpP : (p : 𝓞 C) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
      rw [Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.under_def,
        Ideal.mem_comap] at h1
      simpa using h1
    let w : HeightOneSpectrum (𝓞 C) := ⟨P, hPm.isPrime, fun h => by
      rw [h, Ideal.mem_bot] at hpP
      exact (Nat.cast_ne_zero.mpr hpp.ne_zero) hpP⟩
    rw [← KStar.Ram.map_inertia_eq p P]
    exact Subgroup.map_mono (hin p hpp hpb w hpP)
  rw [← IsGalois.fixedField_fixingSubgroup ℚ⟮ζ ^ b⟯, IntermediateField.le_iff_le]
  intro σ hσ
  have hfix : σ (ζ ^ b) = ζ ^ b := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hker : χ σ ∈ (ZMod.unitsMap (Dvd.intro b rfl : a ∣ a * b)).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ZMod.cast_eq_val, Units.val_one]
    rw [map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (a * b) C σ hζ.pow_eq_one,
      ← pow_mul] at hfix
    have hmod : (χ σ).val.val * b ≡ 1 * b [MOD a * b] := by
      rw [one_mul]
      have h2 := (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod.mp hfix
      rw [← hζ.eq_orderOf] at h2
      exact h2
    have hk := Nat.ModEq.mul_right_cancel' hb0 hmod
    rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk
  have hmem := hsup (UpperTheory.V.CF.unitsGen a b hab hker)
  rw [Subgroup.mem_map] at hmem
  obtain ⟨τ, hτ, hτσ⟩ := hmem
  have hτσ' : τ = σ := χ.injective hτσ
  rwa [hτσ'] at hτ
