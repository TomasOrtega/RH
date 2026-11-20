import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

/- English proof (translation)
Establish `hroot` using `hz.isRoot_cyclotomic hM`. Establish `hfac` using `(Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot`. Establish `h1` using `congrArg (Polynomial.eval 1) hfac`. Rewrite `h1` using `[Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one_cyclotomic_not_prime_pow h]`. Conclude with `IsUnit.of_mul_eq_one _ h1`.
-/
private theorem isUnit_one_sub {R : Type} [CommRing R] [IsDomain R] {M : ℕ} (hM : 0 < M) {z : R}
    (hz : IsPrimitiveRoot z M) (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ M) : IsUnit (1 - z) := by
  have hroot := hz.isRoot_cyclotomic hM
  have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
  have h1 := congrArg (Polynomial.eval 1) hfac
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one_cyclotomic_not_prime_pow h] at h1
  exact IsUnit.of_mul_eq_one _ h1

/- English proof (translation)
Establish `hM : 0 < M` using `NeZero.pos M`. Take `⟨k, hk⟩` from `h4`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec M ℚ L`. Use `set ζ := IsCyclotomicExtension.zeta M ℚ L`. Establish `hη` using `hζ.toInteger_isPrimitiveRoot`.

Establish `hu : IsUnit (1 - hζ.toInteger)` using `isUnit_one_sub hM hη h`. Establish `hm1 : ζ ^ (2 * k) = -1`. Establish `hsq : ζ ^ (2 * k) * ζ ^ (2 * k) = 1`. Rewrite using `[← pow_add, show 2 * k + 2 * k = M by omega]`. Conclude with `hζ.pow_eq_one`.

Establish `hne : ζ ^ (2 * k) ≠ 1` using `hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)`. Conclude with `(mul_self_eq_one_iff.mp hsq).resolve_left hne`. Establish `hneg : IsPrimitiveRoot (-ζ) M`. Establish `hpow : -ζ = ζ ^ (2 * k + 1)`. Rewrite using `[pow_succ, hm1, neg_one_mul]`.

Rewrite using `[hpow]`. Apply `hζ.pow_of_coprime` to reduce the goal to its premises. Rewrite using `[hk, Nat.coprime_comm, show 4 * k = 2 * (2 * k) by ring]`. Use `Nat.Coprime.mul ?_ ?_` and prove the remaining obligations. Conclude with `Nat.coprime_two_left.mpr (odd_two_mul_add_one k)`.

Conclude with `Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)`. Establish `hζne : ζ ≠ 1` using `hζ.ne_one (by omega)`. Use `set g := IsCMField.unitsMulComplexConjInv L hu.unit with hgdef`. Establish `hg : algebraMap (𝓞 L) L ((g : (𝓞 L)ˣ) : 𝓞 L) = -ζ`. Establish `hc : IsCMField.complexConj L ζ = ζ⁻¹`.

Take `⟨φ⟩` from `(inferInstance : Nonempty (L →+* ℂ))`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Apply `φ.injective` to reduce the goal to its premises. Establish `hz : ‖φ ζ‖ = 1` using `(hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)`. Rewrite using `[map_mul, map_one, IsCMField.complexEmbedding_complexConj, Complex.conj_mul', hz]`.

Simplify using the standard rewrite rules. Rewrite using `[hgdef, IsCMField.unitsMulComplexConjInv_apply, Units.coe_mul, map_units_inv]`. Simplify using the standard rewrite rules. Establish `e1 : (algebraMap (𝓞 L) L) hζ.toInteger = ζ` using `rfl`. Establish `e2 : ((hζ.toInteger : 𝓞 L) : L) = ζ` using `rfl`.

Rewrite using `[e1, e2, hc]`. Establish `h0 : ζ ≠ 0` using `hζ.ne_zero (NeZero.ne M)`. Establish `h1 : ζ - 1 ≠ 0` using `sub_ne_zero.mpr hζne`. Establish `h2 : (1 : L) - ζ⁻¹ = (ζ - 1) / ζ`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h2, inv_div]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hgp : IsPrimitiveRoot g M`. Rewrite using `[← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff, ← IsPrimitiveRoot.map_iff_of_injective (f := algebraMap (𝓞 L) L) (FaithfulSMul.algebraMap_injective _ _), hg]`.

Conclude with `hneg`. Establish `htop : Subgroup.zpowers g = ⊤`. Apply `Subgroup.eq_top_of_card_eq` to reduce the goal to its premises. Rewrite using `[Nat.card_zpowers, ← hgp.eq_orderOf]`. Establish `ht` using `IsCyclotomicExtension.Rat.torsionOrder_eq (n := M) (K := L)`.

Rewrite `ht` using `[if_pos ⟨2 * k, by omega⟩]`. Conclude with `ht.symm`. Introduce `y`. Take `⟨j, hj⟩` from `Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top y)`. Conclude with `⟨hu.unit ^ j, by rw [map_zpow, hj]⟩`.
-/
private theorem exists_finset_adjoin_laurent_preimage (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {M} ℚ L] [IsCMField L] (h4 : 4 ∣ M)
    (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ M) :
    Function.Surjective (IsCMField.unitsMulComplexConjInv L) := by
  have hM : 0 < M := NeZero.pos M
  obtain ⟨k, hk⟩ := h4
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ L
  set ζ := IsCyclotomicExtension.zeta M ℚ L
  have hη := hζ.toInteger_isPrimitiveRoot
  have hu : IsUnit (1 - hζ.toInteger) := isUnit_one_sub hM hη h
  have hm1 : ζ ^ (2 * k) = -1 := by
    have hsq : ζ ^ (2 * k) * ζ ^ (2 * k) = 1 := by
      rw [← pow_add, show 2 * k + 2 * k = M by omega]
      exact hζ.pow_eq_one
    have hne : ζ ^ (2 * k) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    exact (mul_self_eq_one_iff.mp hsq).resolve_left hne
  have hneg : IsPrimitiveRoot (-ζ) M := by
    have hpow : -ζ = ζ ^ (2 * k + 1) := by
      rw [pow_succ, hm1, neg_one_mul]
    rw [hpow]
    apply hζ.pow_of_coprime
    rw [hk, Nat.coprime_comm, show 4 * k = 2 * (2 * k) by ring]
    refine Nat.Coprime.mul ?_ ?_
    · exact Nat.coprime_two_left.mpr (odd_two_mul_add_one k)
    · exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hζne : ζ ≠ 1 := hζ.ne_one (by omega)
  set g := IsCMField.unitsMulComplexConjInv L hu.unit with hgdef
  have hg : algebraMap (𝓞 L) L ((g : (𝓞 L)ˣ) : 𝓞 L) = -ζ := by
    have hc : IsCMField.complexConj L ζ = ζ⁻¹ := by
      obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
      refine eq_inv_of_mul_eq_one_left ?_
      apply φ.injective
      have hz : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)
      rw [map_mul, map_one, IsCMField.complexEmbedding_complexConj, Complex.conj_mul', hz]
      simp
    rw [hgdef, IsCMField.unitsMulComplexConjInv_apply, Units.coe_mul, map_units_inv]
    simp
    have e1 : (algebraMap (𝓞 L) L) hζ.toInteger = ζ := rfl
    have e2 : ((hζ.toInteger : 𝓞 L) : L) = ζ := rfl
    rw [e1, e2, hc]
    have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
    have h1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζne
    have h2 : (1 : L) - ζ⁻¹ = (ζ - 1) / ζ := by
      field_simp
    rw [h2, inv_div]
    field_simp
    ring
  have hgp : IsPrimitiveRoot g M := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff,
      ← IsPrimitiveRoot.map_iff_of_injective (f := algebraMap (𝓞 L) L)
        (FaithfulSMul.algebraMap_injective _ _), hg]
    exact hneg
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ← hgp.eq_orderOf]
    have ht := IsCyclotomicExtension.Rat.torsionOrder_eq (n := M) (K := L)
    rw [if_pos ⟨2 * k, by omega⟩] at ht
    exact ht.symm
  intro y
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top y)
  exact ⟨hu.unit ^ j, by rw [map_zpow, hj]⟩

/- English proof (translation)
Introduce `f n _ L _ _ _ _ hf hf1 hn`. Apply `exists_finset_adjoin_laurent_preimage (f * 2 ^ n) L` to reduce the goal to its premises. Establish `h4 : (4 : ℕ) = 2 ^ 2` using `by norm_num`. Rewrite using `[h4]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow 2 hn) f`.

Introduce `p hp k hk`. Establish `h2 : 2 ∣ p ^ k` using `hk ▸ Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) f`. Establish `hp2 : p = 2` using `((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm`. Substitute `hp2` using the available equality. Establish `hfd : f ∣ 2 ^ k` using `hk ▸ Dvd.intro _ rfl`.

Take `⟨i, -, rfl⟩` from `(Nat.dvd_prime_pow Nat.prime_two).mp hfd`. Break down `Nat.eq_zero_or_pos i with hi | hi` into its components or cases. Substitute `hi` using the available equality. Simplify using `at hf1`. Establish `hev : Even (2 ^ i)` using `(Nat.even_pow).mpr ⟨even_two, hi.ne'⟩`.

Conclude with `(Nat.not_even_iff_odd.mpr hf) hev`.
-/
theorem UpperTheory.V.FW.unitSurj :
    ∀ (f n : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L], Odd f → 1 < f → 2 ≤ n → Function.Surjective (IsCMField.unitsMulComplexConjInv L) := by
  intro f n _ L _ _ _ _ hf hf1 hn
  apply exists_finset_adjoin_laurent_preimage (f * 2 ^ n) L
  · have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hn) f
  · intro p hp k hk
    have h2 : 2 ∣ p ^ k := hk ▸ Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) f
    have hp2 : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    subst hp2
    have hfd : f ∣ 2 ^ k := hk ▸ Dvd.intro _ rfl
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hfd
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp at hf1
    · have hev : Even (2 ^ i) := (Nat.even_pow).mpr ⟨even_two, hi.ne'⟩
      exact (Nat.not_even_iff_odd.mpr hf) hev
