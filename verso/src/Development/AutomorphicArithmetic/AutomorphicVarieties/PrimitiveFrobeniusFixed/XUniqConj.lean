import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

/- English proof (translation)
Establish `hζ` using `IsCyclotomicExtension.zeta_spec M ℚ K`. Use `set ζ := IsCyclotomicExtension.zeta M ℚ K`. Establish `hz : (φ ζ) ^ M = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`. Establish `key : φ (sg M K (-1) ζ) = starRingEnd ℂ (φ ζ)`. Rewrite using `[sg_apply M K (-1) hζ.pow_eq_one, map_pow]`.

Establish `hM : M ∣ ((-1 : (ZMod M)ˣ) : ZMod M).val + 1`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Use `push_cast`. Simplify using the standard rewrite rules. Establish `hnorm : ‖φ ζ‖ = 1`.

Establish `h1` using `congrArg norm hz`. Rewrite `h1` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne M)).mp h1`. Establish `hinv : starRingEnd ℂ (φ ζ) = (φ ζ)⁻¹`. Rewrite using `[Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]`.

Simplify using the standard rewrite rules. Rewrite using `[hinv]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ]`. Take `⟨k, hk⟩` from `hM`.

Rewrite using `[hk, pow_mul, hz, one_pow]`. Establish `hext` using `AlgHom.ext_of_adjoin_eq_top (R := ℚ) (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) (φ₁ := (φ.comp (sg M K (-1)).toAlgHom.toRingHom).toRatAlgHom) (φ₂ := ((starRingEnd ℂ).comp φ).toRatAlgHom) (by`. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality.

Conclude with `key)`. Establish `h2` using `DFunLike.congr_fun hext x`. Simplify using `using h2`.
-/
private theorem UpperTheory.V.ML.xUniq_conj (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {M} ℚ K] (φ : K →+* ℂ) (x : K) : φ (sg M K (-1) x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec M ℚ K
  set ζ := IsCyclotomicExtension.zeta M ℚ K
  have hz : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have key : φ (sg M K (-1) ζ) = starRingEnd ℂ (φ ζ) := by
    rw [sg_apply M K (-1) hζ.pow_eq_one, map_pow]
    have hM : M ∣ ((-1 : (ZMod M)ˣ) : ZMod M).val + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp
    have hnorm : ‖φ ζ‖ = 1 := by
      have h1 := congrArg norm hz
      rw [norm_pow, norm_one] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne M)).mp h1
    have hinv : starRingEnd ℂ (φ ζ) = (φ ζ)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
      simp
    rw [hinv]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hz, one_pow]
  have hext := AlgHom.ext_of_adjoin_eq_top (R := ℚ)
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
    (φ₁ := (φ.comp (sg M K (-1)).toAlgHom.toRingHom).toRatAlgHom)
    (φ₂ := ((starRingEnd ℂ).comp φ).toRatAlgHom)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact key)
  have h2 := DFunLike.congr_fun hext x
  simpa using h2

/- English proof (translation)
Introduce `M _ K _ _ _ b 𝔞 X X' _ hX hX'`. Take `⟨z, hz⟩` from `(FractionalIdeal.spanSingleton_eq_spanSingleton).mp (hX.2.trans hX'.2.symm)`. Use `set w : K := ((z : 𝓞 K) : K) with hw`. Establish `hX'eq : X' = w * X`. Rewrite using `[← hz, Units.smul_def, Algebra.smul_def]`.

Establish `hww : w * sg M K (-1) w = 1`. Establish `h1` using `hX'.1`. Rewrite `h1` using `[hX'eq, map_mul]`. Establish `h2` using `hX.1`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnorm : ∀ φ : K →+* ℂ, ‖φ w‖ = 1`. Introduce `φ`. Establish `h3 : φ w * starRingEnd ℂ (φ w) = 1`. Rewrite using `[← UpperTheory.V.ML.xUniq_conj M K φ w, ← map_mul, hww, map_one]`. Rewrite `h3` using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Establish `h4 : ‖φ w‖ ^ 2 = 1` using `by exact_mod_cast h3`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4`. Take `⟨n, hn, hwn⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ (RingOfIntegers.isIntegral_coe (z : 𝓞 K)) hnorm`. Establish `hzt : z ∈ NumberField.Units.torsion K`. Rewrite using `[NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]`.

Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `using hwn`. Establish `hpow : w ^ NumberField.Units.torsionOrder K = 1`.

Establish `h5` using `pow_card_eq_one' (x := (⟨z, hzt⟩ : NumberField.Units.torsion K))`. Establish `h6 : z ^ Nat.card (NumberField.Units.torsion K) = 1`. Establish `h7` using `congrArg Subtype.val h5`. Rewrite `h7` using `[SubgroupClass.coe_pow, OneMemClass.coe_one]`. Then use the resulting hypothesis. Establish `h8` using `congrArg (fun t : (𝓞 K)ˣ => ((t : 𝓞 K) : K)) h6`.

Simplify using `only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] at h8`. Conclude with `h8`. Use `⟨w, ?_, hX'eq⟩` and prove the remaining obligations. Establish `hdvd : NumberField.Units.torsionOrder K ∣ 2 * M`. Rewrite using `[IsCyclotomicExtension.Rat.torsionOrder_eq (n := M)]`.

Use `split_ifs with he`. Conclude with `dvd_mul_left M 2`. Conclude with `dvd_rfl`. Take `⟨k, hk⟩` from `hdvd`. Rewrite using `[hk, pow_mul, hpow, one_pow]`.
-/
theorem UpperTheory.V.ML.xUniq :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)) (X X' : K), 𝔞 ≠ ⊥ → IsX M K b 𝔞 X → IsX M K b 𝔞 X' → ∃ ζ : K, ζ ^ (2 * M) = 1 ∧ X' = ζ * X := by
  intro M _ K _ _ _ b 𝔞 X X' _ hX hX'
  obtain ⟨z, hz⟩ := (FractionalIdeal.spanSingleton_eq_spanSingleton).mp (hX.2.trans hX'.2.symm)
  set w : K := ((z : 𝓞 K) : K) with hw
  have hX'eq : X' = w * X := by
    rw [← hz, Units.smul_def, Algebra.smul_def]
  have hww : w * sg M K (-1) w = 1 := by
    have h1 := hX'.1
    rw [hX'eq, map_mul] at h1
    have h2 := hX.1
    calc w * sg M K (-1) w = w * sg M K (-1) w * (X * sg M K (-1) X) := by rw [h2, mul_one]
      _ = 1 := by rw [← h1]; ring
  have hnorm : ∀ φ : K →+* ℂ, ‖φ w‖ = 1 := by
    intro φ
    have h3 : φ w * starRingEnd ℂ (φ w) = 1 := by
      rw [← UpperTheory.V.ML.xUniq_conj M K φ w, ← map_mul, hww, map_one]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h3
    have h4 : ‖φ w‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h4
  obtain ⟨n, hn, hwn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
    (RingOfIntegers.isIntegral_coe (z : 𝓞 K)) hnorm
  have hzt : z ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using hwn
  have hpow : w ^ NumberField.Units.torsionOrder K = 1 := by
    have h5 := pow_card_eq_one' (x := (⟨z, hzt⟩ : NumberField.Units.torsion K))
    have h6 : z ^ Nat.card (NumberField.Units.torsion K) = 1 := by
      have h7 := congrArg Subtype.val h5
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h7
    have h8 := congrArg (fun t : (𝓞 K)ˣ => ((t : 𝓞 K) : K)) h6
    simp only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] at h8
    exact h8
  refine ⟨w, ?_, hX'eq⟩
  have hdvd : NumberField.Units.torsionOrder K ∣ 2 * M := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := M)]
    split_ifs with he
    · exact dvd_mul_left M 2
    · exact dvd_rfl
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hpow, one_pow]
