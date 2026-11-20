import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantCongruencesImaginaryQuadratic
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermutedStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.WeberSplit

/- English proof (translation)
Use `haveI : NeZero ((n : ℕ) : K) := hζ.neZero'`. Use `haveI : NeZero ((n : ℕ) : k) := ⟨fun h => NeZero.ne ((n : ℕ) : K) (by rw [← map_natCast (algebraMap k K), h, map_zero])⟩`. Use `haveI : FiniteDimensional k K := Module.finite_of_finrank_eq_succ h2`. Establish `hint : IsIntegral k ζ` using `IsIntegral.of_finite k ζ`. Establish `hmin : cyclotomic n k = minpoly k ζ` using `hζ.minpoly_eq_cyclotomic_of_irreducible hirr`.

Establish `hfr : Module.finrank k k⟮ζ⟯ = 2`. Rewrite using `[IntermediateField.adjoin.finrank hint, ← hmin, natDegree_cyclotomic, hn]`. Establish `htop : k⟮ζ⟯ = ⊤` using `IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hfr, IntermediateField.finrank_top', h2])`. Establish `h1 : Algebra.adjoin k {ζ} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop, IntermediateField.top_toSubalgebra]`.

Use `(IsCyclotomicExtension.iff_singleton n k K).2 ⟨⟨ζ, hζ⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ Algebra.adjoin k {ζ}` using `by rw [h1]; exact Algebra.mem_top`. Use `Algebra.adjoin_mono ?_ hx` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`.

Substitute `hy` using the available equality. Conclude with `hζ.pow_eq_one`.
-/
theorem isCyclotomic_of_root {k K : Type} [Field k] [Field K] [Algebra k K] (h2 : Module.finrank k K = 2) {n : ℕ}
    [NeZero n] (hirr : Irreducible (cyclotomic n k))
    (hn : n.totient = 2) {ζ : K} (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} k K := by
  haveI : NeZero ((n : ℕ) : K) := hζ.neZero'
  haveI : NeZero ((n : ℕ) : k) := ⟨fun h => NeZero.ne ((n : ℕ) : K) (by rw [← map_natCast (algebraMap k K), h, map_zero])⟩
  haveI : FiniteDimensional k K := Module.finite_of_finrank_eq_succ h2
  have hint : IsIntegral k ζ := IsIntegral.of_finite k ζ
  have hmin : cyclotomic n k = minpoly k ζ := hζ.minpoly_eq_cyclotomic_of_irreducible hirr
  have hfr : Module.finrank k k⟮ζ⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank hint, ← hmin, natDegree_cyclotomic, hn]
  have htop : k⟮ζ⟯ = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hfr, IntermediateField.finrank_top', h2])
  have h1 : Algebra.adjoin k {ζ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop,
      IntermediateField.top_toSubalgebra]
  refine (IsCyclotomicExtension.iff_singleton n k K).2 ⟨⟨ζ, hζ⟩, fun x => ?_⟩
  have hx : x ∈ Algebra.adjoin k {ζ} := by rw [h1]; exact Algebra.mem_top
  refine Algebra.adjoin_mono ?_ hx
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hζ.pow_eq_one

section Lattice

variable (K : IntermediateField ℚ ℂ) [NumberField K] (h2 : Module.finrank ℚ K = 2) (L : PeriodPair)
  (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z)

include hL in

/- English proof (translation)
Establish `hh : GlobalTheory.IsHomothetic m L (GlobalTheory.scalePeriods L m hm0)` using `GlobalTheory.isHomothetic_scalePeriods L m hm0`. Establish `h2' : (GlobalTheory.scalePeriods L m hm0).g₂ = L.g₂` using `by rw [GlobalTheory.IsHomothetic.g₂_eq hh]; exact e2`. Establish `h3' : (GlobalTheory.scalePeriods L m hm0).g₃ = L.g₃` using `by rw [GlobalTheory.IsHomothetic.g₃_eq hh]; exact e3`. Establish `hlat : (GlobalTheory.scalePeriods L m hm0).lattice = L.lattice` using `GlobalTheory.lattice_eq_of_g₂_eq_of_g₃_eq h2' h3'`. Establish `h1 : (1 : ℂ) ∈ L.lattice` using `(hL 1).2 ⟨1, by simp⟩`.

Establish `hm : m ∈ L.lattice`. Use `(hh 1).2 h1` as an intermediate fact. Rewrite `this` using `[hlat, mul_one]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `(hL m).1 hm`. Conclude with `⟨(a : K), ha⟩`.
-/
theorem mem_of_invariant (m : ℂ) (hm0 : m ≠ 0) (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) :
    ∃ a : K, (a : ℂ) = m := by
  have hh : GlobalTheory.IsHomothetic m L (GlobalTheory.scalePeriods L m hm0) := GlobalTheory.isHomothetic_scalePeriods L m hm0
  have h2' : (GlobalTheory.scalePeriods L m hm0).g₂ = L.g₂ := by rw [GlobalTheory.IsHomothetic.g₂_eq hh]; exact e2
  have h3' : (GlobalTheory.scalePeriods L m hm0).g₃ = L.g₃ := by rw [GlobalTheory.IsHomothetic.g₃_eq hh]; exact e3
  have hlat : (GlobalTheory.scalePeriods L m hm0).lattice = L.lattice := GlobalTheory.lattice_eq_of_g₂_eq_of_g₃_eq h2' h3'
  have h1 : (1 : ℂ) ∈ L.lattice := (hL 1).2 ⟨1, by simp⟩
  have hm : m ∈ L.lattice := by
    have := (hh 1).2 h1
    rwa [hlat, mul_one] at this
  obtain ⟨a, ha⟩ := (hL m).1 hm
  exact ⟨(a : K), ha⟩

include h2 hL in
/- English proof (translation)
Introduce `h0`. Establish `hm : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))) 3` using `Complex.isPrimitiveRoot_exp 3 (by norm_num)`. Establish `hm0 : Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ≠ 0` using `Complex.exp_ne_zero _`. Establish `hm6 : Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ 6 = 1`. Rewrite using `[show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hm.pow_eq_one, one_pow]`.

Take `⟨a, ha⟩` from `mem_of_invariant K L hL _ hm0 (by rw [h0, mul_zero]) (by rw [hm6, inv_one, one_mul])`. Establish `haK : IsPrimitiveRoot a 3`. Rewrite `hm` using `[← ha]`. Conclude with `IsPrimitiveRoot.coe_submonoidClass_iff.mp hm`. Use `haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩`.

Apply the tactic sequence `haveI : IsCyclotomicExtension {3} ℚ K := isCyclotomic_of_root h2 (cyclotomic.irreducible_rat (by norm_num)) (by rw [Nat.totient_prime Nat.prime_three] <;> norm_num) haK`. Establish `hdisc` using `IsCyclotomicExtension.Rat.discr_prime 3 K`. Evaluate the numerical expressions using `at hdisc`. Rewrite `hd` using `[hdisc]`. Evaluate the numerical expressions using `at hd`.
-/
theorem g₂_ne_zero (hd : discr K < -4) : L.g₂ ≠ 0 := by
  intro h0
  have hm : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hm0 : Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ≠ 0 := Complex.exp_ne_zero _
  have hm6 : Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ)) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hm.pow_eq_one, one_pow]
  obtain ⟨a, ha⟩ := mem_of_invariant K L hL _ hm0 (by rw [h0, mul_zero])
    (by rw [hm6, inv_one, one_mul])
  have haK : IsPrimitiveRoot a 3 := by
    rw [← ha] at hm
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclotomicExtension {3} ℚ K :=
    isCyclotomic_of_root h2 (cyclotomic.irreducible_rat (by norm_num))
      (by rw [Nat.totient_prime Nat.prime_three] <;> norm_num) haK
  have hdisc := IsCyclotomicExtension.Rat.discr_prime 3 K
  norm_num at hdisc
  rw [hdisc] at hd
  norm_num at hd

include h2 hL in
/- English proof (translation)
Introduce `h0`. Establish `hm : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) 4` using `Complex.isPrimitiveRoot_exp 4 (by norm_num)`. Establish `hm0 : Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ)) ≠ 0` using `Complex.exp_ne_zero _`. Take `⟨a, ha⟩` from `mem_of_invariant K L hL _ hm0 (by rw [hm.pow_eq_one, inv_one, one_mul]) (by rw [h0, mul_zero])`. Establish `haK4 : IsPrimitiveRoot a 4`.

Rewrite `hm` using `[← ha]`. Conclude with `IsPrimitiveRoot.coe_submonoidClass_iff.mp hm`. Establish `haK : IsPrimitiveRoot a (2 ^ 2)` using `by norm_num; exact haK4`. Apply the tactic sequence `haveI : IsCyclotomicExtension {2 ^ 2} ℚ K := isCyclotomic_of_root h2 (cyclotomic.irreducible_rat (by norm_num)) (by rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] <;> norm_num) haK`. Establish `hdisc` using `IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K`.

Rewrite `hdisc` using `[Nat.totient_prime_pow Nat.prime_two (by norm_num)]`. Evaluate the numerical expressions using `at hdisc`. Rewrite `hd` using `[hdisc]`. Evaluate the numerical expressions using `at hd`.
-/
theorem g₃_ne_zero (hd : discr K < -4) : L.g₃ ≠ 0 := by
  intro h0
  have hm : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ))) 4 :=
    Complex.isPrimitiveRoot_exp 4 (by norm_num)
  have hm0 : Complex.exp (2 * Real.pi * Complex.I / (4 : ℕ)) ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨a, ha⟩ := mem_of_invariant K L hL _ hm0 (by rw [hm.pow_eq_one, inv_one, one_mul])
    (by rw [h0, mul_zero])
  have haK4 : IsPrimitiveRoot a 4 := by
    rw [← ha] at hm
    exact IsPrimitiveRoot.coe_submonoidClass_iff.mp hm
  have haK : IsPrimitiveRoot a (2 ^ 2) := by norm_num; exact haK4
  haveI : IsCyclotomicExtension {2 ^ 2} ℚ K :=
    isCyclotomic_of_root h2 (cyclotomic.irreducible_rat (by norm_num))
      (by rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] <;> norm_num) haK
  have hdisc := IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K
  rw [Nat.totient_prime_pow Nat.prime_two (by norm_num)] at hdisc
  norm_num at hdisc
  rw [hdisc] at hd
  norm_num at hd

include h2 hL in
/- English proof (translation)
Take `⟨a, τ, ha, hlat⟩` from `(GlobalTheory.weierstrass_uniformisation.2.2.1 L).1`. Establish `hj` using `GlobalTheory.g₂_cube_div_eq_modularJ ha hlat`. Establish `hΔ` using `GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L`. Establish `hstab : ∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1}, (algebraMap K ℂ) (α : K) * x ∈ Submodule.span ℤ {(τ : ℂ), 1}`. Introduce `α x hx`.

Rewrite `hx`, the goal using `[Submodule.mem_span_pair]`. Take `⟨c, d, rfl⟩` from `hx`. Establish `hax : a * (c • (τ : ℂ) + d • (1 : ℂ)) ∈ L.lattice` using `(hlat _).2 ⟨c, d, by simp [zsmul_eq_mul]⟩`. Take `⟨b, hb⟩` from `(hL _).1 hax`. Establish `hmem : (((α * b : 𝓞 K) : K) : ℂ) ∈ L.lattice` using `(hL _).2 ⟨α * b, rfl⟩`.

Take `⟨c', d', h'⟩` from `(hlat _).1 hmem`. Use `⟨c', d', ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ ha` to reduce the goal to its premises. Establish `e1 : (((α * b : 𝓞 K) : K) : ℂ) = (algebraMap K ℂ) (α : K) * (((b : 𝓞 K) : K) : ℂ)`. Simplify using the standard rewrite rules.

Rewrite `e1` using `[hb]`. Simplify using `only [zsmul_eq_mul, mul_one] at h' e1 ⊢`. Rewrite using `[h', e1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint` using `GlobalTheory.isIntegral_modularJ_of_ringOfIntegers (K := K) h2 (algebraMap K ℂ) hstab`.

Establish `e : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = GlobalTheory.modularJ τ * algebraMap ℚ ℂ (1728 : ℚ)⁻¹`. Rewrite using `[← hj]`. Simplify using `only [map_inv₀, map_ofNat]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `((hint.tower_top (A := ℚ)).mul isIntegral_algebraMap).isAlgebraic`.
-/
theorem invariant_isAlgebraic : IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
  obtain ⟨a, τ, ha, hlat⟩ := (GlobalTheory.weierstrass_uniformisation.2.2.1 L).1
  have hj := GlobalTheory.g₂_cube_div_eq_modularJ ha hlat
  have hΔ := GlobalTheory.g₂_cube_sub_g₃_sq_ne_zero L
  have hstab : ∀ α : 𝓞 K, ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1},
      (algebraMap K ℂ) (α : K) * x ∈ Submodule.span ℤ {(τ : ℂ), 1} := by
    intro α x hx
    rw [Submodule.mem_span_pair] at hx ⊢
    obtain ⟨c, d, rfl⟩ := hx
    have hax : a * (c • (τ : ℂ) + d • (1 : ℂ)) ∈ L.lattice :=
      (hlat _).2 ⟨c, d, by simp [zsmul_eq_mul]⟩
    obtain ⟨b, hb⟩ := (hL _).1 hax
    have hmem : (((α * b : 𝓞 K) : K) : ℂ) ∈ L.lattice := (hL _).2 ⟨α * b, rfl⟩
    obtain ⟨c', d', h'⟩ := (hlat _).1 hmem
    refine ⟨c', d', ?_⟩
    apply mul_left_cancel₀ ha
    have e1 : (((α * b : 𝓞 K) : K) : ℂ) = (algebraMap K ℂ) (α : K) * (((b : 𝓞 K) : K) : ℂ) := by
      simp
    rw [hb] at e1
    simp only [zsmul_eq_mul, mul_one] at h' e1 ⊢
    rw [h', e1]
    ring
  have hint := GlobalTheory.isIntegral_modularJ_of_ringOfIntegers (K := K) h2 (algebraMap K ℂ) hstab
  have e : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = GlobalTheory.modularJ τ * algebraMap ℚ ℂ (1728 : ℚ)⁻¹ := by
    rw [← hj]
    simp only [map_inv₀, map_ofNat]
    field_simp
  rw [e]
  exact ((hint.tower_top (A := ℚ)).mul isIntegral_algebraMap).isAlgebraic

/- English proof (translation)
Establish `back : ∀ I : Ideal B, (I.map (e : B →+* C)).map (e.symm : C →+* B) = I` using `fun I => by`. Rewrite using `[Ideal.map_map, RingEquiv.symm_comp, Ideal.map_id]`. Establish `fwd : ∀ I : Ideal C, (I.map (e.symm : C →+* B)).map (e : B →+* C) = I` using `fun I => by`. Rewrite using `[Ideal.map_map, RingEquiv.comp_symm, Ideal.map_id]`. Use `Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.map (e : B →+* C), ?_, ?_⟩ : HeightOneSpectrum C)) ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Ideal.map_comap_of_equiv] haveI := Q.isPrime`. Conclude with `Ideal.comap_isPrime _ _`. Conclude with `(Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr Q.ne_bot`. Introduce `Q hQ`. Simplify using `only [Set.mem_setOf_eq] at hQ ⊢`.

Rewrite using `[← hQ]`. Use extensionality with `a`. Simplify using `only [Ideal.mem_comap]`. Rewrite using `[Ideal.map_comap_of_equiv]`. Simplify using `only [Ideal.mem_comap]`.

Rewrite using `[← hij, RingEquiv.symm_apply_apply]`. Introduce `Q₁ Q₂ _ _ h`. Establish `h'` using `congrArg (fun Q : HeightOneSpectrum C => Q.asIdeal.map (e.symm : C →+* B)) h`. Simplify using `only [back] at h'`. Conclude with `HeightOneSpectrum.ext h'`.

Introduce `Q hQ`. Simplify using `only [Set.mem_setOf_eq] at hQ`. Establish `hp : (Q.asIdeal.map (e.symm : C →+* B)).IsPrime`. Rewrite using `[Ideal.map_comap_of_equiv]`. Use `haveI := Q.isPrime`.

Conclude with `Ideal.comap_isPrime _ _`. Use `⟨⟨Q.asIdeal.map (e.symm : C →+* B), hp, (Ideal.map_eq_bot_iff_of_injective e.symm.injective).not.mpr Q.ne_bot⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[← hQ]`. Use extensionality with `a`.

Simplify using `only [Ideal.mem_comap]`. Rewrite using `[Ideal.map_comap_of_equiv]`. Simplify using `only [Ideal.mem_comap, RingEquiv.symm_symm]`. Rewrite using `[hij]`. Conclude with `HeightOneSpectrum.ext (fwd Q.asIdeal)`.
-/
private lemma ncard_primes_over_eq_of_ringEquiv_comp {A B C : Type} [CommRing A] [CommRing B] [IsDedekindDomain B]
    [CommRing C] [IsDedekindDomain C] (e : B ≃+* C) (i : A →+* B) (j : A →+* C)
    (hij : ∀ a, e (i a) = j a) (p : Ideal A) :
    {Q : HeightOneSpectrum B | Q.asIdeal.comap i = p}.ncard =
      {Q : HeightOneSpectrum C | Q.asIdeal.comap j = p}.ncard := by
  have back : ∀ I : Ideal B, (I.map (e : B →+* C)).map (e.symm : C →+* B) = I := fun I => by
    rw [Ideal.map_map, RingEquiv.symm_comp, Ideal.map_id]
  have fwd : ∀ I : Ideal C, (I.map (e.symm : C →+* B)).map (e : B →+* C) = I := fun I => by
    rw [Ideal.map_map, RingEquiv.comp_symm, Ideal.map_id]
  refine Set.ncard_congr (fun Q _ => (⟨Q.asIdeal.map (e : B →+* C), ?_, ?_⟩ : HeightOneSpectrum C))
    ?_ ?_ ?_
  · rw [Ideal.map_comap_of_equiv]
    haveI := Q.isPrime
    exact Ideal.comap_isPrime _ _
  · exact (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr Q.ne_bot
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ ⊢
    rw [← hQ]
    ext a
    simp only [Ideal.mem_comap]
    rw [Ideal.map_comap_of_equiv]
    simp only [Ideal.mem_comap]
    rw [← hij, RingEquiv.symm_apply_apply]
  · intro Q₁ Q₂ _ _ h
    have h' := congrArg (fun Q : HeightOneSpectrum C => Q.asIdeal.map (e.symm : C →+* B)) h
    simp only [back] at h'
    exact HeightOneSpectrum.ext h'
  · intro Q hQ
    simp only [Set.mem_setOf_eq] at hQ
    have hp : (Q.asIdeal.map (e.symm : C →+* B)).IsPrime := by
      rw [Ideal.map_comap_of_equiv]
      haveI := Q.isPrime
      exact Ideal.comap_isPrime _ _
    refine ⟨⟨Q.asIdeal.map (e.symm : C →+* B), hp,
      (Ideal.map_eq_bot_iff_of_injective e.symm.injective).not.mpr Q.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [← hQ]
      ext a
      simp only [Ideal.mem_comap]
      rw [Ideal.map_comap_of_equiv]
      simp only [Ideal.mem_comap, RingEquiv.symm_symm]
      rw [hij]
    · exact HeightOneSpectrum.ext (fwd Q.asIdeal)

end Lattice

/- English proof (translation)
Set `φ : M →ₐ[K] N` to `IsScalarTower.toAlgHom K M N`. Set `e : M ≃ₐ[K] φ.fieldRange` to `φ.equivFieldRange`. Establish `h1` using `GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes K N φ.fieldRange 𝔭 (fun σ hσ x hx => by`. Take `⟨y, rfl⟩` from `hx`. Conclude with `h σ hσ y)`.

Rewrite using `[ncard_primes_over_eq_of_ringEquiv_comp (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv) (algebraMap (𝓞 K) (𝓞 M)) (algebraMap (𝓞 K) (𝓞 φ.fieldRange)) ?_ 𝔭.asIdeal, h1]`. Conclude with `e.toLinearEquiv.finrank_eq.symm`. Introduce `a`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [NumberField.RingOfIntegers.mapRingEquiv_apply]`.

Conclude with `e.commutes (a : K)`.
-/
theorem ncard_eq_of_tower (K M N : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] [IsGalois K N] (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ σ : N ≃ₐ[K] N, GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x : M, σ (algebraMap M N x) = algebraMap M N x) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard =
      Module.finrank K M := by
  let φ : M →ₐ[K] N := IsScalarTower.toAlgHom K M N
  let e : M ≃ₐ[K] φ.fieldRange := φ.equivFieldRange
  have h1 := GlobalTheory.T.ncard_primes_eq_finrank_of_frobenius_fixes K N φ.fieldRange 𝔭 (fun σ hσ x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact h σ hσ y)
  rw [ncard_primes_over_eq_of_ringEquiv_comp (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv)
    (algebraMap (𝓞 K) (𝓞 M)) (algebraMap (𝓞 K) (𝓞 φ.fieldRange)) ?_ 𝔭.asIdeal, h1]
  · exact e.toLinearEquiv.finrank_eq.symm
  · intro a
    apply NumberField.RingOfIntegers.ext
    simp only [NumberField.RingOfIntegers.mapRingEquiv_apply]
    exact e.commutes (a : K)

/- English proof (translation)
Use `set f : 𝓞 N →+* ℂ := ι.comp (algebraMap (𝓞 N) N) with hf`. Establish `hinj : Function.Injective f` using `ι.injective.comp RingOfIntegers.coe_injective`. Establish `hbij : Function.Bijective f.rangeRestrict` using `⟨fun a b h => hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩`. Establish `hI : P.map f.rangeRestrict ≠ ⊤`. Rewrite using `[Ne, Ideal.map_eq_top_of_bijective (f := f.rangeRestrict) (hf := hbij)]` and apply the resulting hypothesis.

Take `⟨W, -, hW⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hI`. Use `⟨W, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : (f.range.subtype (f.rangeRestrict x)) ∈ W.nonunits` using `hW ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩`. Conclude with `(ValuationSubring.mem_nonunits_iff W).mp h1`.
-/
theorem exists_valuationSubring {N : Type} [Field N] (ι : N →+* ℂ) (P : Ideal (𝓞 N)) (hP : P ≠ ⊤) :
    ∃ W : ValuationSubring ℂ, ∀ x ∈ P, W.valuation (ι x) < 1 := by
  set f : 𝓞 N →+* ℂ := ι.comp (algebraMap (𝓞 N) N) with hf
  have hinj : Function.Injective f := ι.injective.comp RingOfIntegers.coe_injective
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hI : P.map f.rangeRestrict ≠ ⊤ := by
    rwa [Ne, Ideal.map_eq_top_of_bijective (f := f.rangeRestrict) (hf := hbij)]
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨W, fun x hx => ?_⟩
  have h1 : (f.range.subtype (f.rangeRestrict x)) ∈ W.nonunits :=
    hW ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  exact (ValuationSubring.mem_nonunits_iff W).mp h1

/- English proof (translation)
Establish `h1 : IsIntegral W.toLocalSubring.toSubring x` using `hx.tower_top`. Conclude with `(W.valuation_le_one_iff x).mpr (LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring h1)`.
-/
theorem valuation_le_one_of_isIntegral (W : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) :
    W.valuation x ≤ 1 := by
  have h1 : IsIntegral W.toLocalSubring.toSubring x := hx.tower_top
  exact (W.valuation_le_one_iff x).mpr
    (LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring h1)

/- English proof (translation)
Establish `hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1` using `fun m => (W.valuation_le_one_iff _).mpr (intCast_mem W m)`. Use `le_antisymm (hle d) (not_lt.mp fun hlt => ?_)` and prove the remaining obligations. Take `⟨u, w, huw⟩` from `((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hd`. Establish `h : (u : ℂ) * (p : ℂ) + (w : ℂ) * (d : ℂ) = 1` using `by exact_mod_cast huw`. Establish `h2 : W.valuation ((u : ℂ) * (p : ℂ) + (w : ℂ) * (d : ℂ)) < 1`.

Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h2` using `[h, map_one]`. Conclude with `lt_irrefl _ h2`.
-/
theorem valuation_intCast_eq_one (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : W.valuation p < 1) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) : W.valuation d = 1 := by
  have hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1 := fun m =>
    (W.valuation_le_one_iff _).mpr (intCast_mem W m)
  refine le_antisymm (hle d) (not_lt.mp fun hlt => ?_)
  obtain ⟨u, w, huw⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hd
  have h : (u : ℂ) * (p : ℂ) + (w : ℂ) * (d : ℂ) = 1 := by exact_mod_cast huw
  have h2 : W.valuation ((u : ℂ) * (p : ℂ) + (w : ℂ) * (d : ℂ)) < 1 := by
    apply Valuation.map_add_lt
    · rw [map_mul]
      calc W.valuation (u : ℂ) * W.valuation (p : ℂ) ≤ 1 * W.valuation (p : ℂ) := by
            gcongr; exact hle u
        _ < 1 := by rwa [one_mul]
    · rw [map_mul]
      calc W.valuation (w : ℂ) * W.valuation (d : ℂ) ≤ 1 * W.valuation (d : ℂ) := by
            gcongr; exact hle w
        _ < 1 := by rwa [one_mul]
  rw [h, map_one] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Establish `hd1 : W.valuation (d : ℂ) = 1` using `valuation_intCast_eq_one W hp hW hd`. Establish `hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1` using `fun m => (W.valuation_le_one_iff _).mpr (intCast_mem W m)`. Establish `hy : W.valuation (ι (σ (d • x) - (d • x) ^ p)) < 1` using `hσ ⟨d • x, hx⟩`. Simplify using `only [map_sub, map_pow, map_zsmul, zsmul_eq_mul, map_mul, map_intCast] at hy`. Establish `hX : W.valuation (ι x) ≤ 1`.

Establish `h0` using `valuation_le_one_of_isIntegral W (hx.map ι.toIntAlgHom)`. Establish `e : ι.toIntAlgHom (d • x) = (d : ℂ) * ι x`. Simplify using `[RingHom.toIntAlgHom, map_zsmul, zsmul_eq_mul]`. Rewrite `h0` using `[e, map_mul, hd1, one_mul]`. Conclude with `h0`.

Establish `hdvd : (p : ℤ) ∣ d ^ p - d` using `by haveI := Fact.mk hp`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.pow_card, sub_self]`. Take `⟨k, hk⟩` from `hdvd`.

Establish `hk' : ((d : ℂ) ^ p - d) = (p : ℂ) * k` using `by exact_mod_cast hk`. Establish `hsum : (d : ℂ) * (ι (σ x) - ι x ^ p) = ((d : ℂ) * ι (σ x) - ((d : ℂ) * ι x) ^ p) + ((d : ℂ) ^ p - d) * ι x ^ p` using `by ring`. Establish `h2 : W.valuation ((d : ℂ) * (ι (σ x) - ι x ^ p)) < 1`. Rewrite using `[hsum]`. Apply `Valuation.map_add_lt _ hy` to reduce the goal to its premises.

Rewrite using `[hk', map_mul, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hle k`. Conclude with `pow_le_one' hX p`. Use `_ < 1 := by rwa [mul_one, mul_one]`.

Rewrite `h2` using `[map_mul, hd1, one_mul]`. Then use the resulting hypothesis.
-/
theorem frob_congr {K N : Type} [Field K] [Field N] [Algebra K N] (ι : N →+* ℂ) (σ : N ≃ₐ[K] N)
    (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : W.valuation p < 1)
    (hσ : ∀ x : 𝓞 N, W.valuation (ι (σ • x - x ^ p : 𝓞 N)) < 1) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) {x : N}
    (hx : IsIntegral ℤ (d • x)) : W.valuation (ι (σ x) - ι x ^ p) < 1 := by
  have hd1 : W.valuation (d : ℂ) = 1 := valuation_intCast_eq_one W hp hW hd
  have hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1 := fun m =>
    (W.valuation_le_one_iff _).mpr (intCast_mem W m)
  have hy : W.valuation (ι (σ (d • x) - (d • x) ^ p)) < 1 := hσ ⟨d • x, hx⟩
  simp only [map_sub, map_pow, map_zsmul, zsmul_eq_mul, map_mul, map_intCast] at hy
  have hX : W.valuation (ι x) ≤ 1 := by
    have h0 := valuation_le_one_of_isIntegral W (hx.map ι.toIntAlgHom)
    have e : ι.toIntAlgHom (d • x) = (d : ℂ) * ι x := by
      simp [RingHom.toIntAlgHom, map_zsmul, zsmul_eq_mul]
    rw [e, map_mul, hd1, one_mul] at h0
    exact h0
  have hdvd : (p : ℤ) ∣ d ^ p - d := by
    haveI := Fact.mk hp
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  obtain ⟨k, hk⟩ := hdvd
  have hk' : ((d : ℂ) ^ p - d) = (p : ℂ) * k := by exact_mod_cast hk
  have hsum : (d : ℂ) * (ι (σ x) - ι x ^ p) =
      ((d : ℂ) * ι (σ x) - ((d : ℂ) * ι x) ^ p) + ((d : ℂ) ^ p - d) * ι x ^ p := by ring
  have h2 : W.valuation ((d : ℂ) * (ι (σ x) - ι x ^ p)) < 1 := by
    rw [hsum]
    apply Valuation.map_add_lt _ hy
    rw [hk', map_mul, map_mul, map_pow]
    calc W.valuation (p : ℂ) * W.valuation (k : ℂ) * W.valuation (ι x) ^ p
        ≤ W.valuation (p : ℂ) * 1 * 1 := by
          gcongr
          · exact hle k
          · exact pow_le_one' hX p
      _ < 1 := by rwa [mul_one, mul_one]
  rwa [map_mul, hd1, one_mul] at h2

/- English proof (translation)
Assume the negation of the conclusion as `hx0`. Establish `hd1 : W.valuation (d : ℂ) = 1` using `valuation_intCast_eq_one W hp hW hd`. Establish `h1` using `valuation_le_one_of_isIntegral W (hx.map ι.toIntAlgHom)`. Establish `e : ι.toIntAlgHom (d • x⁻¹) = (d : ℂ) * (ι x)⁻¹`. Simplify using `[RingHom.toIntAlgHom, map_zsmul, zsmul_eq_mul, map_inv₀]`.

Rewrite `h1` using `[e, map_mul, hd1, one_mul, map_inv₀]`. Establish `hne : W.valuation (ι x) ≠ 0` using `(Valuation.ne_zero_iff _).mpr ((map_ne_zero ι).mpr hx0)`. Establish `h3 : W.valuation (ι x) * (W.valuation (ι x))⁻¹ ≤ W.valuation (ι x) * 1` using `by gcongr`. Rewrite `h3` using `[mul_inv_cancel₀ hne, mul_one]`. Conclude with `absurd h (not_lt.mpr h3)`.
-/
theorem eq_zero_of_valuation_lt_one {N : Type} [Field N] (ι : N →+* ℂ)
    (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime) (hW : W.valuation p < 1) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) {x : N}
    (hx : IsIntegral ℤ (d • x⁻¹)) (h : W.valuation (ι x) < 1) : x = 0 := by
  by_contra hx0
  have hd1 : W.valuation (d : ℂ) = 1 := valuation_intCast_eq_one W hp hW hd
  have h1 := valuation_le_one_of_isIntegral W (hx.map ι.toIntAlgHom)
  have e : ι.toIntAlgHom (d • x⁻¹) = (d : ℂ) * (ι x)⁻¹ := by
    simp [RingHom.toIntAlgHom, map_zsmul, zsmul_eq_mul, map_inv₀]
  rw [e, map_mul, hd1, one_mul, map_inv₀] at h1
  have hne : W.valuation (ι x) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero ι).mpr hx0)
  have h3 : W.valuation (ι x) * (W.valuation (ι x))⁻¹ ≤ W.valuation (ι x) * 1 := by
    gcongr
  rw [mul_inv_cancel₀ hne, mul_one] at h3
  exact absurd h (not_lt.mpr h3)

/- English proof (translation)
Use `letI : Algebra K ℂ := ((algebraMap M ℂ).comp (algebraMap K M)).toAlgebra`. Use `haveI : IsScalarTower K M ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Take `⟨α, hα⟩` from `Field.exists_primitive_element K M`. Set `f` to `minpoly K α`. Set `N : IntermediateField K ℂ` to `IntermediateField.adjoin K (f.rootSet ℂ)`.

Use `haveI hS : f.IsSplittingField K N := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)`. Use `haveI : FiniteDimensional K N := Polynomial.IsSplittingField.finiteDimensional N f`. Use `haveI : Normal K N := Normal.of_isSplittingField f`. Use `haveI : NumberField N := NumberField.of_module_finite K N`. Use `haveI : IsGalois K N := ⟨⟩`.

Set `φ : M →ₐ[K] ℂ` to `IsScalarTower.toAlgHom K M ℂ`. Establish `hroot : φ α ∈ f.rootSet ℂ`. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral α), ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`.

Establish `hle : (⊤ : IntermediateField K M).map φ ≤ N`. Rewrite using `[← hα, IntermediateField.adjoin_map, Set.image_singleton]`. Conclude with `IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin K _ hroot))`. Establish `hmem : ∀ x : M, φ x ∈ N` using `fun x => hle ⟨x, trivial, rfl⟩`. Set `ψ : M →+* N` to `(φ : M →+* ℂ).codRestrict N hmem`.

Use `letI : Algebra M N := ψ.toAlgebra`. Use `haveI : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => Subtype.ext rfl)`. Conclude with `⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, (N.val : N →+* ℂ), fun x => rfl⟩`.
-/
theorem exists_isGalois (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [Algebra M ℂ] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N) (_ : Algebra M N),
      IsScalarTower K M N ∧ IsGalois K N ∧ ∃ ι : N →+* ℂ, ∀ x : M, ι (algebraMap M N x) = algebraMap M ℂ x := by
  letI : Algebra K ℂ := ((algebraMap M ℂ).comp (algebraMap K M)).toAlgebra
  haveI : IsScalarTower K M ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K M
  let f := minpoly K α
  let N : IntermediateField K ℂ := IntermediateField.adjoin K (f.rootSet ℂ)
  haveI hS : f.IsSplittingField K N :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional K N := Polynomial.IsSplittingField.finiteDimensional N f
  haveI : Normal K N := Normal.of_isSplittingField f
  haveI : NumberField N := NumberField.of_module_finite K N
  haveI : IsGalois K N := ⟨⟩
  let φ : M →ₐ[K] ℂ := IsScalarTower.toAlgHom K M ℂ
  have hroot : φ α ∈ f.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral α), ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hle : (⊤ : IntermediateField K M).map φ ≤ N := by
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton]
    exact IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin K _ hroot))
  have hmem : ∀ x : M, φ x ∈ N := fun x => hle ⟨x, trivial, rfl⟩
  let ψ : M →+* N := (φ : M →+* ℂ).codRestrict N hmem
  letI : Algebra M N := ψ.toAlgebra
  haveI : IsScalarTower K M N := IsScalarTower.of_algebraMap_eq (fun k => Subtype.ext rfl)
  exact ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (N.val : N →+* ℂ), fun x => rfl⟩

end GlobalTheory.WeberSplit
