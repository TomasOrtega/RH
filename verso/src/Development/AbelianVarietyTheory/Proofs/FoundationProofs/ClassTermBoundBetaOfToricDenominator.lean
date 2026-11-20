import Mathlib
import Development.AutomorphicArithmetic.WeightCongruences.ProdCMTypeEmbeddingsRootOfUnityEqOne
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BoundedDenominatorsOfBeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomBridge

/- English proof (translation)
Establish `h' : IsIntegral ℤ (algebraMap ℚ ℂ r)` using `h`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h')`.
-/
theorem exists_int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h')

/- English proof (translation)
Use `set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw`. Establish `hw2 : w ^ 2 = -(d : ℂ)`. Rewrite using `[hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]`. Simplify using the standard rewrite rules. Establish `hwc : starRingEnd ℂ w = -w` using `by simp [hw]`.

Establish `hZ : ∀ n : ℤ, IsIntegral ℤ (n : ℂ)` using `fun n => isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)`. Take `⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c` from `⟨(d + 1) / 4, by omega⟩`. Establish `hcC : (d : ℂ) + 1 = 4 * c` using `by exact_mod_cast hc`. Introduce `x`. Rewrite using `[PeriodPair.mem_lattice, h1, h2]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Use `⟨((hZ m).mul isIntegral_one).add ((hZ n).mul ?_), m + n / 2, n / 2, by push_cast; ring⟩` and prove the remaining obligations. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, algebraMap_int_eq, eq_intCast, Int.cast_natCast]`.

Take the linear combination `(1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC`. Introduce and unpack `⟨hx, a, b, rfl⟩`. Establish `hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w)`. Use `hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)` as an intermediate fact. Simplify `this` using `[hwc, sub_eq_add_neg]`.

Take `⟨t, ht⟩` from `exists_int_of_isIntegral (r := 2 * a) (by`. Use `(congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')` and prove the remaining obligations. Use `push_cast`. Use the proof step `ring)`. Take `⟨n, hn⟩` from `exists_int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by`.

Use `(congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(b : ℂ) ^ 2 * hw2)`. Establish `hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ)`. Use `push_cast`.

Rewrite using `[hn, ht]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩` from `exists_int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by`. Rewrite using `[← Rat.cast_pow, hm2, Rat.cast_intCast]`. Conclude with `hZ _))`.

Establish `hm3 : m ^ 2 = d * (4 * n - t ^ 2)`. Rewrite `hm2` using `[← hm]`. Conclude with `hm2` after adjusting the coercions. Take `⟨u, rfl⟩ : (d : ℤ) ∣ m` from `(Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow ⟨_, hm3⟩`. Establish `hd0 : (d : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hd.ne_zero`.

Establish `hu : (u : ℚ) = 2 * b`. Move the coercions through the operations in `at hm`. Conclude with `mul_left_cancel₀ hd0 hm`. Establish `hn4 : 4 * n = t ^ 2 + d * u ^ 2`. Establish `: (4 : ℚ) * n = t ^ 2 + d * u ^ 2` using `by rw [hn, ht, hu]; ring`.

Conclude with `this` after adjusting the coercions. Establish `hcZ : (d : ℤ) = 4 * c - 1` using `by omega`. Establish `hpar : Even (t - u)`. Establish `h5 : Even ((t - u) * (t - u))` using `⟨2 * n - 2 * c * u ^ 2 + u ^ 2 - t * u, by rw [hcZ] at hn4; linear_combination -hn4⟩`. Conclude with `(Int.even_mul.1 h5).elim id id`.

Take `⟨k, hk⟩` from `hpar`. Use `⟨k, u, ?_⟩` and prove the remaining obligations. Establish `e1 : (t : ℂ) = 2 * a` using `by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) ht`. Establish `e2 : (u : ℂ) = 2 * b` using `by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hu`. Establish `e3 : (t : ℂ) - u = k + k` using `by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hk`.

Take the linear combination `(-1 / 2 : ℂ) * e3 + (1 / 2 : ℂ) * e1 + (w / 2) * e2`.
-/
theorem isIntLattice_of {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) {Λ : PeriodPair} (h1 : Λ.ω₁ = 1)
    (h2 : Λ.ω₂ = (1 + Complex.I * (Real.sqrt d : ℝ)) / 2) : IsIntLattice d Λ := by
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hZ : ∀ n : ℤ, IsIntegral ℤ (n : ℂ) := fun n => isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
  have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  intro x
  rw [PeriodPair.mem_lattice, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨((hZ m).mul isIntegral_one).add ((hZ n).mul ?_), m + n / 2, n / 2, by push_cast; ring⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
  · rintro ⟨hx, a, b, rfl⟩
    have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
      have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
      simpa [hwc, sub_eq_add_neg] using this
    obtain ⟨t, ht⟩ := exists_int_of_isIntegral (r := 2 * a) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
      push_cast; ring)
    obtain ⟨n, hn⟩ := exists_int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
      push_cast
      linear_combination (b : ℂ) ^ 2 * hw2)
    have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [hn, ht]; ring
    obtain ⟨m, hm⟩ := exists_int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
      rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
      exact hZ _))
    have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
      rw [← hm] at hm2
      exact_mod_cast hm2
    obtain ⟨u, rfl⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow ⟨_, hm3⟩
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
    have hu : (u : ℚ) = 2 * b := by
      push_cast at hm
      exact mul_left_cancel₀ hd0 hm
    have hn4 : 4 * n = t ^ 2 + d * u ^ 2 := by
      have : (4 : ℚ) * n = t ^ 2 + d * u ^ 2 := by rw [hn, ht, hu]; ring
      exact_mod_cast this
    have hcZ : (d : ℤ) = 4 * c - 1 := by omega
    have hpar : Even (t - u) := by
      have h5 : Even ((t - u) * (t - u)) :=
        ⟨2 * n - 2 * c * u ^ 2 + u ^ 2 - t * u, by rw [hcZ] at hn4; linear_combination -hn4⟩
      exact (Int.even_mul.1 h5).elim id id
    obtain ⟨k, hk⟩ := hpar
    refine ⟨k, u, ?_⟩
    have e1 : (t : ℂ) = 2 * a := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) ht
    have e2 : (u : ℂ) = 2 * b := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hu
    have e3 : (t : ℂ) - u = k + k := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hk
    linear_combination (-1 / 2 : ℂ) * e3 + (1 / 2 : ℂ) * e1 + (w / 2) * e2

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Use `H.hostE_isGalois` as an intermediate fact. Establish `: IsMulCommutative Gal(H.E/ℚ)` using `⟨⟨fun σ τ => (H.gal).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩`. Conclude with `{}`.
-/
theorem host_isAbelianGalois : IsAbelianGalois ℚ H.E := by
  have := H.hostE_isGalois
  have : IsMulCommutative Gal(H.E/ℚ) :=
    ⟨⟨fun σ τ => (H.gal).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  exact {}

/- English proof (translation)
Establish `: IsCMField H.E` using `H.isCMField_hostE`. Establish `h : discr H.E = discr (maximalRealSubfield H.E) ^ 2` using `H.der.discr_sq`. Establish `h2` using `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield H.E) (OF H.E) H.E (𝓞 H.E)`. Rewrite `h2` using `[Algebra.IsQuadraticExtension.finrank_eq_two, h, Int.natAbs_pow]`. Establish `h0 : (discr (maximalRealSubfield H.E)).natAbs ^ 2 ≠ 0` using `pow_ne_zero _ (Int.natAbs_ne_zero.2 (discr_ne_zero _))`.

Conclude with `Ideal.absNorm_eq_one_iff.1 (mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm))`.
-/
theorem host_unramFin : UnramFin H.E := by
  have : IsCMField H.E := H.isCMField_hostE
  have h : discr H.E = discr (maximalRealSubfield H.E) ^ 2 := H.der.discr_sq
  have h2 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (maximalRealSubfield H.E) (OF H.E) H.E (𝓞 H.E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two, h, Int.natAbs_pow] at h2
  have h0 : (discr (maximalRealSubfield H.E)).natAbs ^ 2 ≠ 0 := pow_ne_zero _ (Int.natAbs_ne_zero.2 (discr_ne_zero _))
  exact Ideal.absNorm_eq_one_iff.1 (mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm))

/- English proof (translation)
The claim follows from `H.der.discr_primes.2.1`.
-/
theorem two_dvd_discr_host : (2 : ℤ) ∣ discr H.E := H.der.discr_primes.2.1

/- English proof (translation)
Use `Fintype.card_le_of_surjective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) fun σ => by` as an intermediate fact. Take `⟨i, hi | hi, -⟩` from `h σ`. Conclude with `⟨Sum.inl i, hi.symm⟩`. Conclude with `⟨Sum.inr i, hi.symm⟩`. Rewrite `this` using `[Embeddings.card, Fintype.card_sum, ← two_mul]`. Then use the resulting hypothesis.
-/
theorem finrank_le_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Module.finrank ℚ E ≤ 2 * Fintype.card I := by
  have := Fintype.card_le_of_surjective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) fun σ => by
    obtain ⟨i, hi | hi, -⟩ := h σ
    · exact ⟨Sum.inl i, hi.symm⟩
    · exact ⟨Sum.inr i, hi.symm⟩
  rwa [Embeddings.card, Fintype.card_sum, ← two_mul] at this

/- English proof (translation)
Establish `hcard : 2 ≤ Fintype.card I`. Establish `h1` using `finrank_le_of_isCMType h`. Establish `h2 : Module.finrank ℚ H.E = 4 * R.ord` using `H.finrank_cmField`. Establish `h3 : 0 < R.ord` using `R.ord_pos`. Rewrite `h1` using `[h2]`.

Use linear arithmetic over natural numbers and integers. Use `⟨H.hyp.2.1, by have := H.hyp.2.2.2.1; omega, host_unramFin H, fun x hx => ?_, two_dvd_discr_host H, hcard, h, ?_⟩` and prove the remaining obligations. Conclude with `UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one R H I φ h h' x (isOfFinOrder_iff_pow_eq_one.1 hx)`. Take `⟨i⟩ : Nonempty I` from `Fintype.card_pos_iff.1 (by omega)`. Establish `hb : H.sqrtMinusD ^ 2 = -(H.d : H.E)` using `H.sqrtMinusD_sq`.

Establish `hsq : φ i H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℝ)) ^ 2`. Rewrite using `[← map_pow, hb, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e` into its components or cases. Conclude with `⟨_, hb, fun j => (h' j i).trans e⟩`.

Conclude with `⟨-H.sqrtMinusD, by rw [neg_sq, hb], fun j => by rw [map_neg, h' j i, e, neg_neg]⟩`.
-/
theorem isFieldData_host {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} (h : IsCMType φ)
    (h' : ∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) : IsFieldData H.d φ := by
  have hcard : 2 ≤ Fintype.card I := by
    have h1 := finrank_le_of_isCMType h
    have h2 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
    have h3 : 0 < R.ord := R.ord_pos
    rw [h2] at h1
    omega
  refine ⟨H.hyp.2.1, by have := H.hyp.2.2.2.1; omega, host_unramFin H, fun x hx => ?_, two_dvd_discr_host H, hcard, h, ?_⟩
  · exact UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one R H I φ h h' x (isOfFinOrder_iff_pow_eq_one.1 hx)
  · obtain ⟨i⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqrtMinusD_sq
    have hsq : φ i H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℝ)) ^ 2 := by
      rw [← map_pow, hb, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · exact ⟨_, hb, fun j => (h' j i).trans e⟩
    · exact ⟨-H.sqrtMinusD, by rw [neg_sq, hb], fun j => by rw [map_neg, h' j i, e, neg_neg]⟩

/- English proof (translation)
Introduce `R H I _ φ s κ 𝔣 χ hD Λ h1 h2 l hl`. Establish `: IsCMField H.E` using `H.isCMField_hostE`. Use `host_isAbelianGalois H` as an intermediate fact. Take `⟨z, -, hz⟩` from `h H.E I H.d φ s (isFieldData_host H hD.1 hD.2.1) hD.2.2.1`. Establish `hΛ` using `isIntLattice_of H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) h1 h2`.

Use `⟨⌈betaBound_vp H.d s κ 𝔣 z l⌉₊, fun Q hQ hQl y T hT => ?_⟩` and prove the remaining obligations. Use `(hz κ 𝔣 Λ χ hD.2.2.2.2.1 hΛ hD.2.2.2.2.2 l hl Q hQ hQl).1 y T hT (⌈betaBound_vp H.d s κ 𝔣 z l⌉₊ : ℕ) 1 one_pos (by simpa using Nat.le_ceil _)` as an intermediate fact. Simplify using `using this`.
-/
theorem classTermBoundBeta_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBoundBeta := by
  intro R H I _ φ s κ 𝔣 χ hD Λ h1 h2 l hl
  have : IsCMField H.E := H.isCMField_hostE
  have := host_isAbelianGalois H
  obtain ⟨z, -, hz⟩ := h H.E I H.d φ s (isFieldData_host H hD.1 hD.2.1) hD.2.2.1
  have hΛ := isIntLattice_of H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) h1 h2
  refine ⟨⌈betaBound_vp H.d s κ 𝔣 z l⌉₊, fun Q hQ hQl y T hT => ?_⟩
  have := (hz κ 𝔣 Λ χ hD.2.2.2.2.1 hΛ hD.2.2.2.2.2 l hl Q hQ hQl).1 y T hT (⌈betaBound_vp H.d s κ 𝔣 z l⌉₊ : ℕ) 1 one_pos
    (by simpa using Nat.le_ceil _)
  simpa using this

/- English proof (translation)
The claim follows from `GlobalTheory.ToricDenom.classTermBound_of_beta (classTermBoundBeta_of_toricDenominator h)`.
-/
theorem classTermBound_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBound :=
  GlobalTheory.ToricDenom.classTermBound_of_beta (classTermBoundBeta_of_toricDenominator h)

end GlobalTheory.ToricDenomBridge
