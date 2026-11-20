import Mathlib

open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Take `⟨m, hm, t, ht⟩` from `hy.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hy0)`. Establish `ht' : (m : S) = y * t` using `by simpa using ht`. Use `⟨(m.sign : S) * t, m.natAbs, Int.natAbs_pos.mpr hm, ?_⟩` and prove the remaining obligations. Establish `h1 : ((m.natAbs : ℤ) : S) = ((m.sign * m : ℤ) : S)`. Rewrite using `[Int.sign_mul_self_eq_natAbs]`.

Establish `h2 : (m.natAbs : S) = (m.sign : S) * (m : S)`. Rewrite using `[← Int.cast_mul, ← h1, Int.cast_natCast]`. Rewrite using `[h2, ht']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_eq_natCast_of_isIntegral_int {S : Type*} [CommRing S] [IsDomain S]
    {y : S} (hy : IsIntegral ℤ y) (hy0 : y ≠ 0) :
    ∃ (t : S) (n : ℕ), 0 < n ∧ y * t = n := by
  obtain ⟨m, hm, t, ht⟩ :=
    hy.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hy0)
  have ht' : (m : S) = y * t := by simpa using ht
  refine ⟨(m.sign : S) * t, m.natAbs, Int.natAbs_pos.mpr hm, ?_⟩
  have h1 : ((m.natAbs : ℤ) : S) = ((m.sign * m : ℤ) : S) := by
    rw [Int.sign_mul_self_eq_natAbs]
  have h2 : (m.natAbs : S) = (m.sign : S) * (m : S) := by
    rw [← Int.cast_mul, ← h1, Int.cast_natCast]
  rw [h2, ht']; ring

/- English proof (translation)
Introduce `R _ φ hφ`. Set `S` to `R ⧸ RingHom.ker φ`. Establish `hinj : Function.Injective (RingHom.kerLift φ)` using `RingHom.kerLift_injective φ`. Use `haveI : IsDomain S := hinj.isDomain (RingHom.kerLift φ)`. Use `haveI : CharZero S := (RingHom.kerLift φ).charZero`.

Establish `hint : ∀ y : S, @IsIntegral ℤ S _ _ (Ring.toIntAlgebra S) y`. Introduce `y`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[← isIntegral_algHom_iff (RingHom.kerLift φ).toIntAlgHom hinj]`. Conclude with `hφ r`.

Use `haveI : CharZero (FractionRing S) := charZero_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S))`. Use `⟨FractionRing S, inferInstance, inferInstance, (algebraMap S (FractionRing S)).comp (Ideal.Quotient.mk _), ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨a, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := S) x`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`.

Take `⟨t, n, hn, ht⟩` from `exists_mul_eq_natCast_of_isIntegral_int (hint y) hy0`. Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (a * t)`. Use `⟨r, n, hn, ?_⟩` and prove the remaining obligations. Establish `hy' : algebraMap S (FractionRing S) y ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hy0`. Establish `hn' : (n : FractionRing S) = algebraMap S (FractionRing S) y * algebraMap S (FractionRing S) t`.

Rewrite using `[← map_mul, ht, map_natCast]`. Rewrite using `[RingHom.comp_apply, hr, hn', map_mul]`. Clear the denominators using the available nonvanishing facts. Introduce `A _ _ χ hχ`. Set `ψ : S →+* A` to `Ideal.Quotient.lift (RingHom.ker φ) χ (fun r hr => hχ r hr)`.

Establish `hu : ∀ y : nonZeroDivisors S, IsUnit (ψ y)`. Introduce `y`. Take `⟨t, n, hn, ht⟩` from `exists_mul_eq_natCast_of_isIntegral_int (hint y) (nonZeroDivisors.ne_zero y.2)`. Establish `hnu : IsUnit (n : A)`. Establish `: IsUnit (n : ℚ)` using `IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')`.

Simplify using `using this.map (algebraMap ℚ A)`. Establish `: ψ y * ψ t = n` using `by rw [← map_mul, ht, map_natCast]`. Conclude with `isUnit_of_mul_isUnit_left (this ▸ hnu)`. Use `⟨IsLocalization.lift (M := nonZeroDivisors S) (S := FractionRing S) hu, ?_⟩` and prove the remaining obligations. Use extensionality with `r`.

Simplify using `only [RingHom.comp_apply, IsLocalization.lift_eq]`. Both sides reduce to the same expression.
-/
theorem exists_field_of_isIntegral_image :
    ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  intro R _ φ hφ
  let S := R ⧸ RingHom.ker φ
  have hinj : Function.Injective (RingHom.kerLift φ) := RingHom.kerLift_injective φ
  haveI : IsDomain S := hinj.isDomain (RingHom.kerLift φ)
  haveI : CharZero S := (RingHom.kerLift φ).charZero
  have hint : ∀ y : S, @IsIntegral ℤ S _ _ (Ring.toIntAlgebra S) y := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isIntegral_algHom_iff (RingHom.kerLift φ).toIntAlgHom hinj]
    exact hφ r
  haveI : CharZero (FractionRing S) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S))
  refine ⟨FractionRing S, inferInstance, inferInstance,
    (algebraMap S (FractionRing S)).comp (Ideal.Quotient.mk _), ?_, ?_⟩
  · intro x
    obtain ⟨a, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨t, n, hn, ht⟩ := exists_mul_eq_natCast_of_isIntegral_int (hint y) hy0
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (a * t)
    refine ⟨r, n, hn, ?_⟩
    have hy' : algebraMap S (FractionRing S) y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hy0
    have hn' : (n : FractionRing S) =
        algebraMap S (FractionRing S) y * algebraMap S (FractionRing S) t := by
      rw [← map_mul, ht, map_natCast]
    rw [RingHom.comp_apply, hr, hn', map_mul]
    field_simp
  · intro A _ _ χ hχ
    let ψ : S →+* A := Ideal.Quotient.lift (RingHom.ker φ) χ (fun r hr => hχ r hr)
    have hu : ∀ y : nonZeroDivisors S, IsUnit (ψ y) := by
      intro y
      obtain ⟨t, n, hn, ht⟩ :=
        exists_mul_eq_natCast_of_isIntegral_int (hint y) (nonZeroDivisors.ne_zero y.2)
      have hnu : IsUnit (n : A) := by
        have : IsUnit (n : ℚ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
        simpa using this.map (algebraMap ℚ A)
      have : ψ y * ψ t = n := by rw [← map_mul, ht, map_natCast]
      exact isUnit_of_mul_isUnit_left (this ▸ hnu)
    refine ⟨IsLocalization.lift (M := nonZeroDivisors S) (S := FractionRing S) hu, ?_⟩
    ext r
    simp only [RingHom.comp_apply, IsLocalization.lift_eq]
    rfl

end GlobalTheory
