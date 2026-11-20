import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExt
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.NormValU

section Gen

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

/- English proof (translation)
Unfold `val`. Establish `hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0` using `by simpa using hx`. Establish `hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation E y ≠ 0` using `by simpa using hy`. Rewrite using `[map_mul, WithZero.log_mul hx' hy']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_mul_ne {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : val O (x * y) = val O x + val O y := by
  unfold val
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation E y ≠ 0 := by simpa using hy
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

/- English proof (translation)
Simplify using `[val]`.
-/
theorem val_one_eq : val O (1 : E) = 0 := by simp [val]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [val_one_eq]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, val_mul_ne O (pow_ne_zero _ hx) hx, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_pow_eq {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by
  induction k with
  | zero => simp [val_one_eq]
  | succ k ih =>
    rw [pow_succ, val_mul_ne O (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

/- English proof (translation)
Use `val_mul_ne O hx (inv_ne_zero hx)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hx, val_one_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_inv_eq {x : E} (hx : x ≠ 0) : val O x⁻¹ = -val O x := by
  have := val_mul_ne O hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, val_one_eq] at this
  omega

/- English proof (translation)
Establish `hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0` using `by simpa using hx`. Establish `h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation E x = 1`. Unfold `val at h`. Rewrite using `[← WithZero.exp_log hx']`. Establish `: WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x) = 0` using `by omega`.

Rewrite using `[this, WithZero.exp_zero]`. Conclude with `IsDiscreteValuationRing.exists_lift_of_le_one h1.le`.
-/
theorem lift_of_val_eq_zero {x : E} (hx : x ≠ 0) (h : val O x = 0) : ∃ a : O, algebraMap O E a = x := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation E x = 1 := by
    unfold val at h
    rw [← WithZero.exp_log hx']
    have : WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x) = 0 := by omega
    rw [this, WithZero.exp_zero]
  exact IsDiscreteValuationRing.exists_lift_of_le_one h1.le

/- English proof (translation)
Unfold `val`. Establish `: (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) = 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]`. Conclude with `fun h => (IsLocalRing.mem_maximalIdeal a).1 h ha`. Rewrite using `[this]`.

Simplify using the standard rewrite rules.
-/
theorem val_unit_eq (a : O) (ha : IsUnit a) : val O (algebraMap O E a) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (IsLocalRing.mem_maximalIdeal a).1 h ha
  rw [this]; simp

/- English proof (translation)
Take `⟨π, hπ⟩` from `(IsDiscreteValuationRing.maximalIdeal O).valuation_exists_uniformizer E`. Conclude with `⟨π, by simp [val, hπ]⟩`.
-/
theorem exists_val_one : ∃ π : E, val O π = 1 := by
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal O).valuation_exists_uniformizer E
  exact ⟨π, by simp [val, hπ]⟩

end Gen

/- English proof (translation)
Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Use `letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra`. Use `haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hd)`. Use `haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _`.

Establish `h` using `Algebra.isIntegral_norm (R := K.O) K.E (intO K K' d φ hU hd z)`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Conclude with `⟨a, ha⟩`.
-/
theorem norm_int (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) (hd : d ≠ 0) (z : K'.O) :
    ∃ a : K.O, algebraMap K.O K.E a = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  have h := Algebra.isIntegral_norm (R := K.O) K.E (intO K K' d φ hU hd z)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha⟩

/- English proof (translation)
Introduce `K K' d φ hφ y`. Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Establish `hd : d ≠ 0`. Introduce `hd0`. Establish `h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1`.

Rewrite using `[K'.card_res, hφ.1, hd0, pow_zero, one_pow]`. Establish `h2` using `Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)`. Use linear arithmetic over natural numbers and integers. Establish `hfr : Module.finrank K.E K'.E = d` using `hφ.2.2.2.2`. Use `haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by omega)`.

Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Rewrite using `[Algebra.norm_zero]`. Simplify using `[val]`. Take `⟨π, hπ⟩` from `exists_val_one K.O (E := K.E)`.

Establish `hπ0 : π ≠ 0` using `by rintro rfl; simp [val] at hπ`. Establish `hφπ : val K'.O (φ π) = 1` using `by rw [hφ.2.2.1, hπ]`. Establish `hφπ0 : φ π ≠ 0` using `(map_ne_zero φ).2 hπ0`. Use `set n := val K'.O y with hn`. Use `set a := (-n).toNat`.

Use `set b := n.toNat`. Establish `hab : (b : ℤ) - a = n` using `Int.toNat_sub_toNat_neg n`. Use `set u := y * φ π ^ a * (φ π ^ b)⁻¹ with hu`. Establish `hu0 : u ≠ 0` using `mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0))`. Establish `hvu : val K'.O u = 0`.

Rewrite using `[hu, val_mul_ne _ (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0)), val_mul_ne _ hy (pow_ne_zero _ hφπ0), val_inv_eq _ (pow_ne_zero _ hφπ0), val_pow_eq _ hφπ0, val_pow_eq _ hφπ0, hφπ, ← hn]`. Use linear arithmetic over natural numbers and integers. Establish `hvu' : val K'.O u⁻¹ = 0` using `by rw [val_inv_eq _ hu0, hvu]; rfl`. Take `⟨u₁, hu₁⟩` from `lift_of_val_eq_zero K'.O hu0 hvu`. Take `⟨u₂, hu₂⟩` from `lift_of_val_eq_zero K'.O (inv_ne_zero hu0) hvu'`.

Take `⟨m₁, hm₁⟩` from `norm_int K K' d φ hφ hd u₁`. Take `⟨m₂, hm₂⟩` from `norm_int K K' d φ hφ hd u₂`. Establish `hunit : IsUnit m₁`. Establish `h12 : m₁ * m₂ = 1`. Apply `IsFractionRing.injective K.O K.E` to reduce the goal to its premises.

Rewrite using `[map_mul, hm₁, hm₂, hu₁, hu₂, ← map_mul, mul_inv_cancel₀ hu0, map_one, map_one]`. Conclude with `IsUnit.of_mul_eq_one m₂ h12`. Establish `hNu : val K.O (Algebra.norm K.E u) = 0`. Rewrite using `[← hu₁, ← hm₁]`. Conclude with `val_unit_eq K.O m₁ hunit`.

Establish `hNu0 : Algebra.norm K.E u ≠ 0` using `Algebra.norm_ne_zero_iff.2 hu0`. Establish `hNy0 : Algebra.norm K.E y ≠ 0` using `Algebra.norm_ne_zero_iff.2 hy`. Establish `hNφ : Algebra.norm K.E (φ π) = π ^ d`. Rewrite using `[← hfr]`. Conclude with `Algebra.norm_algebraMap π`.

Establish `key : y * φ π ^ a = u * φ π ^ b`. Rewrite using `[hu, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hφπ0), mul_one]`. Establish `key2` using `congrArg (fun x => val K.O (Algebra.norm K.E x)) key`. Simplify using `only [map_mul, map_pow, hNφ] at key2`. Rewrite `key2` using `[val_mul_ne _ hNy0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_mul_ne _ hNu0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_pow_eq _ (pow_ne_zero _ hπ0), val_pow_eq _ (pow_ne_zero _ hπ0), val_pow_eq _ hπ0, hNu, hπ]`.

Rewrite using `[← hab]`. Move the coercions through the operations in `at key2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem val_norm : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E,
    val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  intro K K' d φ hφ y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hd : d ≠ 0 := by
    intro hd0
    have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
      rw [K'.card_res, hφ.1, hd0, pow_zero, one_pow]
    have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
    omega
  have hfr : Module.finrank K.E K'.E = d := hφ.2.2.2.2
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by omega)
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero]
    simp [val]
  obtain ⟨π, hπ⟩ := exists_val_one K.O (E := K.E)
  have hπ0 : π ≠ 0 := by rintro rfl; simp [val] at hπ
  have hφπ : val K'.O (φ π) = 1 := by rw [hφ.2.2.1, hπ]
  have hφπ0 : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
  set n := val K'.O y with hn
  set a := (-n).toNat
  set b := n.toNat
  have hab : (b : ℤ) - a = n := Int.toNat_sub_toNat_neg n
  set u := y * φ π ^ a * (φ π ^ b)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0))
  have hvu : val K'.O u = 0 := by
    rw [hu, val_mul_ne _ (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0)),
      val_mul_ne _ hy (pow_ne_zero _ hφπ0), val_inv_eq _ (pow_ne_zero _ hφπ0), val_pow_eq _ hφπ0,
      val_pow_eq _ hφπ0, hφπ, ← hn]
    omega
  have hvu' : val K'.O u⁻¹ = 0 := by rw [val_inv_eq _ hu0, hvu]; rfl
  obtain ⟨u₁, hu₁⟩ := lift_of_val_eq_zero K'.O hu0 hvu
  obtain ⟨u₂, hu₂⟩ := lift_of_val_eq_zero K'.O (inv_ne_zero hu0) hvu'
  obtain ⟨m₁, hm₁⟩ := norm_int K K' d φ hφ hd u₁
  obtain ⟨m₂, hm₂⟩ := norm_int K K' d φ hφ hd u₂
  have hunit : IsUnit m₁ := by
    have h12 : m₁ * m₂ = 1 := by
      apply IsFractionRing.injective K.O K.E
      rw [map_mul, hm₁, hm₂, hu₁, hu₂, ← map_mul, mul_inv_cancel₀ hu0, map_one, map_one]
    exact IsUnit.of_mul_eq_one m₂ h12
  have hNu : val K.O (Algebra.norm K.E u) = 0 := by
    rw [← hu₁, ← hm₁]; exact val_unit_eq K.O m₁ hunit
  have hNu0 : Algebra.norm K.E u ≠ 0 := Algebra.norm_ne_zero_iff.2 hu0
  have hNy0 : Algebra.norm K.E y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hNφ : Algebra.norm K.E (φ π) = π ^ d := by
    rw [← hfr]; exact Algebra.norm_algebraMap π
  have key : y * φ π ^ a = u * φ π ^ b := by
    rw [hu, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hφπ0), mul_one]
  have key2 := congrArg (fun x => val K.O (Algebra.norm K.E x)) key
  simp only [map_mul, map_pow, hNφ] at key2
  rw [val_mul_ne _ hNy0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_mul_ne _ hNu0 (pow_ne_zero _ (pow_ne_zero _ hπ0)),
    val_pow_eq _ (pow_ne_zero _ hπ0), val_pow_eq _ (pow_ne_zero _ hπ0), val_pow_eq _ hπ0, hNu, hπ] at key2
  rw [← hab]
  push_cast at key2 ⊢
  linarith

end GlobalTheory.UnitLemma.Unr.NormValU
