import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Apply `IsDiscreteValuationRing.exists_lift_of_le_one` to reduce the goal to its premises. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0` using `by simpa using hx`. Unfold `val at h`.

Rewrite using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem intO_lift_of_val_nonneg (K : UQ) (x : K.E) (h : 0 ≤ val K.O x) : ∃ a : K.O, algebraMap K.O K.E a = x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  unfold val at h
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[ha, val]`. Establish `h1` using `(IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) a`. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0`. Simplify using `using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha`.

Unfold `val`. Rewrite `h1` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem intO_val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  have h1 := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/- English proof (translation)
Establish `h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) < 1` using `(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha`. Establish `h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0`. Simplify using `using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha0`. Unfold `val`. Rewrite `h1` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem intO_val_ne_zero_of_mem (K : UQ) (a : K.O) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal K.O) :
    val K.O (algebraMap K.O K.E a) ≠ 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha0
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

/- English proof (translation)
Introduce `K K' d φ hU hd y`. Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Use `letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra`. Use `haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hfr : Module.finrank K.E K'.E = d` using `hU.2.2.2.2`.

Use `haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _`. Set `S` to `integralClosure K.O K'.E`. Use `haveI : Module.Finite K.O S := IsIntegralClosure.finite K.O K.E K'.E S`. Use `haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain K.O K.E K'.E S`.

Use `haveI : IsFractionRing S K'.E := IsIntegralClosure.isFractionRing_of_finite_extension K.O K.E K'.E S`. Use `haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := K.O) S`. Establish `hinj : Function.Injective (algebraMap K.O S)` using `algebraMap_injective_of_field_isFractionRing K.O S K.E K'.E`. Establish `hnf : ¬ IsField S` using `fun h => IsDiscreteValuationRing.not_isField K.O (isField_of_isIntegral_of_isField hinj h)`. Use `haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1 (inferInstance : IsDedekindDomain S)`.

Establish `hv : ∀ a : K.O, 0 ≤ val K'.O (φ (algebraMap K.O K.E a))` using `fun a => by`. Rewrite using `[hU.2.2.1]`. Conclude with `intO_val_algebraMap_nonneg K a`. Use `choose ψf hψf using fun a : K.O => intO_lift_of_val_nonneg K' _ (hv a)`. Establish `hinj' : Function.Injective (algebraMap K'.O K'.E)` using `IsFractionRing.injective _ _`.

Set `ψ : K.O →+* K'.O` to `{ toFun := ψf map_one' := hinj' (by rw [hψf]; simp) map_mul' := fun a b => hinj' (by simp [hψf]) map_zero' := hinj' (by rw [hψf]; simp) map_add' := fun a b => hinj' (by simp [hψf]) }`. Establish `hψ : ∀ a, algebraMap K'.O K'.E (ψ a) = algebraMap K.O K'.E a` using `fun a => hψf a`. Establish `hS : ∀ t : K'.E, IsIntegral K.O t → ∃ z : K'.O, algebraMap K'.O K'.E z = t`. Introduce `t ht`. Establish `: IsIntegral K'.O t` using `IsIntegral.map_of_comp_eq (T := K'.O) (U := K'.E) ψ (RingHom.id K'.E) (by ext a; exact hψ a) ht`.

Conclude with `IsIntegrallyClosed.isIntegral_iff.1 this`. Use `set x := algebraMap K'.O K'.E y with hx`. Break down `ValuationRing.isInteger_or_isInteger S x with ⟨s, hs⟩ | ⟨s, hs⟩` into its components or cases. Rewrite using `[← hs]`. Conclude with `s.2`.

Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `isIntegral_zero`. Distinguish the cases in `hsu : IsUnit s`. Establish `hu1 : ((hsu.unit⁻¹ : Sˣ) : S) * s = 1`.

Use `hsu.unit.inv_mul` as an intermediate fact. Rewrite `this` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis. Establish `e : algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) * algebraMap S K'.E s = 1`. Rewrite using `[← map_mul, hu1, map_one]`. Establish `: x = algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S)`.

Rewrite using `[eq_inv_of_mul_eq_one_left e, hs, inv_inv]`. Rewrite using `[this]`. Conclude with `((hsu.unit⁻¹ : Sˣ) : S).2`. It suffices to derive a contradiction. Establish `hall : ∀ n : Ideal S, n.IsMaximal → s ∈ n` using `fun n hn => by`.

Rewrite using `[IsLocalRing.eq_maximalIdeal hn]`. Conclude with `(mem_maximalIdeal s).2 hsu`. Take `⟨N, -, hN⟩` from `ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := K.O) S s hall`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible K.O`. Rewrite `hN` using `[hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`.

Take `⟨t, ht⟩` from `hN`. Take `⟨z, hz⟩` from `hS _ t.2`. Establish `h1 : algebraMap K'.O K'.E (y ^ N * (ψ π * z)) = 1`. Use `congrArg (algebraMap S K'.E) ht` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, hs, ← IsScalarTower.algebraMap_apply]`.

Establish `h' : (t : K'.E) * algebraMap K.O K'.E π = x⁻¹ ^ N` using `this`. Rewrite using `[map_mul, map_pow, map_mul, hψ, hz, ← hx, mul_comm (algebraMap K.O K'.E π), h', ← mul_pow, mul_inv_cancel₀ hx0, one_pow]`. Establish `hu : IsUnit (ψ π)`. Establish `: y ^ N * (ψ π * z) = 1` using `hinj' (by rw [h1, map_one])`. Conclude with `IsUnit.of_mul_eq_one (z * y ^ N) (by rw [← this]; ring)`.

Establish `h2` using `GlobalTheory.UnitLemma.Orbit.val_unit (K := K') _ hu`. Rewrite `h2` using `[hψ]`. Establish `h3` using `hU.2.2.1 (algebraMap K.O K.E π)`. Express the relevant statement in the definitionally equal form `val K'.O (φ (algebraMap K.O K.E π)) = 0 at h2`. Rewrite `h2` using `[h3]`.

Conclude with `intO_val_ne_zero_of_mem K π hπ.ne_zero hπ.not_isUnit h2`.
-/
theorem intO : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O,
    @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  intro K K' d φ hU hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfr : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure K.O K'.E
  haveI : Module.Finite K.O S := IsIntegralClosure.finite K.O K.E K'.E S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain K.O K.E K'.E S
  haveI : IsFractionRing S K'.E := IsIntegralClosure.isFractionRing_of_finite_extension K.O K.E K'.E S
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := K.O) S
  have hinj : Function.Injective (algebraMap K.O S) :=
    algebraMap_injective_of_field_isFractionRing K.O S K.E K'.E
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField K.O (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1
    (inferInstance : IsDedekindDomain S)

  have hv : ∀ a : K.O, 0 ≤ val K'.O (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hU.2.2.1]; exact intO_val_algebraMap_nonneg K a
  choose ψf hψf using fun a : K.O => intO_lift_of_val_nonneg K' _ (hv a)
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let ψ : K.O →+* K'.O :=
    { toFun := ψf
      map_one' := hinj' (by rw [hψf]; simp)
      map_mul' := fun a b => hinj' (by simp [hψf])
      map_zero' := hinj' (by rw [hψf]; simp)
      map_add' := fun a b => hinj' (by simp [hψf]) }
  have hψ : ∀ a, algebraMap K'.O K'.E (ψ a) = algebraMap K.O K'.E a := fun a => hψf a

  have hS : ∀ t : K'.E, IsIntegral K.O t → ∃ z : K'.O, algebraMap K'.O K'.E z = t := by
    intro t ht
    have : IsIntegral K'.O t :=
      IsIntegral.map_of_comp_eq (T := K'.O) (U := K'.E) ψ (RingHom.id K'.E) (by ext a; exact hψ a) ht
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  set x := algebraMap K'.O K'.E y with hx
  rcases ValuationRing.isInteger_or_isInteger S x with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact s.2
  by_cases hx0 : x = 0
  · rw [hx0]; exact isIntegral_zero
  by_cases hsu : IsUnit s
  · have hu1 : ((hsu.unit⁻¹ : Sˣ) : S) * s = 1 := by
      have := hsu.unit.inv_mul; rwa [IsUnit.unit_spec] at this
    have e : algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) * algebraMap S K'.E s = 1 := by
      rw [← map_mul, hu1, map_one]
    have : x = algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) := by
      rw [eq_inv_of_mul_eq_one_left e, hs, inv_inv]
    rw [this]; exact ((hsu.unit⁻¹ : Sˣ) : S).2
  exfalso
  have hall : ∀ n : Ideal S, n.IsMaximal → s ∈ n := fun n hn => by
    rw [IsLocalRing.eq_maximalIdeal hn]; exact (mem_maximalIdeal s).2 hsu
  obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := K.O) S s hall
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hN
  obtain ⟨t, ht⟩ := hN
  obtain ⟨z, hz⟩ := hS _ t.2
  have h1 : algebraMap K'.O K'.E (y ^ N * (ψ π * z)) = 1 := by
    have := congrArg (algebraMap S K'.E) ht
    rw [map_mul, map_pow, hs, ← IsScalarTower.algebraMap_apply] at this
    have h' : (t : K'.E) * algebraMap K.O K'.E π = x⁻¹ ^ N := this
    rw [map_mul, map_pow, map_mul, hψ, hz, ← hx, mul_comm (algebraMap K.O K'.E π), h', ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow]
  have hu : IsUnit (ψ π) := by
    have : y ^ N * (ψ π * z) = 1 := hinj' (by rw [h1, map_one])
    exact IsUnit.of_mul_eq_one (z * y ^ N) (by rw [← this]; ring)
  have h2 := GlobalTheory.UnitLemma.Orbit.val_unit (K := K') _ hu
  rw [hψ] at h2
  have h3 := hU.2.2.1 (algebraMap K.O K.E π)
  change val K'.O (φ (algebraMap K.O K.E π)) = 0 at h2
  rw [h3] at h2
  exact intO_val_ne_zero_of_mem K π hπ.ne_zero hπ.not_isUnit h2

end GlobalTheory.UnitLemma.Unr
