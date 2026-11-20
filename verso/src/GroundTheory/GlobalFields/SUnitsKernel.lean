import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace SUnit

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha⟩` from `mem_integers_of_valuation_le_one (R := 𝓞 K) K (x : K) fun v => (h v).le`. Take `⟨b, hb⟩` from `mem_integers_of_valuation_le_one (R := 𝓞 K) K ((x⁻¹ : Kˣ) : K) fun v => by`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]`.

Establish `hab : a * b = 1`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[map_mul, ha, hb, map_one, Units.mul_inv]`. Establish `hba : b * a = 1` using `by rw [mul_comm, hab]`. Use `⟨⟨a, b, hab, hba⟩, ?_⟩` and prove the remaining obligations.

Use `ext`. Simplify using `[ha]`. Introduce and unpack `⟨u, rfl⟩ v`. Rewrite using `[← valuationOfNeZero_eq, valuation_of_unit_eq, WithZero.coe_one]`.
-/
theorem forall_valuation_eq_one_iff (x : Kˣ) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x : K) = 1) ↔
      x ∈ (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).range := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K (x : K) fun v => (h v).le
    obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 K) K ((x⁻¹ : Kˣ) : K) fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    have hba : b * a = 1 := by rw [mul_comm, hab]
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext
    simp [ha]
  · rintro ⟨u, rfl⟩ v
    rw [← valuationOfNeZero_eq, valuation_of_unit_eq, WithZero.coe_one]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

def ofUnits : (𝓞 K)ˣ →* S.unit K where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, fun v _ =>
    (forall_valuation_eq_one_iff _).mpr ⟨u, rfl⟩ v⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_ofUnits (u : (𝓞 K)ˣ) : ((ofUnits S u : Kˣ) : K) = algebraMap (𝓞 K) K u := rfl

/- English proof (translation)
Introduce `u u' h`. Establish `: ((ofUnits S u : Kˣ) : K) = ((ofUnits S u' : Kˣ) : K)` using `by rw [h]`. Simplify using `only [coe_ofUnits] at this`. Conclude with `Units.ext (IsFractionRing.injective (𝓞 K) K this)`.
-/
theorem ofUnits_injective : Function.Injective (ofUnits S (K := K)) := by
  intro u u' h
  have : ((ofUnits S u : Kˣ) : K) = ((ofUnits S u' : Kˣ) : K) := by rw [h]
  simp only [coe_ofUnits] at this
  exact Units.ext (IsFractionRing.injective (𝓞 K) K this)

def valuationVector : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => Multiplicative.toAdd (v.1.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ))
      map_zero' := by funext v; simp
      map_add' := fun x y => by funext v; simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valuationVector_apply (x : S.unit K) (v : S) :
    valuationVector S (Additive.ofMul x) v = Multiplicative.toAdd (v.1.valuationOfNeZero (x : Kˣ)) :=
  rfl

/- English proof (translation)
Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`. Distinguish the cases in `hv : v ∈ S`. Establish `h1` using `congrFun h ⟨v, hv⟩`.

Rewrite `h1` using `[valuationVector_apply, Pi.zero_apply, toAdd_eq_zero]`. Rewrite using `[← valuationOfNeZero_eq, h1, WithZero.coe_one]`. Conclude with `x.2 v hv`. Introduce `h`. Use function extensionality and compare the values at `v`.

Rewrite using `[valuationVector_apply, Pi.zero_apply, toAdd_eq_zero, ← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]`. Conclude with `h v.1`.
-/
theorem mem_ker_valuationVector_iff (x : S.unit K) :
    Additive.ofMul x ∈ LinearMap.ker (valuationVector S) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x : Kˣ) : K) = 1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have h1 := congrFun h ⟨v, hv⟩
      rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero] at h1
      rw [← valuationOfNeZero_eq, h1, WithZero.coe_one]
    · exact x.2 v hv
  · intro h
    funext v
    rw [valuationVector_apply, Pi.zero_apply, toAdd_eq_zero, ← WithZero.coe_inj,
      valuationOfNeZero_eq, WithZero.coe_one]
    exact h v.1

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← ofMul_toMul x, mem_ker_valuationVector_iff, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨u, hu⟩` from `(forall_valuation_eq_one_iff _).mp h`.

Conclude with `⟨Additive.ofMul u, by`. Express the relevant statement in the definitionally equal form `Additive.ofMul (ofUnits S u) = _`. Use `congr 1`. Conclude with `Subtype.ext hu⟩`. Introduce and unpack `⟨u, hu⟩`.

Establish `hx : ofUnits S u.toMul = x.toMul` using `congrArg Additive.toMul hu`. Rewrite using `[← hx]`. Conclude with `(forall_valuation_eq_one_iff _).mpr ⟨u.toMul, rfl⟩`.
-/
theorem ker_valuationVector :
    LinearMap.ker (valuationVector S) =
      LinearMap.range (ofUnits S).toAdditive.toIntLinearMap := by
  ext x
  rw [← ofMul_toMul x, mem_ker_valuationVector_iff, LinearMap.mem_range]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (forall_valuation_eq_one_iff _).mp h
    exact ⟨Additive.ofMul u, by
      change Additive.ofMul (ofUnits S u) = _
      congr 1
      exact Subtype.ext hu⟩
  · rintro ⟨u, hu⟩
    have hx : ofUnits S u.toMul = x.toMul := congrArg Additive.toMul hu
    rw [← hx]
    exact (forall_valuation_eq_one_iff _).mpr ⟨u.toMul, rfl⟩

def unitsEquivKer : Additive (𝓞 K)ˣ ≃ₗ[ℤ] LinearMap.ker (valuationVector S) :=
  (LinearEquiv.ofInjective (ofUnits S).toAdditive.toIntLinearMap
    (ofUnits_injective S)).trans (LinearEquiv.ofEq _ _ (ker_valuationVector S).symm)

end SUnit

end

end GroundTheory.Global
