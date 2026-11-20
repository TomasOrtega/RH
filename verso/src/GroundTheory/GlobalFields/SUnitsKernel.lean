import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace SUnit

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
