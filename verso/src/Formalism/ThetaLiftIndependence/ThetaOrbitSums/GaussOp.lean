import Formalism.ThetaLiftIndependence.Statement

open scoped BigOperators

namespace Formalism.ThetaLiftIndependence

namespace GaussOperatorLemmas

variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/- English proof (translation)
Rewrite using `[Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left, Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]`. Conclude with `Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)`.
-/
theorem sum_units_eq_sub {M : Type*} [AddCommGroup M] (f : 𝔽 → M) :
    ∑ u : 𝔽ˣ, f u = ∑ x, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left,
    Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)

/- English proof (translation)
Rewrite using `[sum_units_eq_sub (fun x => ψ (a * x))]`. Simplify using `only [mul_zero, AddChar.map_zero_eq_one]`. Use `congr 1`. Establish `h` using `AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)`. Rewrite `h` using `[Nat.cast_ite, Nat.cast_zero]`.

Rewrite using `[← h]`. Conclude with `Finset.sum_congr rfl (fun x _ => by rw [mul_comm])`.
-/
theorem sum_units_char (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (a : 𝔽) :
    ∑ d : 𝔽ˣ, ψ (a * d) = (if a = 0 then (Fintype.card 𝔽 : ℂ) else 0) - 1 := by
  rw [sum_units_eq_sub (fun x => ψ (a * x))]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  congr 1
  have h := AddChar.sum_mulShift a (AddChar.IsPrimitive.of_ne_one hψ)
  rw [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun x _ => by rw [mul_comm])

/- English proof (translation)
Repeatedly rewrite using `[sum_units_char ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero, sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem core (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) (v : V) (hv : ∑ c : 𝔽ˣ, ρ c v = 0) :
    ∑ e : 𝔽ˣ, (∑ d : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d)) • ρ e v = (Fintype.card 𝔽 : ℂ) • v := by
  simp_rw [sum_units_char ψ hψ, sub_smul, one_smul, Finset.sum_sub_distrib, hv, sub_zero,
    sub_eq_zero, Units.val_eq_one, ite_smul, zero_smul]
  simp

end GaussOperatorLemmas

open GaussOperatorLemmas in
/- English proof (translation)
Introduce `𝔽 V _ _ _ _ _ ψ ρ hψ v hv`. Establish `hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w`. Introduce `a b w`. Rewrite using `[map_mul, Module.End.mul_apply]`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hρ]`. Establish `step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v = ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v`. Introduce `d`. Rewrite using `[Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d) (fun e => ψ (-(d : 𝔽)) • ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun e => rfl)]`. Use `Finset.sum_congr rfl (fun e _ => ?_)` and prove the remaining obligations.

Rewrite using `[smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun d _ => step d), Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`.

Conclude with `core ψ hψ ρ v hv`. Simplify using `only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hρ]`. Repeatedly rewrite using `[Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Establish `step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v = ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v`.

Introduce `c`. Rewrite using `[← Fintype.sum_equiv (Equiv.mulLeft c) (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun e => rfl)]`. Use `Finset.sum_congr rfl (fun e _ => ?_)` and prove the remaining obligations. Rewrite using `[inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.sum_smul]`. Conclude with `core ψ hψ ρ v hv`.
-/
theorem gaussOp_eq : GaussOp := by
  intro 𝔽 V _ _ _ _ _ ψ ρ hψ v hv
  have hρ : ∀ (a b : 𝔽ˣ) (w : V), ρ a (ρ b w) = ρ (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  constructor
  · simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    have step : ∀ d : 𝔽ˣ, ψ (-(d : 𝔽)) • ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ (c * d⁻¹) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * d) • ρ e v := by
      intro d
      rw [Finset.smul_sum, ← Fintype.sum_equiv (Equiv.mulRight d) (fun e => ψ (-(d : 𝔽)) •
        ψ ((e * d : 𝔽ˣ) : 𝔽) • ρ (e * d * d⁻¹) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [smul_smul, mul_inv_cancel_right, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun d _ => step d), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv
  · simp only [Formalism.ThetaLiftIndependence.gaussOp, gaussOpDual, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, hρ]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have step : ∀ c : 𝔽ˣ, ∑ d : 𝔽ˣ, (ψ (d : 𝔽) * ψ (-(c : 𝔽))) • ρ (c⁻¹ * d) v =
        ∑ e : 𝔽ˣ, ψ (((e : 𝔽) - 1) * c) • ρ e v := by
      intro c
      rw [← Fintype.sum_equiv (Equiv.mulLeft c) (fun e => (ψ ((c * e : 𝔽ˣ) : 𝔽) *
        ψ (-(c : 𝔽))) • ρ (c⁻¹ * (c * e)) v) _ (fun e => rfl)]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [inv_mul_cancel_left, ← AddChar.map_add_eq_mul, Units.val_mul]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact core ψ hψ ρ v hv

end Formalism.ThetaLiftIndependence
