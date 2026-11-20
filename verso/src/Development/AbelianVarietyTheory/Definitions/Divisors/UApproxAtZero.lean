import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType

noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
namespace GlobalTheory.UPoinc.UModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def valInt (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* OO p :=
  (RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

/- English proof (translation)
The claim follows from `RatModel.val_spMap_comp (OO p).subtype t.y (specializes_of_eq t.cen) (X₁.M.stalkEquiv z₁ a)`.
-/
theorem val_eq_valInt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : t.val a = (valInt t a : PadicAlgCl p) :=
  RatModel.val_spMap_comp (OO p).subtype t.y (specializes_of_eq t.cen) (X₁.M.stalkEquiv z₁ a)

/- English proof (translation)
Rewrite using `[val_eq_valInt]`. Establish `h : Valued.v (valInt t a : PadicAlgCl p) ≤ 1` using `(valInt t a).2`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_val_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖t.val a‖ ≤ 1 := by
  rw [val_eq_valInt]
  have h : Valued.v (valInt t a : PadicAlgCl p) ≤ 1 := (valInt t a).2
  exact_mod_cast h

/- English proof (translation)
Use `set x := algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ with hx`. Establish `h0 : x ≠ 0` using `fun h => t.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)`. Establish `h1 : 0 < ‖t.ι x‖` using `norm_pos_iff.2 ((map_ne_zero t.ι).2 h0)`. Establish `h2 : ‖t.ι x‖ < 1`. Assume the negation of the conclusion as `h`.

Establish `: ‖t.ι x⁻¹‖ ≤ 1`. Rewrite using `[map_inv₀, norm_inv]`. Conclude with `inv_le_one_of_one_le₀ (not_lt.1 h)`. Take `⟨v, hv⟩` from `(t.int _).1 this`. Use `t.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing t.T.V) ?_))` and prove the remaining obligations.

Rewrite using `[map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]`. Conclude with `neg_pos.2 (Real.log_neg h1 h2)`.
-/
theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  set x := algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ with hx
  have h0 : x ≠ 0 := fun h => t.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have h1 : 0 < ‖t.ι x‖ := norm_pos_iff.2 ((map_ne_zero t.ι).2 h0)
  have h2 : ‖t.ι x‖ < 1 := by
    by_contra h
    have : ‖t.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (t.int _).1 this
    refine t.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing t.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)

/- English proof (translation)
Introduce `p _ z₁ t₀ e` and use `⟨1, by simp [val_eq_valInt], fun t => Or.inl (by simp [val_eq_valInt])⟩`.
-/
theorem uApproxAt_zero (φ : GlobalTheory.LocM.InvFun (𝓞 E)) : UApproxAt X₁ φ 0 := fun p _ z₁ t₀ e =>
  ⟨1, by simp [val_eq_valInt], fun t => Or.inl (by simp [val_eq_valInt])⟩

end GlobalTheory.UPoinc.UModel
