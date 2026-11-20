import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupLaw

namespace GroundTheory.Arith.Abelian

noncomputable section

section Neg

variable {A : Type*} [CommRing A] (V : WeierstrassCurve A)

/- English proof (translation)
Unfold `zwPoly`. Take the linear combination `(-e * w * (e + 1)) * he`.
-/
theorem zwPoly_neg_mul {z w e : A} (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = -e ^ 3 * zwPoly V z w := by
  unfold zwPoly
  linear_combination (-e * w * (e + 1)) * he

end Neg

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

section Apply

variable {T : Type*} [CommRing T] [Algebra R T] (ψ : MvPowerSeries (Fin 2) R →ₐ[R] T)

/- English proof (translation)
Establish `: MvPowerSeries.C r = algebraMap R (MvPowerSeries (Fin 2) R) r`. Rewrite using `[MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[this, ψ.commutes]`.
-/
theorem algHom_C (r : R) : ψ (MvPowerSeries.C r) = algebraMap R T r := by
  have : MvPowerSeries.C r = algebraMap R (MvPowerSeries (Fin 2) R) r := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [this, ψ.commutes]

/- English proof (translation)
Rewrite using `[WeierstrassCurve.map_map]`. Use `congr 1`. Use extensionality with `r`. Conclude with `algHom_C ψ r`.
-/
theorem map_C_algHom :
    (W.map (MvPowerSeries.C (σ := Fin 2))).map (ψ : MvPowerSeries (Fin 2) R →+* T) =
      W.map (algebraMap R T) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  ext r
  exact algHom_C ψ r

/- English proof (translation)
Rewrite using `[wAt_X_zero_eq, map_add, map_mul]`.
-/
theorem apply_wAt_X_zero :
    ψ (wAt W (MvPowerSeries.X 0)) = ψ (addSlope W) * ψ (MvPowerSeries.X 0) + ψ (addIntercept W) := by
  rw [wAt_X_zero_eq, map_add, map_mul]

/- English proof (translation)
Rewrite using `[wAt_X_one_eq, map_add, map_mul]`.
-/
theorem apply_wAt_X_one :
    ψ (wAt W (MvPowerSeries.X 1)) = ψ (addSlope W) * ψ (MvPowerSeries.X 1) + ψ (addIntercept W) := by
  rw [wAt_X_one_eq, map_add, map_mul]

/- English proof (translation)
Use `congrArg (ψ : MvPowerSeries (Fin 2) R →+* T) (zwPoly_wAt W (MvPowerSeries.constantCoeff_X (R := R) i))` as an intermediate fact. Rewrite `this` using `[map_zwPoly, map_zero, map_C_algHom]`. Then use the resulting hypothesis.
-/
theorem zwPoly_apply_wAt_X (i : Fin 2) :
    zwPoly (W.map (algebraMap R T)) (ψ (MvPowerSeries.X i)) (ψ (wAt W (MvPowerSeries.X i))) = 0 := by
  have := congrArg (ψ : MvPowerSeries (Fin 2) R →+* T)
    (zwPoly_wAt W (MvPowerSeries.constantCoeff_X (R := R) i))
  rwa [map_zwPoly, map_zero, map_C_algHom] at this

/- English proof (translation)
Use `congrArg (ψ : MvPowerSeries (Fin 2) R →+* T) (mul_invOfUnit_one (constantCoeff_secantB W))` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, map_secantB, map_C_algHom]`. Then use the resulting hypothesis.
-/
theorem secantB_apply_mul :
    secantB (W.map (algebraMap R T)) (ψ (addSlope W)) *
      ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) = 1 := by
  have := congrArg (ψ : MvPowerSeries (Fin 2) R →+* T) (mul_invOfUnit_one (constantCoeff_secantB W))
  rwa [map_mul, map_one, map_secantB, map_C_algHom] at this

/- English proof (translation)
Establish `h` using `map_secantA (W.map (MvPowerSeries.C (σ := Fin 2))) (ψ : MvPowerSeries (Fin 2) R →+* T) (addSlope W) (addIntercept W)`. Rewrite `h` using `[map_C_algHom]`. Establish `h' : ψ (secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W)) = secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W))` using `h`. Rewrite using `[thirdZ, map_sub, map_sub, map_neg, map_mul, h']`.
-/
theorem apply_thirdZ :
    ψ (thirdZ W) = -ψ (MvPowerSeries.X 0) - ψ (MvPowerSeries.X 1) -
      secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W)) *
        ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) := by
  have h := map_secantA (W.map (MvPowerSeries.C (σ := Fin 2))) (ψ : MvPowerSeries (Fin 2) R →+* T)
    (addSlope W) (addIntercept W)
  rw [map_C_algHom] at h
  have h' : ψ (secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W)) =
      secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W)) := h
  rw [thirdZ, map_sub, map_sub, map_neg, map_mul, h']

/- English proof (translation)
Rewrite using `[thirdW, map_add, map_mul]`.
-/
theorem apply_thirdW : ψ (thirdW W) = ψ (addSlope W) * ψ (thirdZ W) + ψ (addIntercept W) := by
  rw [thirdW, map_add, map_mul]

/- English proof (translation)
Use `congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, negDen, map_sub, map_sub, map_one, map_mul, map_mul, algHom_C, algHom_C]`. Then use the resulting hypothesis.
-/
theorem negDen_apply_mul :
    (1 - algebraMap R T W.a₁ * ψ (thirdZ W) - algebraMap R T W.a₃ * ψ (thirdW W)) *
      ψ (MvPowerSeries.invOfUnit (negDen W) 1) = 1 := by
  have := congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))
  rwa [map_mul, map_one, negDen, map_sub, map_sub, map_one, map_mul, map_mul, algHom_C,
    algHom_C] at this

/- English proof (translation)
Rewrite using `[addSeries, map_mul, map_neg]`.
-/
theorem apply_addSeries :
    ψ (addSeries W) = -ψ (thirdZ W) * ψ (MvPowerSeries.invOfUnit (negDen W) 1) := by
  rw [addSeries, map_mul, map_neg]

end Apply

section Inverse

def invDen : PowerSeries R :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W

/- English proof (translation)
Establish `h : MvPowerSeries.constantCoeff (formalW W) = 0` using `constantCoeff_formalW W`. Simplify using `[invDen, PowerSeries.C_apply, h, PowerSeries.X]`.
-/
theorem constantCoeff_invDen : MvPowerSeries.constantCoeff (invDen W) = 1 := by
  have h : MvPowerSeries.constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  simp [invDen, PowerSeries.C_apply, h, PowerSeries.X]

def invSeries : PowerSeries R :=
  -PowerSeries.X * MvPowerSeries.invOfUnit (invDen W) 1

/- English proof (translation)
Simplify using `[invSeries, PowerSeries.X]`.
-/
theorem constantCoeff_invSeries : MvPowerSeries.constantCoeff (invSeries W) = 0 := by
  simp [invSeries, PowerSeries.X]

/- English proof (translation)
The claim follows from `PowerSeries.X_subst _`.
-/
theorem wAt_X_unit : wAt W (PowerSeries.X : PowerSeries R) = formalW W :=
  PowerSeries.X_subst _

/- English proof (translation)
Use `set e := MvPowerSeries.invOfUnit (invDen W) 1 with he_def`. Establish `he : (1 - (W.map MvPowerSeries.C).a₁ * (PowerSeries.X : PowerSeries R) - (W.map MvPowerSeries.C).a₃ * formalW W) * e = 1` using `mul_invOfUnit_one (constantCoeff_invDen W)`. Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0` using `PowerSeries.constantCoeff_X`. Establish `h0 : zwPoly (W.map MvPowerSeries.C) PowerSeries.X (formalW W) = 0`. Use `zwPoly_wAt W hX` as an intermediate fact.

Rewrite `this` using `[wAt_X_unit]`. Then use the resulting hypothesis. Establish `hneg` using `zwPoly_neg_mul (W.map MvPowerSeries.C) he`. Rewrite `hneg` using `[h0, mul_zero]`. Establish `hi` using `constantCoeff_invSeries W`. Use `eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hi) hneg ?_` and prove the remaining obligations.

Use `MvPowerSeries.isUnit_iff_constantCoeff.2 ?_` and prove the remaining obligations. Establish `hw : MvPowerSeries.constantCoeff (formalW W) = 0` using `constantCoeff_formalW W`. Simplify using `[hi, constantCoeff_wAt W hi, hw]`.
-/
theorem wAt_invSeries :
    wAt W (invSeries W) = -formalW W * MvPowerSeries.invOfUnit (invDen W) 1 := by
  set e := MvPowerSeries.invOfUnit (invDen W) 1 with he_def
  have he : (1 - (W.map MvPowerSeries.C).a₁ * (PowerSeries.X : PowerSeries R) -
      (W.map MvPowerSeries.C).a₃ * formalW W) * e = 1 :=
    mul_invOfUnit_one (constantCoeff_invDen W)
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
    PowerSeries.constantCoeff_X
  have h0 : zwPoly (W.map MvPowerSeries.C) PowerSeries.X (formalW W) = 0 := by
    have := zwPoly_wAt W hX
    rwa [wAt_X_unit] at this
  have hneg := zwPoly_neg_mul (W.map MvPowerSeries.C) he
  rw [h0, mul_zero] at hneg
  have hi := constantCoeff_invSeries W
  refine eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hi) hneg ?_
  refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
  have hw : MvPowerSeries.constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  simp [hi, constantCoeff_wAt W hi, hw]

/- English proof (translation)
Establish `h : MvPowerSeries.map f (formalW W) = formalW (W.map f)` using `map_formalW W f`. Simplify using `only [invDen, map_sub, map_one, map_mul, h, PowerSeries.C_apply, MvPowerSeries.map_C, PowerSeries.X, MvPowerSeries.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]`.
-/
theorem map_invDen {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f (invDen W) = invDen (W.map f) := by
  have h : MvPowerSeries.map f (formalW W) = formalW (W.map f) := map_formalW W f
  simp only [invDen, map_sub, map_one, map_mul, h, PowerSeries.C_apply, MvPowerSeries.map_C,
    PowerSeries.X, MvPowerSeries.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/- English proof (translation)
Rewrite using `[invSeries, map_mul, map_neg, map_invOfUnit_one f (constantCoeff_invDen W), map_invDen, invSeries, PowerSeries.X, MvPowerSeries.map_X]`. Both sides reduce to the same expression.
-/
theorem map_invSeries {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f (invSeries W) = invSeries (W.map f) := by
  rw [invSeries, map_mul, map_neg, map_invOfUnit_one f (constantCoeff_invDen W), map_invDen,
    invSeries, PowerSeries.X, MvPowerSeries.map_X]
  rfl

/- English proof (translation)
Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0` using `PowerSeries.constantCoeff_X`. Establish `hi` using `constantCoeff_invSeries W`. Establish `hab` using `GroundTheory.LocalField.FormalGroup.hasSubst_pair hX hi`. Use `set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef`. Establish `hψ : ∀ f, MvPowerSeries.subst ![PowerSeries.X, invSeries W] f = ψ f` using `fun f => by`.

Rewrite using `[hψdef, MvPowerSeries.coe_substAlgHom]`. Establish `ψX0 : ψ (MvPowerSeries.X 0) = PowerSeries.X`. Rewrite using `[← hψ, MvPowerSeries.subst_X hab]`. Both sides reduce to the same expression. Establish `ψX1 : ψ (MvPowerSeries.X 1) = invSeries W`.

Rewrite using `[← hψ, MvPowerSeries.subst_X hab]`. Both sides reduce to the same expression. Establish `ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![PowerSeries.X, invSeries W] i)` using `fun i => by`. Rewrite using `[← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i) hab, MvPowerSeries.subst_X hab, wAt]`. Use `set V := W.map (algebraMap R (PowerSeries R)) with hV`.

Use `set u : PowerSeries R := PowerSeries.X with hu`. Use `set e := MvPowerSeries.invOfUnit (invDen W) 1 with he`. Use `set w := formalW W with hw`. Use `set l := ψ (addSlope W) with hl`. Use `set n := ψ (addIntercept W) with hn`.

Use `set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb`. Establish `hu' : invSeries W = -u * e` using `rfl`. Establish `r₁ : w = l * u + n`. Use `apply_wAt_X_zero W ψ` as an intermediate fact. Rewrite `this` using `[ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit]`. Then use the resulting hypothesis.

Establish `r₂ : -w * e = l * invSeries W + n`. Use `apply_wAt_X_one W ψ` as an intermediate fact. Rewrite `this` using `[ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries]`. Then use the resulting hypothesis. Establish `he1 : e + 1 ≠ 0`. Introduce `h`.

Use `congrArg MvPowerSeries.constantCoeff h` as an intermediate fact. Simplify using `[he, MvPowerSeries.constantCoeff_invOfUnit] at this`. Conclude with `h2 (by linear_combination this)`. Establish `hlu : l * u = w`. Establish `h : (e + 1) * (l * u - w) = 0` using `by rw [hu'] at r₂; linear_combination r₂ - r₁`.

Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left he1)`. Establish `hn0 : n = 0` using `by linear_combination -r₁ - hlu`. Establish `z₁ : zwPoly V u w = 0`. Use `zwPoly_apply_wAt_X W ψ 0` as an intermediate fact. Rewrite `this` using `[ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit]`. Then use the resulting hypothesis.

Establish `z₂ : zwPoly V (invSeries W) (-w * e) = 0`. Use `zwPoly_apply_wAt_X W ψ 1` as an intermediate fact. Rewrite `this` using `[ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries]`. Then use the resulting hypothesis. Establish `hcub : ∀ t, zwPoly V t (l * t) = t * (secantB V l * t ^ 2 + secantA V l n * t - l)`. Introduce `t`.

Simplify using `only [zwPoly, secantB, secantA, hn0]`. Expand and normalize the polynomial expressions, which then agree. Establish `q₁ : u * (secantB V l * u ^ 2 + secantA V l n * u - l) = 0`. Rewrite using `[← hcub, hlu, z₁]`. Establish `q₂ : invSeries W * (secantB V l * invSeries W ^ 2 + secantA V l n * invSeries W - l) = 0`.

Rewrite using `[← hcub, ← z₂]`. Use `congr 1`. Take the linear combination `-r₂ - hn0`. Establish `hu0 : u ≠ 0` using `PowerSeries.X_ne_zero`. Establish `heu : IsUnit e`.

Use `MvPowerSeries.isUnit_iff_constantCoeff.2 ?_` and prove the remaining obligations. Simplify using `[he, MvPowerSeries.constantCoeff_invOfUnit]`. Establish `hu'0 : invSeries W ≠ 0`. Rewrite using `[hu']`. Conclude with `mul_ne_zero (neg_ne_zero.2 hu0) heu.ne_zero`.

Establish `p₁` using `(mul_eq_zero.1 q₁).resolve_left hu0`. Establish `p₂` using `(mul_eq_zero.1 q₂).resolve_left hu'0`. Establish `hd : u - invSeries W ≠ 0`. Rewrite using `[hu', show u - -u * e = u * (e + 1) by ring]`. Conclude with `mul_ne_zero hu0 he1`.

Establish `hs : secantB V l * (u + invSeries W) + secantA V l n = 0`. Establish `: (u - invSeries W) * (secantB V l * (u + invSeries W) + secantA V l n) = 0`. Take the linear combination `p₁ - p₂`. Conclude with `(mul_eq_zero.1 this).resolve_left hd`. Establish `rb` using `secantB_apply_mul W ψ`.

Establish `hz : ψ (thirdZ W) = 0`. Rewrite using `[apply_thirdZ, ψX0, ψX1]`. Take the linear combination `(u + invSeries W) * rb - b * hs`. Rewrite using `[hψ, apply_addSeries, hz, neg_zero, zero_mul]`.
-/
theorem subst_X_invSeries_of_isDomain [IsDomain R] (h2 : (2 : R) ≠ 0) :
    MvPowerSeries.subst ![PowerSeries.X, invSeries W] (addSeries W) = (0 : PowerSeries R) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
    PowerSeries.constantCoeff_X
  have hi := constantCoeff_invSeries W
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair hX hi
  set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef
  have hψ : ∀ f, MvPowerSeries.subst ![PowerSeries.X, invSeries W] f = ψ f := fun f => by
    rw [hψdef, MvPowerSeries.coe_substAlgHom]
  have ψX0 : ψ (MvPowerSeries.X 0) = PowerSeries.X := by
    rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψX1 : ψ (MvPowerSeries.X 1) = invSeries W := by
    rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![PowerSeries.X, invSeries W] i) :=
    fun i => by
      rw [← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst
        (PowerSeries.HasSubst.X i) hab, MvPowerSeries.subst_X hab, wAt]
  set V := W.map (algebraMap R (PowerSeries R)) with hV
  set u : PowerSeries R := PowerSeries.X with hu
  set e := MvPowerSeries.invOfUnit (invDen W) 1 with he
  set w := formalW W with hw
  set l := ψ (addSlope W) with hl
  set n := ψ (addIntercept W) with hn
  set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb
  have hu' : invSeries W = -u * e := rfl
  have r₁ : w = l * u + n := by
    have := apply_wAt_X_zero W ψ
    rwa [ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit] at this
  have r₂ : -w * e = l * invSeries W + n := by
    have := apply_wAt_X_one W ψ
    rwa [ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries] at this
  have he1 : e + 1 ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    simp [he, MvPowerSeries.constantCoeff_invOfUnit] at this
    exact h2 (by linear_combination this)
  have hlu : l * u = w := by
    have h : (e + 1) * (l * u - w) = 0 := by rw [hu'] at r₂; linear_combination r₂ - r₁
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left he1)
  have hn0 : n = 0 := by linear_combination -r₁ - hlu
  have z₁ : zwPoly V u w = 0 := by
    have := zwPoly_apply_wAt_X W ψ 0
    rwa [ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit] at this
  have z₂ : zwPoly V (invSeries W) (-w * e) = 0 := by
    have := zwPoly_apply_wAt_X W ψ 1
    rwa [ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries] at this
  have hcub : ∀ t, zwPoly V t (l * t) =
      t * (secantB V l * t ^ 2 + secantA V l n * t - l) := by
    intro t; simp only [zwPoly, secantB, secantA, hn0]; ring
  have q₁ : u * (secantB V l * u ^ 2 + secantA V l n * u - l) = 0 := by
    rw [← hcub, hlu, z₁]
  have q₂ : invSeries W * (secantB V l * invSeries W ^ 2 + secantA V l n * invSeries W - l) = 0 := by
    rw [← hcub, ← z₂]; congr 1; linear_combination -r₂ - hn0
  have hu0 : u ≠ 0 := PowerSeries.X_ne_zero
  have heu : IsUnit e := by
    refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
    simp [he, MvPowerSeries.constantCoeff_invOfUnit]
  have hu'0 : invSeries W ≠ 0 := by
    rw [hu']; exact mul_ne_zero (neg_ne_zero.2 hu0) heu.ne_zero
  have p₁ := (mul_eq_zero.1 q₁).resolve_left hu0
  have p₂ := (mul_eq_zero.1 q₂).resolve_left hu'0
  have hd : u - invSeries W ≠ 0 := by
    rw [hu', show u - -u * e = u * (e + 1) by ring]
    exact mul_ne_zero hu0 he1
  have hs : secantB V l * (u + invSeries W) + secantA V l n = 0 := by
    have : (u - invSeries W) * (secantB V l * (u + invSeries W) + secantA V l n) = 0 := by
      linear_combination p₁ - p₂
    exact (mul_eq_zero.1 this).resolve_left hd
  have rb := secantB_apply_mul W ψ
  have hz : ψ (thirdZ W) = 0 := by
    rw [apply_thirdZ, ψX0, ψX1]
    linear_combination (u + invSeries W) * rb - b * hs
  rw [hψ, apply_addSeries, hz, neg_zero, zero_mul]

/- English proof (translation)
Introduce `h`. Use `congrArg (MvPolynomial.eval (0 : Fin 5 → ℤ)) h` as an intermediate fact. Rewrite `this` using `[map_ofNat, map_zero]`. Evaluate the numerical expressions using `at this`.
-/
theorem two_ne_zero_univ : (2 : MvPolynomial (Fin 5) ℤ) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (0 : Fin 5 → ℤ)) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

/- English proof (translation)
Establish `h` using `congrArg (MvPowerSeries.map (univMap W)) (subst_X_invSeries_of_isDomain univCurve two_ne_zero_univ)`. Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries (MvPolynomial (Fin 5) ℤ)) = 0` using `PowerSeries.constantCoeff_X`. Establish `hab` using `GroundTheory.LocalField.FormalGroup.hasSubst_pair hX (constantCoeff_invSeries univCurve)`. Rewrite `h` using `[MvPowerSeries.map_subst hab, map_zero]`. Rewrite using `[← h, addSeries_eq_map]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `[PowerSeries.X, MvPowerSeries.map_X]`. Simplify using `[map_invSeries, univCurve_map]`.
-/
theorem subst_X_invSeries :
    MvPowerSeries.subst ![PowerSeries.X, invSeries W] (addSeries W) = (0 : PowerSeries R) := by
  have h := congrArg (MvPowerSeries.map (univMap W))
    (subst_X_invSeries_of_isDomain univCurve two_ne_zero_univ)
  have hX : MvPowerSeries.constantCoeff
      (PowerSeries.X : PowerSeries (MvPolynomial (Fin 5) ℤ)) = 0 := PowerSeries.constantCoeff_X
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair hX (constantCoeff_invSeries univCurve)
  rw [MvPowerSeries.map_subst hab, map_zero] at h
  rw [← h, addSeries_eq_map]
  congr 1
  funext i
  fin_cases i
  · simp [PowerSeries.X, MvPowerSeries.map_X]
  · simp [map_invSeries, univCurve_map]

/- English proof (translation)
The claim follows from `(GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero _ (constantCoeff_invSeries W) (subst_X_invSeries W)).symm`.
-/
theorem inv_formalGroup : GroundTheory.LocalField.FormalGroup.inv (formalGroup W) = invSeries W :=
  (GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero _ (constantCoeff_invSeries W)
    (subst_X_invSeries W)).symm

end Inverse

end

end GroundTheory.Arith.Abelian
