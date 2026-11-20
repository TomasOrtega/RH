import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace WeierstrassPointSeriesTail

def wTail {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Take `⟨u, rfl⟩` from `h`. Use `⟨C W.a₁ * u + C W.a₂ * X * u + C W.a₃ * X ^ j * u ^ 2 + C W.a₄ * X ^ (j + 1) * u ^ 2 + C W.a₆ * X ^ (2 * j + 1) * u ^ 3, ?_⟩` and prove the remaining obligations. Unfold `wTail`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wTail_dvd {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (k : ℕ) (hk : 1 ≤ k) (h : (X : PowerSeries R) ^ k ∣ w) :
    (X : PowerSeries R) ^ (k + 1) ∣ wTail W w := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, rfl⟩ := h
  refine ⟨C W.a₁ * u + C W.a₂ * X * u + C W.a₃ * X ^ j * u ^ 2 + C W.a₄ * X ^ (j + 1) * u ^ 2 +
    C W.a₆ * X ^ (2 * j + 1) * u ^ 3, ?_⟩
  unfold wTail
  ring

/- English proof (translation)
Establish `hsplit : w = X ^ 3 + wTail W w`. Unfold `wTail`. Use `conv_lhs => rw [hw.2]`. Expand and normalize the polynomial expressions, which then agree. Establish `d1 : (X : PowerSeries R) ^ 1 ∣ w`.

Rewrite using `[pow_one, PowerSeries.X_dvd_iff]`. Conclude with `hw.1`. Establish `d2 : (X : PowerSeries R) ^ 2 ∣ w`. Rewrite using `[hsplit]`. Conclude with `dvd_add (pow_dvd_pow X (by norm_num)) (wTail_dvd W w 1 le_rfl d1)`.

Establish `d3 : (X : PowerSeries R) ^ 3 ∣ w`. Rewrite using `[hsplit]`. Conclude with `dvd_add dvd_rfl (wTail_dvd W w 2 (by norm_num) d2)`. Take `⟨e, he⟩` from `wTail_dvd W w 3 (by norm_num) d3`. Conclude with `⟨e, by rw [hsplit, he]; ring⟩`.
-/
theorem factor {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (hw : WFixed W w) : ∃ e : PowerSeries R, w = X ^ 3 * (1 + X * e) := by
  have hsplit : w = X ^ 3 + wTail W w := by
    unfold wTail
    conv_lhs => rw [hw.2]
    ring
  have d1 : (X : PowerSeries R) ^ 1 ∣ w := by
    rw [pow_one, PowerSeries.X_dvd_iff]
    exact hw.1
  have d2 : (X : PowerSeries R) ^ 2 ∣ w := by
    rw [hsplit]
    exact dvd_add (pow_dvd_pow X (by norm_num)) (wTail_dvd W w 1 le_rfl d1)
  have d3 : (X : PowerSeries R) ^ 3 ∣ w := by
    rw [hsplit]
    exact dvd_add dvd_rfl (wTail_dvd W w 2 (by norm_num) d2)
  obtain ⟨e, he⟩ := wTail_dvd W w 3 (by norm_num) d3
  exact ⟨e, by rw [hsplit, he]; ring⟩

end WeierstrassPointSeriesTail

open WeierstrassPointSeriesTail in
/- English proof (translation)
Introduce `K _ W w hw σ _ s hs0 hs`. Establish `: IsDomain (MvPowerSeries σ K)` using `NoZeroDivisors.to_isDomain _`. Establish `hsub : PowerSeries.HasSubst s` using `PowerSeries.HasSubst.of_constantCoeff_zero hs0`. Establish `hE : w.subst s = s ^ 3 + MvPowerSeries.C W.a₁ * s * w.subst s + MvPowerSeries.C W.a₂ * s ^ 2 * w.subst s + MvPowerSeries.C W.a₃ * (w.subst s) ^ 2 + MvPowerSeries.C W.a₄ * s * (w.subst s) ^ 2 + MvPowerSeries.C W.a₆ * (w.subst s) ^ 3` using `by conv_lhs => rw [hw.2]`. Simplify using `only [PowerSeries.subst_add hsub, PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub, PowerSeries.subst_X hsub, PowerSeries.subst_C]`.

Take `⟨e, he⟩` from `factor W w hw`. Establish `hfac : w.subst s = s ^ 3 * (1 + s * e.subst s)`. Rewrite using `[← PowerSeries.coe_substAlgHom hsub, he]`. Simplify using `[PowerSeries.substAlgHom_X]`. Establish `hwc : MvPowerSeries.constantCoeff (w.subst s) = 0`.

Rewrite using `[hfac]`. Simplify using `[hs0]`. Establish `hws0 : w.subst s ≠ 0`. Rewrite using `[hfac]`. Use `mul_ne_zero (pow_ne_zero 3 hs) (fun h0 => ?_)` and prove the remaining obligations.

Use `congrArg MvPowerSeries.constantCoeff h0` as an intermediate fact. Simplify using `[hs0] at this`. Establish `hinj` using `IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))`. Establish `hV : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0` using `(map_ne_zero_iff _ hinj).mpr hws0`. Establish `hC : ∀ a : K, algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries σ K)) a` using `fun a => (IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) a).symm`.

Establish `hE'` using `congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hE`. Simplify using `only [map_add, map_mul, map_pow, hC] at hE'`. Establish `hx : xOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) = algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s`. Simplify using `only [xOf]`. Conclude with `div_mul_cancel₀ _ hV`.

Establish `hy : yOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) = -1`. Simplify using `only [yOf]`. Rewrite using `[div_mul_cancel₀ _ hV]`. Use `set Z := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s`. Use `set V := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)`.

Use `set x := xOf w s`. Use `set y := yOf w s`. Use `set A₁ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₁`. Use `set A₂ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₂`. Use `set A₃ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₃`.

Use `set A₄ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₄`. Use `set A₆ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₆`. Rewrite using `[WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ (pow_ne_zero 3 hV)` to reduce the goal to its premises. Take the linear combination `hE' + (V * (y * V - 1) + A₁ * V * Z + A₃ * V ^ 2) * hy + (A₁ * V * (y * V) - ((x * V) ^ 2 + (x * V) * Z + Z ^ 2) - A₂ * V * (x * V + Z) - A₄ * V ^ 2) * hx`. Assume the negation of the conclusion as `hcon push Not at hcon`. Take `⟨hP, hQ⟩` from `hcon`. Establish `hD0 : (1 - MvPowerSeries.C W.a₁ * s - 2 * MvPowerSeries.C W.a₃ * w.subst s - MvPowerSeries.C W.a₂ * s ^ 2 - 2 * MvPowerSeries.C W.a₄ * s * w.subst s - 3 * MvPowerSeries.C W.a₆ * (w.subst s) ^ 2 : MvPowerSeries σ K) ≠ 0`.

Introduce `h0`. Use `congrArg MvPowerSeries.constantCoeff h0` as an intermediate fact. Simplify using `[hs0, hwc] at this`. Apply `hD0` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Apply `(mul_eq_zero.mp _).resolve_right hV` to reduce the goal to its premises. Simplify using `only [map_sub, map_mul, map_pow, map_one, map_ofNat, hC]`. Take the linear combination `V ^ 2 * hQ - Z * V ^ 2 * hP + 3 * hE' + (-2 * V + Z * A₁ * V) * hy + (-A₁ * V - 3 * Z * (x * V + Z) - 2 * A₂ * Z * V) * hx`.
-/
theorem wSeriesNonsingularPoint_holds : WPoint := by
  intro K _ W w hw σ _ s hs0 hs
  have : IsDomain (MvPowerSeries σ K) := NoZeroDivisors.to_isDomain _
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have hE : w.subst s = s ^ 3 + MvPowerSeries.C W.a₁ * s * w.subst s +
      MvPowerSeries.C W.a₂ * s ^ 2 * w.subst s + MvPowerSeries.C W.a₃ * (w.subst s) ^ 2 +
      MvPowerSeries.C W.a₄ * s * (w.subst s) ^ 2 + MvPowerSeries.C W.a₆ * (w.subst s) ^ 3 := by
    conv_lhs => rw [hw.2]
    simp only [PowerSeries.subst_add hsub, PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub,
      PowerSeries.subst_X hsub, PowerSeries.subst_C]
  obtain ⟨e, he⟩ := factor W w hw
  have hfac : w.subst s = s ^ 3 * (1 + s * e.subst s) := by
    rw [← PowerSeries.coe_substAlgHom hsub, he]
    simp [PowerSeries.substAlgHom_X]
  have hwc : MvPowerSeries.constantCoeff (w.subst s) = 0 := by
    rw [hfac]
    simp [hs0]
  have hws0 : w.subst s ≠ 0 := by
    rw [hfac]
    refine mul_ne_zero (pow_ne_zero 3 hs) (fun h0 => ?_)
    have := congrArg MvPowerSeries.constantCoeff h0
    simp [hs0] at this
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have hV : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hws0
  have hC : ∀ a : K, algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries σ K)) a := fun a =>
    (IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) a).symm
  have hE' := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hE
  simp only [map_add, map_mul, map_pow, hC] at hE'
  have hx : xOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s := by
    simp only [xOf]
    exact div_mul_cancel₀ _ hV
  have hy : yOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) =
      -1 := by
    simp only [yOf]
    rw [div_mul_cancel₀ _ hV]
  set Z := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s
  set V := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)
  set x := xOf w s
  set y := yOf w s
  set A₁ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₁
  set A₂ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₂
  set A₃ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₃
  set A₄ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₄
  set A₆ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₆
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  refine ⟨?_, ?_⟩
  · apply mul_left_cancel₀ (pow_ne_zero 3 hV)
    linear_combination hE' + (V * (y * V - 1) + A₁ * V * Z + A₃ * V ^ 2) * hy +
      (A₁ * V * (y * V) - ((x * V) ^ 2 + (x * V) * Z + Z ^ 2) - A₂ * V * (x * V + Z) - A₄ * V ^ 2) * hx
  · by_contra hcon
    push Not at hcon
    obtain ⟨hP, hQ⟩ := hcon
    have hD0 : (1 - MvPowerSeries.C W.a₁ * s - 2 * MvPowerSeries.C W.a₃ * w.subst s -
        MvPowerSeries.C W.a₂ * s ^ 2 - 2 * MvPowerSeries.C W.a₄ * s * w.subst s -
        3 * MvPowerSeries.C W.a₆ * (w.subst s) ^ 2 : MvPowerSeries σ K) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff h0
      simp [hs0, hwc] at this
    apply hD0
    apply hinj
    rw [map_zero]
    apply (mul_eq_zero.mp _).resolve_right hV
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, hC]
    linear_combination V ^ 2 * hQ - Z * V ^ 2 * hP + 3 * hE' + (-2 * V + Z * A₁ * V) * hy +
      (-A₁ * V - 3 * Z * (x * V + Z) - 2 * A₂ * Z * V) * hx

end Formalism.ELL
