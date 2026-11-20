import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Member.TameDivOrd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[pow_zero, _root_.mul_one, Nat.cast_zero]`. Conclude with `(_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).map_unit u`. Consider the case `succ m ih`.

Rewrite using `[pow_succ, ← _root_.mul_assoc, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul, ih, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw_uniformiser h0 ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma ord_vw_unit_mul_uniformiser_pow {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {ϖ : W} (hϖ : Irreducible ϖ) (h0 : ϖ ≠ 0) (u : Wˣ) (m : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun
      (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m) = m := by
  induction m with
  | zero =>
    rw [pow_zero, _root_.mul_one, Nat.cast_zero]
    exact (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).map_unit u
  | succ m ih =>
    rw [pow_succ, ← _root_.mul_assoc, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul, ih,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw_uniformiser h0
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
    push_cast
    ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
/- English proof (translation)
Break down `lt_trichotomy a 1 with h1 | h1 | h1` into its components or cases. Conclude with `absurd h (pow_lt_one₀ zero_le' h1 hk).ne`. Conclude with `h1`. Conclude with `absurd h (one_lt_pow₀ h1 hk).ne'`.
-/
private lemma eq_one_of_pow_eq_one_of_ne_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ}
    {k : ℕ} (hk : k ≠ 0) (h : a ^ k = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hk).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hk).ne'

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
/- English proof (translation)
Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hk`. Establish `hsum : ∑ i ∈ Finset.range k, w ^ i = 0`. Rewrite using `[geom_sum_eq hw1, hw, sub_self, zero_div]`.

Establish `hkF : (k : F) = (w - 1) * -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j`. Rewrite using `[mul_neg, Finset.mul_sum]`. Repeatedly rewrite using `[mul_comm (w - 1), geom_sum_mul]`. Rewrite using `[Finset.sum_sub_distrib, hsum]`. Simplify using the standard rewrite rules.

Establish `hvw : O.valuation w = 1` using `eq_one_of_pow_eq_one_of_ne_zero hk0 (by rw [← map_pow, hw, map_one])`. Establish `hwO : w ∈ O` using `(O.valuation_le_one_iff w).1 hvw.le`. Establish `hcO : -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j ∈ O` using `neg_mem (sum_mem fun i _ => sum_mem fun j _ => pow_mem hwO j)`. Establish `hvk : O.valuation (k : F) = 1`. Simplify using `using O.valuation_unit hk.unit`.

Rewrite using `[← hvk, hkF, map_mul]`. Conclude with `mul_le_of_le_one_right' ((O.valuation_le_one_iff _).2 hcO)`.
-/
private lemma one_le_valuation_root_of_unity_sub_one {F : Type} [Field F] (O : ValuationSubring F) {k : ℕ}
    (hk : IsUnit (k : O)) {w : F} (hw : w ^ k = 1) (hw1 : w ≠ 1) : 1 ≤ O.valuation (w - 1) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hsum : ∑ i ∈ Finset.range k, w ^ i = 0 := by
    rw [geom_sum_eq hw1, hw, sub_self, zero_div]
  have hkF : (k : F) = (w - 1) * -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp_rw [mul_comm (w - 1), geom_sum_mul]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hvw : O.valuation w = 1 :=
    eq_one_of_pow_eq_one_of_ne_zero hk0 (by rw [← map_pow, hw, map_one])
  have hwO : w ∈ O := (O.valuation_le_one_iff w).1 hvw.le
  have hcO : -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j ∈ O :=
    neg_mem (sum_mem fun i _ => sum_mem fun j _ => pow_mem hwO j)
  have hvk : O.valuation (k : F) = 1 := by
    simpa using O.valuation_unit hk.unit
  rw [← hvk, hkF, map_mul]
  exact mul_le_of_le_one_right' ((O.valuation_le_one_iff _).2 hcO)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in

/- English proof (translation)
Introduce `W _ _ _ F _ _ ϖ hϖ k O φ σ π hk _ hφ hσ hπ hζ d z hd hdz`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hk`. Establish `h0 : ϖ ≠ 0` using `hϖ.ne_zero`.

Establish `hϖF : algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ≠ 0` using `(map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).2 h0)`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[zero_pow hk0]`. Conclude with `hϖF hπ.symm`.

Use `set ζ := σ π / π with hζdef`. Establish `hσπ : σ π = ζ * π` using `by rw [hζdef, div_mul_cancel₀ _ hπ0]`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective W (z : FractionRing W)`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbF : algebraMap W (FractionRing W) b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`.

Establish `key : (z : FractionRing W) * algebraMap W _ b = algebraMap W _ a`. Rewrite using `[← hab, div_mul_cancel₀ _ hbF]`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `key` using `[map_zero]`.

Conclude with `z.ne_zero (by simpa [hbF] using key)`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ`. Take `⟨m', u', rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ`. Establish `hU : z * (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u' * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m') = Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u * _root_.GlobalTheory.IndefiniteRowSideFullHecke.Ge …`. Use `ext`.

Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[show ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 : (FractionRing W)ˣ) : FractionRing W) = algebraMap W _ ϖ from rfl, ← map_pow, ← map_mul, ← map_pow, ← map_mul, key]`. Establish `hord : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z + m' = m`. Use `congrArg (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun hU` as an intermediate fact. Rewrite `this` using `[_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul, ord_vw_unit_mul_uniformiser_pow hϖ, ord_vw_unit_mul_uniformiser_pow hϖ]`. Then use the resulting hypothesis.

Establish `hφu : ∀ x : Wˣ, O.valuation (φ x : F) = 1` using `fun x => by`. Simplify using `using O.valuation_unit (Units.map (φ : W →* O) x)`. Establish `keyF : algebraMap _ F (z : FractionRing W) * ((φ u' : F) * (φ ϖ : F) ^ m') = (φ u : F) * (φ ϖ : F) ^ m`. Use `congrArg (algebraMap (FractionRing W) F) key` as an intermediate fact. Simplify `this` using `only [hφ, map_mul, map_pow]`.

Establish `hP : O.valuation (φ ϖ : F) = O.valuation π ^ k` using `by rw [hφ, ← hπ, map_pow]`. Establish `hV : O.valuation d ^ k * O.valuation π ^ (k * m') = O.valuation π ^ (k * m)`. Use `congrArg O.valuation keyF` as an intermediate fact. Simplify using `only [map_mul, map_pow, hφu, _root_.one_mul, hP] at this`. Rewrite using `[hdz, pow_mul, pow_mul]`.

Conclude with `this`. Establish `hvπ : O.valuation π ≠ 0` using `(Valuation.ne_zero_iff _).2 hπ0`. Use `set y := d * π ^ m' / π ^ m with hydef`. Establish `hvy : O.valuation y = 1`. Apply `eq_one_of_pow_eq_one_of_ne_zero hk0` to reduce the goal to its premises.

Rewrite using `[hydef, map_div₀, map_mul, map_pow, map_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m' k, mul_comm m k, hV, div_self (pow_ne_zero _ hvπ)]`. Use `set w := ζ ^ m' / ζ ^ m with hwdef`. Establish `hσy : σ y = w * y`. Rewrite using `[hydef, hwdef, map_div₀, map_mul, map_pow, map_pow, hd, hσπ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hyO : y ∈ O` using `(O.valuation_le_one_iff y).1 hvy.le`. Establish `hwk : w ^ k = 1`. Rewrite using `[hwdef, div_pow, ← pow_mul, ← pow_mul, mul_comm m' k, mul_comm m k, pow_mul, pow_mul, hζ.pow_eq_one, one_pow, one_pow, div_one]`. Establish `hw : w = 1`. Assume the negation of the conclusion as `hw1`.

Establish `h1` using `one_le_valuation_root_of_unity_sub_one O hk hwk hw1`. Establish `hlt` using `hσ y hyO`. Rewrite `hlt` using `[hσy, show w * y - y = (w - 1) * y by ring, map_mul, hvy, _root_.mul_one]`. Conclude with `absurd hlt (not_lt.2 h1)`. Establish `hdvd : (k : ℤ) ∣ (m' : ℤ) - m`.

Rewrite using `[← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hk0), zpow_natCast, zpow_natCast]`. Conclude with `hw`. Establish `hn : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z = m - m'` using `by omega`. Rewrite using `[hn, ← dvd_neg, neg_sub]`. Conclude with `hdvd`.
-/
theorem _root_.GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ (k : ℕ) (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F), IsUnit (k : O) →
      IsLocalHom φ → (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ x ∈ O, O.valuation (σ x - x) < 1) → π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) →
      IsPrimitiveRoot (σ π / π) k →
      ∀ (d : F) (z : (FractionRing W)ˣ), σ d = d → O.valuation d ^ k = O.valuation (algebraMap (FractionRing W) F z) →
        (k : ℤ) ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z := by
  intro W _ _ _ F _ _ ϖ hϖ k O φ σ π hk _ hφ hσ hπ hζ d z hd hdz
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have h0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖF : algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).2 h0)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hπ
    exact hϖF hπ.symm
  set ζ := σ π / π with hζdef
  have hσπ : σ π = ζ * π := by rw [hζdef, div_mul_cancel₀ _ hπ0]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective W (z : FractionRing W)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap W (FractionRing W) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : (z : FractionRing W) * algebraMap W _ b = algebraMap W _ a := by
    rw [← hab, div_mul_cancel₀ _ hbF]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at key
    exact z.ne_zero (by simpa [hbF] using key)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ

  have hU : z * (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u' *
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m') =
      Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m := by
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [show ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 : (FractionRing W)ˣ) : FractionRing W) =
      algebraMap W _ ϖ from rfl, ← map_pow, ← map_mul, ← map_pow, ← map_mul, key]
  have hord : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z + m' = m := by
    have := congrArg (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun hU
    rwa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul,
      ord_vw_unit_mul_uniformiser_pow hϖ, ord_vw_unit_mul_uniformiser_pow hϖ] at this

  have hφu : ∀ x : Wˣ, O.valuation (φ x : F) = 1 := fun x => by
    simpa using O.valuation_unit (Units.map (φ : W →* O) x)
  have keyF : algebraMap _ F (z : FractionRing W) * ((φ u' : F) * (φ ϖ : F) ^ m') =
      (φ u : F) * (φ ϖ : F) ^ m := by
    have := congrArg (algebraMap (FractionRing W) F) key
    simpa only [hφ, map_mul, map_pow] using this
  have hP : O.valuation (φ ϖ : F) = O.valuation π ^ k := by rw [hφ, ← hπ, map_pow]
  have hV : O.valuation d ^ k * O.valuation π ^ (k * m') = O.valuation π ^ (k * m) := by
    have := congrArg O.valuation keyF
    simp only [map_mul, map_pow, hφu, _root_.one_mul, hP] at this
    rw [hdz, pow_mul, pow_mul]
    exact this
  have hvπ : O.valuation π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  set y := d * π ^ m' / π ^ m with hydef
  have hvy : O.valuation y = 1 := by
    apply eq_one_of_pow_eq_one_of_ne_zero hk0
    rw [hydef, map_div₀, map_mul, map_pow, map_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm m' k, mul_comm m k, hV, div_self (pow_ne_zero _ hvπ)]
  set w := ζ ^ m' / ζ ^ m with hwdef
  have hσy : σ y = w * y := by
    rw [hydef, hwdef, map_div₀, map_mul, map_pow, map_pow, hd, hσπ]
    ring
  have hyO : y ∈ O := (O.valuation_le_one_iff y).1 hvy.le
  have hwk : w ^ k = 1 := by
    rw [hwdef, div_pow, ← pow_mul, ← pow_mul, mul_comm m' k, mul_comm m k, pow_mul, pow_mul,
      hζ.pow_eq_one, one_pow, one_pow, div_one]
  have hw : w = 1 := by
    by_contra hw1
    have h1 := one_le_valuation_root_of_unity_sub_one O hk hwk hw1
    have hlt := hσ y hyO
    rw [hσy, show w * y - y = (w - 1) * y by ring, map_mul, hvy, _root_.mul_one] at hlt
    exact absurd hlt (not_lt.2 h1)
  have hdvd : (k : ℤ) ∣ (m' : ℤ) - m := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hk0), zpow_natCast, zpow_natCast]
    exact hw
  have hn : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z = m - m' := by omega
  rw [hn, ← dvd_neg, neg_sub]
  exact hdvd

end GlobalTheory.Member.TameDivOrd
