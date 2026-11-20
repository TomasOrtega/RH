import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenQuadraticPosOfFiniteNonpos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Set `v` to `(IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)`. Establish `hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0` using `fun x => (Valuation.ne_zero_iff v).mpr x.ne_zero`. Use `⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Simplify using `only [Units.val_mul, map_mul]`.

Rewrite using `[WithZero.log_mul (hne x) (hne y)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y u h`. Establish `hu : v (algebraMap V (FractionRing V) u.val) = 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]`.

Simplify using `[IsDiscreteValuationRing.maximalIdeal]`. Simplify using `only [h, map_mul, hu, _root_.one_mul]`. Introduce `x show 0 < - WithZero.log (v x.val) ↔ _`. Rewrite using `[neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨r, hr⟩` from `IsDiscreteValuationRing.exists_lift_of_le_one h.le`. Use `⟨r, ?_, hr⟩` and prove the remaining obligations. Rewrite `h` using `[← hr]`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h`.

Introduce and unpack `⟨r, hr, h⟩`. Rewrite using `[← h]`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr`.
-/
theorem exists_dvr_fraction_order (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] :
    ∃ o : (FractionRing V)ˣ → ℤ, (∀ x y, o (x * y) = o x + o y) ∧
      (∀ (x y : (FractionRing V)ˣ) (u : Vˣ),
        x.val = algebraMap V (FractionRing V) u.val * y.val → o x = o y) ∧
      ∀ x, 0 < o x ↔ ∃ r ∈ IsLocalRing.maximalIdeal V,
        algebraMap V (FractionRing V) r = x.val := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0 := fun x =>
    (Valuation.ne_zero_iff v).mpr x.ne_zero
  refine ⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩
  · intro x y
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (hne x) (hne y)]
    ring
  · intro x y u h
    have hu : v (algebraMap V (FractionRing V) u.val) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      simp [IsDiscreteValuationRing.maximalIdeal]
    simp only [h, map_mul, hu, _root_.one_mul]
  · intro x
    show 0 < - WithZero.log (v x.val) ↔ _
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
      refine ⟨r, ?_, hr⟩
      rw [← hr] at h
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h
    · rintro ⟨r, hr, h⟩
      rw [← h]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr

/- English proof (translation)
Introduce `V _ _ _ X _ _ a hc he hfin x hx`. Take `⟨o, hmul, hunit, hpos⟩` from `exists_dvr_fraction_order V`. Rewrite using `[← hpos]`. Use `even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx` and prove the remaining obligations. Introduce `x y z`.

Take `⟨u, hu⟩` from `hc x y z`. Use `hunit _ _ u hu` as an intermediate fact. Simplify `this` using `only [hmul]`. Introduce `x`. Take `⟨u, hu⟩` from `he x`.

Conclude with `hunit _ _ u hu`. Use `hfin.subset ?_` and prove the remaining obligations. Introduce `x hx`. Use `show ¬ _`. Rewrite using `[← hpos]`.

Conclude with `not_lt.mpr hx`.
-/
theorem cubeRel_scalars_mem_maximalIdeal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (a : X → (FractionRing V)ˣ), (∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) → (∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) → {x | ¬ ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val}.Finite → ∀ x, x ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val := by
  intro V _ _ _ X _ _ a hc he hfin x hx
  obtain ⟨o, hmul, hunit, hpos⟩ := exists_dvr_fraction_order V
  rw [← hpos]
  refine even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx
  · intro x y z
    obtain ⟨u, hu⟩ := hc x y z
    have := hunit _ _ u hu
    simpa only [hmul] using this
  · intro x
    obtain ⟨u, hu⟩ := he x
    exact hunit _ _ u hu
  · refine hfin.subset ?_
    intro x hx
    show ¬ _
    rw [← hpos]
    exact not_lt.mpr hx

end GlobalTheory
