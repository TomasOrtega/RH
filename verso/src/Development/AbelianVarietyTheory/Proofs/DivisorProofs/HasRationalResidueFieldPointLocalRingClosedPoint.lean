import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `Z _ q _ y hy r hr`. Establish `hyt : y ∈ (⊤ : Z.Opens)` using `trivial`. Take `⟨s, rfl⟩` from `hr`. Establish `hsurj : Function.Surjective ((Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤))`. Establish `e : (Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤) = (residueFieldIsoBase q y hy).inv.hom` using `ReciprocityTheory.AnForm.R.constRes_eq q y hy`.

Rewrite using `[e]`. Conclude with `(residueFieldIsoBase q y hy).commRingCatIsoToRingEquiv.symm.surjective`. Take `⟨α, hα⟩` from `hsurj (Z.residue y s)`. Use `set g := Z.presheaf.germ ⊤ y hyt (algX q ⊤ α) with hgdef`. Establish `hg : algebraMap (Z.presheaf.stalk y) Z.functionField g = GlobalTheory.Cartier.constFn q α`.

Rewrite using `[hgdef, algebraMap_germ]`. Conclude with `RingHom.congr_fun (fnOf_comp_algX q ⊤ _) α`. Establish `hres : Z.residue y (s - g) = 0`. Rewrite using `[map_sub, sub_eq_zero, ← hα, hgdef, RingHom.comp_apply, ← Scheme.germ_residue, CommRingCat.comp_apply]`. Establish `hnu : ¬ IsUnit (s - g)`.

Introduce `hu`. Establish `: Z.residue y (s - g) ≠ 0`. Use `hu.map (Z.residue y).hom` as an intermediate fact. Conclude with `this.ne_zero`. Conclude with `this hres`.

Use `⟨α, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg, ← map_sub]`. Use `(nonUnit_iff (R := locRing y) ⟨_, s - g, rfl⟩).2 fun hu => hnu ?_` and prove the remaining obligations. Take `⟨u, hu'⟩` from `hu.exists_right_inv`. Take `⟨t, ht⟩` from `u.2`.

Use `isUnit_iff_exists_inv.2 ⟨t, ?_⟩` and prove the remaining obligations. Use `(IsFractionRing.injective (Z.presheaf.stalk y) Z.functionField ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_one, ht]`. Conclude with `congrArg Subtype.val hu'`.
-/
theorem ratRes_locRing_of_isClosed : ∀ (Z : Scheme.{0}) [IsIntegral Z] (q : Z ⟶ Sp ℂ)
    [LocallyOfFiniteType q] (y : Z), IsClosed ({y} : Set Z) →
    RatRes (GlobalTheory.Cartier.constFn q) (locRing y) := by
  intro Z _ q _ y hy r hr
  have hyt : y ∈ (⊤ : Z.Opens) := trivial
  obtain ⟨s, rfl⟩ := hr
  have hsurj : Function.Surjective ((Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤)) := by
    have e : (Z.evaluation ⊤ y hyt).hom.comp (algX q ⊤) = (residueFieldIsoBase q y hy).inv.hom :=
      ReciprocityTheory.AnForm.R.constRes_eq q y hy
    rw [e]
    exact (residueFieldIsoBase q y hy).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨α, hα⟩ := hsurj (Z.residue y s)
  set g := Z.presheaf.germ ⊤ y hyt (algX q ⊤ α) with hgdef
  have hg : algebraMap (Z.presheaf.stalk y) Z.functionField g = GlobalTheory.Cartier.constFn q α := by
    rw [hgdef, algebraMap_germ]
    exact RingHom.congr_fun (fnOf_comp_algX q ⊤ _) α
  have hres : Z.residue y (s - g) = 0 := by
    rw [map_sub, sub_eq_zero, ← hα, hgdef, RingHom.comp_apply, ← Scheme.germ_residue, CommRingCat.comp_apply]
  have hnu : ¬ IsUnit (s - g) := by
    intro hu
    have : Z.residue y (s - g) ≠ 0 := by
      have := hu.map (Z.residue y).hom
      exact this.ne_zero
    exact this hres
  refine ⟨α, ?_⟩
  rw [← hg, ← map_sub]
  refine (nonUnit_iff (R := locRing y) ⟨_, s - g, rfl⟩).2 fun hu => hnu ?_
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨t, ht⟩ := u.2
  refine isUnit_iff_exists_inv.2 ⟨t, ?_⟩
  refine (IsFractionRing.injective (Z.presheaf.stalk y) Z.functionField ?_)
  rw [map_mul, map_one, ht]
  exact congrArg Subtype.val hu'

end GlobalTheory.FieldPair
