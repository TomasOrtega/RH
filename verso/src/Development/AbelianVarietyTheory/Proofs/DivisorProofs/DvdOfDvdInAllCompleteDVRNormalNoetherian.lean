import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrDiv

/- English proof (translation)
Introduce `R _ _ _ _ _ a b hb h`. Distinguish the cases in `ha : a = 0`. Conclude with `ha ▸ dvd_zero b`. Set `K` to `FractionRing R`. Take `⟨h1, h2, -⟩` from `GlobalTheory.normal_domain_height_one.{0, 0, 0} R K`.

Establish `hbK : algebraMap R K b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb`. It suffices to establish `hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by`. Take `⟨r, hr⟩` from `(h2 (algebraMap R K a / algebraMap R K b)).2 hmem`. Use `⟨r, IsFractionRing.injective R K ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, mul_div_cancel₀ _ hbK]`.

Introduce `p _ hp`. Take `⟨-, hD, -⟩` from `h1 p hp`. Set `D` to `primeLocalSubalgebra K p`. Use `haveI : IsDiscreteValuationRing D := hD`. Set `W` to `AdicCompletion (IsLocalRing.maximalIdeal D) D`.

Set `iW : D →+* W` to `algebraMap D W`. Set `φ : R →+* W` to `iW.comp (algebraMap R D)`. Establish `hRD : Function.Injective (algebraMap R D)` using `fun x y hxy => IsFractionRing.injective R K (congrArg Subtype.val hxy)`. Establish `hφ : Function.Injective φ` using `(algebraMap_adicCompletion_injective_of_dvr D).comp hRD`. Use `haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance`.

Establish `hW : GlobalTheory.LN.CDvr W` using `⟨inferInstance, inferInstance, inferInstance⟩`. Take `⟨t, ht⟩` from `h W hW φ hφ`. Establish `hdvd : algebraMap R D b ∣ algebraMap R D a`. Break down `ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩` into its components or cases. Conclude with `hd`.

Establish `ha' : φ a ≠ 0` using `(map_ne_zero_iff _ hφ).mpr ha`. Establish `e : φ a * (iW c * t) = φ a * 1`. Rewrite using `[_root_.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, _root_.mul_assoc]`.

Both sides reduce to the same expression. Use `_ = φ a := by rw [← hc]; exact ht.symm`. Establish `hu : IsUnit (iW c)` using `isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩`. Take `⟨u, rfl⟩` from `isUnit_of_map_unit iW c hu`. Conclude with `⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩`.

Take `⟨c, hc⟩` from `hdvd`. Establish `hcK : algebraMap R K a = algebraMap R K b * (c : K)` using `congrArg Subtype.val hc`. Rewrite using `[hcK, mul_div_cancel_left₀ _ hbK]`. Conclude with `c.2`.
-/
theorem dvd_of_forall_cDvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨t, ht⟩ := h W hW φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

end GlobalTheory.DvrDiv
