import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfLeStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfReg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Htat.HopfOrderEqTop

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[PositivityTheory.HtPt.Twhopf.mem_order, PositivityTheory.HtPt.Twhopf.mem_order]`. Use `⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩` and prove the remaining obligations. Take `⟨R', _, _, _, _, hN, hflat, hP⟩` from `@hHenselian R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime`. Establish `hinj : Function.Injective (algebraMap R R')` using `FaithfulSMul.algebraMap_injective R R'`.

Take `⟨Γ', F, hF⟩` from `hBaseChange R T Γ R' (algebraMap R R') hinj`. Establish `hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R'))` using `(IsFractionRing.injective R' (FractionRing R')).comp hinj`. Set `κ : FractionRing R →+* FractionRing R'` to `IsFractionRing.lift hinj'`. Establish `hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r)` using `fun r => IsFractionRing.lift_algebraMap hinj' r`. Establish `hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')` using `RingHom.ext hκa`.

Take `⟨g', hg1, hg2⟩` from `Scheme.exists_preimage_of_isPullback hF.cart g (IsLocalRing.closedPoint R') (by`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `hP.symm)`. Use `haveI := Γ'.quasiFinite`. Use `haveI := Γ'.finPres`.

Use `haveI := Γ'.separated`. Use `haveI := Γ'.quasiCompact`. Take `⟨U', hU'fin, hU'cl⟩` from `PositivityTheory.HtPt.Twhopf.finite_part R' Γ'.G.left Γ'.G.hom`. Establish `hU'` using `PositivityTheory.HtPt.Twhopf.finite_sub R' T Γ' U' hU'fin hU'cl`. Establish `hFU` using `GlobalTheory.T.isFinOpenSub_base_change R T Γ R' Γ' F hF U hU`.

Establish `hle : F ⁻¹ᵁ U ≤ U'` using `PositivityTheory.HtPt.Twhopf.finite_le R' _ Γ'.G.hom _ _ hFU.finite hU'cl`. Establish `h1 : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U)`. Introduce `s x hx`. Use `hRegular R T Γ R' Γ' F hF κ hκ _ x (hf s (F x) hx)` as an intermediate fact. Simplify `this` using `only [hκa]`.

Rewrite `h1` using `[← PositivityTheory.HtPt.Twhopf.mem_order, ← GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub R' T Γ' U' _ hU' hFU hle, PositivityTheory.HtPt.Twhopf.mem_order]`. Rewrite using `[← hg1]`. Use `PositivityTheory.HtPt.Htat.bt_reg_descent R T Γ R' Γ' F hF hflat κ hκ _ g' ?_` and prove the remaining obligations. Simplify `h1 t g' (hU'cl g' hg2)` using `only [hκa]`.
-/
theorem btOrder_eq_top (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T]
    [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    Γ.btOrder U = Γ.btOrder ⊤ := by
  ext f
  rw [PositivityTheory.HtPt.Twhopf.mem_order, PositivityTheory.HtPt.Twhopf.mem_order]
  refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
  obtain ⟨R', _, _, _, _, hN, hflat, hP⟩ :=
    @hHenselian R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime
  have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
  obtain ⟨Γ', F, hF⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let κ : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := fun r =>
    IsFractionRing.lift_algebraMap hinj' r
  have hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := RingHom.ext hκa
  obtain ⟨g', hg1, hg2⟩ := Scheme.exists_preimage_of_isPullback hF.cart g (IsLocalRing.closedPoint R') (by
    apply PrimeSpectrum.ext
    exact hP.symm)
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  obtain ⟨U', hU'fin, hU'cl⟩ := PositivityTheory.HtPt.Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU' := PositivityTheory.HtPt.Twhopf.finite_sub R' T Γ' U' hU'fin hU'cl
  have hFU := GlobalTheory.T.isFinOpenSub_base_change R T Γ R' Γ' F hF U hU
  have hle : F ⁻¹ᵁ U ≤ U' := PositivityTheory.HtPt.Twhopf.finite_le R' _ Γ'.G.hom _ _ hFU.finite hU'cl
  have h1 : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U) := by
    intro s x hx
    have := hRegular R T Γ R' Γ' F hF κ hκ _ x (hf s (F x) hx)
    simpa only [hκa] using this
  rw [← PositivityTheory.HtPt.Twhopf.mem_order, ← GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub R' T Γ' U' _ hU' hFU hle, PositivityTheory.HtPt.Twhopf.mem_order] at h1
  rw [← hg1]
  refine PositivityTheory.HtPt.Htat.bt_reg_descent R T Γ R' Γ' F hF hflat κ hκ _ g' ?_
  simpa only [hκa] using h1 t g' (hU'cl g' hg2)

end PositivityTheory.HtPt.Htat.HopfOrderEqTop

/- English proof (translation)
The claim follows from `@PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular`.
-/
theorem PositivityTheory.HtPt.Htat.bt_sub_eq_top_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular
