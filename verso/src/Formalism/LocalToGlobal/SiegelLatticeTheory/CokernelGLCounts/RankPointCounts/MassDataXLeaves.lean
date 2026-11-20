import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HinfCpt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.OpenCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Transfer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ClassCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasureIsomorphismAtInfinity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds

noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

/- English proof (translation)
The claim follows from `PIW.MassDataColumns.hinfCompact_of Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)`.
-/
theorem hinfCompact_holds : MassDataMassesW.HinfCompact :=
  PIW.MassDataColumns.hinfCompact_of Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finHA_eq_eFin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x = Formalism.L2.SG.Pf.Meas.eFin X.B.I hb x := rfl

/- English proof (translation)
Introduce `D X`. Establish `hb` using `Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I`. Establish `hs : Function.Surjective (finHA X hb)`. Introduce `y`. Take `⟨x, hx⟩` from `(Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).surjective y`.

Conclude with `⟨x, by rw [finHA_eq_eFin]; exact hx⟩`. Establish `himg : ((MassDataMassesW.KX X : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) = Formalism.L2.SG.Pf.Meas.eFin X.B.I hb '' X.B.I.Kset`. Rewrite using `[MassDataMassesW.KX, PIW.MassDataColumns.kf_eq_image X hb hs]`. Both sides reduce to the same expression. Rewrite using `[himg]`.

Conclude with `⟨(Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).image (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).continuous, (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).isOpenMap _ (Formalism.L2.SG.Pf.kset_open X.B.I)⟩`.
-/
theorem kCompactOpen_holds : MassDataMassesW.KCompactOpen := by
  intro D X
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hs : Function.Surjective (finHA X hb) := by
    intro y
    obtain ⟨x, hx⟩ := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).surjective y
    exact ⟨x, by rw [finHA_eq_eFin]; exact hx⟩
  have himg : ((MassDataMassesW.KX X : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
      Formalism.L2.SG.Pf.Meas.eFin X.B.I hb '' X.B.I.Kset := by
    rw [MassDataMassesW.KX, PIW.MassDataColumns.kf_eq_image X hb hs]
    rfl
  rw [himg]
  exact ⟨(Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).image (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).continuous,
    (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).isOpenMap _ (Formalism.L2.SG.Pf.kset_open X.B.I)⟩

/- English proof (translation)
Use `haveI : Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K' : Set G))) := hf`. Establish `hr : ∀ a b : G, (DoubleCoset.setoid (Γ : Set G) (K' : Set G)) a b → (DoubleCoset.setoid (Γ : Set G) (K : Set G)) a b`. Introduce `a b hab`. Rewrite `hab`, the goal using `[DoubleCoset.rel_iff]`. Take `⟨x, hx, y, hy, hxy⟩` from `hab`.

Conclude with `⟨x, hx, y, h hy, hxy⟩`. Use `show Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K : Set G)))`. Use `Finite.of_surjective (Quotient.map' id hr) ?_` and prove the remaining obligations. Introduce `q`. Proceed by induction on `q using Quotient.inductionOn' with`.

Consider the case `h a => exact ⟨Quotient.mk'' a, rfl⟩`.
-/
theorem dc_finite_mono {G : Type} [Group G] (Γ K' K : Subgroup G) (h : K' ≤ K)
    (hf : Finite (DoubleCoset.Quotient (Γ : Set G) (K' : Set G))) :
    Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := by
  haveI : Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K' : Set G))) := hf
  have hr : ∀ a b : G, (DoubleCoset.setoid (Γ : Set G) (K' : Set G)) a b → (DoubleCoset.setoid (Γ : Set G) (K : Set G)) a b := by
    intro a b hab
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hab
    exact ⟨x, hx, y, h hy, hxy⟩
  show Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K : Set G)))
  refine Finite.of_surjective (Quotient.map' id hr) ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h a => exact ⟨Quotient.mk'' a, rfl⟩

/- English proof (translation)
Rewrite using `[PIW.MassDataColumns.unitaryLevelClosureSubgroup, Subgroup.closure_le]`. Introduce and unpack `⟨h, hh⟩ hk`. Take `⟨y, ⟨k, hk2, rfl⟩, hy⟩` from `hk`. Use `show h ∈ MassDataMassesW.KX X`. Establish `hy' : finHA X hb (X.xu u) * finHA X hb k * (finHA X hb (X.xu u))⁻¹ = h` using `hy`.

Rewrite using `[← hy']`. Establish `hxu : finHA X hb (X.xu u) ∈ MassDataMassesW.KX X` using `(PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)`. Establish `hkK : finHA X hb k ∈ MassDataMassesW.KX X` using `(PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)`. Conclude with `(MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)`.
-/
theorem hermitian_level_le {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    PIW.MassDataColumns.unitaryLevelClosureSubgroup X hb u ≤ MassDataMassesW.KH X u := by
  rw [PIW.MassDataColumns.unitaryLevelClosureSubgroup, Subgroup.closure_le]
  rintro ⟨h, hh⟩ hk
  obtain ⟨y, ⟨k, hk2, rfl⟩, hy⟩ := hk
  show h ∈ MassDataMassesW.KX X
  have hy' : finHA X hb (X.xu u) * finHA X hb k * (finHA X hb (X.xu u))⁻¹ = h := hy
  rw [← hy']
  have hxu : finHA X hb (X.xu u) ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
  have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
  exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

/- English proof (translation)
Introduce `D X u`. Establish `hb` using `Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I`. Establish `hK` using `Formalism.L2.SG.Closed.level_subgroup_is_group X`. Establish `hF` using `Formalism.L2.SG.Closed.ClassFin_holds X u hK`. Establish `hc` using `PIW.MassDataColumns.class_sets_equal_card X hb hK u (Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I) (Formalism.L2.SG.Closed.level_subgroup_properties X)`.

Establish `hne : Nonempty (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK))` using `inferInstance`. Use `haveI : Finite (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := hF`. Establish `hfin : Finite (PIW.MassDataColumns.ClsHA X hb u)`. Establish `hpos : 0 < Nat.card (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK))` using `Nat.card_pos`. Conclude with `Nat.finite_of_card_ne_zero (hc ▸ hpos.ne')`.

Conclude with `dc_finite_mono _ _ _ (hermitian_level_le X hb u) hfin`.
-/
theorem classFinite_holds : MassDataMassesW.ClassFinite := by
  intro D X u
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hF := Formalism.L2.SG.Closed.ClassFin_holds X u hK
  have hc := PIW.MassDataColumns.class_sets_equal_card X hb hK u (Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I)
    (Formalism.L2.SG.Closed.level_subgroup_properties X)
  have hne : Nonempty (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := inferInstance
  haveI : Finite (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := hF
  have hfin : Finite (PIW.MassDataColumns.ClsHA X hb u) := by
    have hpos : 0 < Nat.card (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) :=
      Nat.card_pos
    exact Nat.finite_of_card_ne_zero (hc ▸ hpos.ne')
  exact dc_finite_mono _ _ _ (hermitian_level_le X hb u) hfin

end Formalism.L2.SG.Pf.MassDataX
