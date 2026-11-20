import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SysW

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i t P hP cV cW hM hV hhV`. Establish `hP0 : Good R A.μ0 P` using `((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).2.2`. Establish `hWinj : Function.Injective (R.HW i (sg0 D A)).e` using `(hC.models.HW i (sg0 D A)).1`. Establish `key : ∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)`. Introduce `h hh y`.

Establish `h1` using `hM y (hV P cV y) (hhV P hP cV y)`. Establish `h2` using `hh P hP0 cW (R.thG i t y)`. Conclude with `hWinj (h1.trans h2.symm)`. Use `⟨key, ?_⟩` and prove the remaining obligations. Introduce `c w hw`.

Establish `XW` using `GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX SF hSF i`. Take `⟨hW, hWo, hWn, -, -, -, hWe, -⟩` from `XW`. Establish `XV` using `(GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t`. Take `⟨hV', hV'o, hV'n⟩` from `XV`. Establish `hVinj : Function.Injective (R.HV i t).e` using `(hC.models.HV i t).1`.

Establish `heq : ∀ c, hV P c = hV' P c` using `fun c => LinearMap.ext fun x => hVinj (by rw [hhV P hP, hV'o P hP])`. Establish `nV' : Commute (hV' P cV) (LinearMap.adjoint (hV' P cV))` using `Eq.mpr (congrArg (Commute (hV' P cV)) (hV'n.2 P hP cV)) (hV'n.1 P P hP hP _ _)`. Establish `nV : Commute (hV P cV) (LinearMap.adjoint (hV P cV))` using `Eq.mpr (congrArg (fun L => Commute L (LinearMap.adjoint L)) (heq cV)) nV'`. Establish `nW : Commute (hW P cW) (LinearMap.adjoint (hW P cW))` using `Eq.mpr (congrArg (Commute (hW P cW)) (hWn.2 P hP0 cW)) (hWn.1 P P hP0 hP0 _ _)`. Conclude with `GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.thG i t) (fun _ : Unit => hV P cV) (fun _ : Unit => hW P cW) (fun _ u => key hW hWo u) (fun _ => nV) (fun _ => nW) () _ w (hWe c P hP0 cW w hw)`.
-/
theorem matched_operators_theta_intertwine : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i t P hP cV cW hM hV hhV
  have hP0 : Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).2.2
  have hWinj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have key : ∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y) := by
    intro h hh y
    have h1 := hM y (hV P cV y) (hhV P hP cV y)
    have h2 := hh P hP0 cW (R.thG i t y)
    exact hWinj (h1.trans h2.symm)
  refine ⟨key, ?_⟩
  intro c w hw
  have XW := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX SF hSF i
  obtain ⟨hW, hWo, hWn, -, -, -, hWe, -⟩ := XW
  have XV := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t
  obtain ⟨hV', hV'o, hV'n⟩ := XV
  have hVinj : Function.Injective (R.HV i t).e := (hC.models.HV i t).1
  have heq : ∀ c, hV P c = hV' P c := fun c => LinearMap.ext fun x => hVinj (by rw [hhV P hP, hV'o P hP])
  have nV' : Commute (hV' P cV) (LinearMap.adjoint (hV' P cV)) :=
    Eq.mpr (congrArg (Commute (hV' P cV)) (hV'n.2 P hP cV)) (hV'n.1 P P hP hP _ _)
  have nV : Commute (hV P cV) (LinearMap.adjoint (hV P cV)) :=
    Eq.mpr (congrArg (fun L => Commute L (LinearMap.adjoint L)) (heq cV)) nV'
  have nW : Commute (hW P cW) (LinearMap.adjoint (hW P cW)) :=
    Eq.mpr (congrArg (Commute (hW P cW)) (hWn.2 P hP0 cW)) (hWn.1 P P hP0 hP0 _ _)
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.thG i t) (fun _ : Unit => hV P cV) (fun _ : Unit => hW P cW) (fun _ u => key hW hWo u)
    (fun _ => nV) (fun _ => nW) () _ w (hWe c P hP0 cW w hw)

end GlobalTheory.SysW
