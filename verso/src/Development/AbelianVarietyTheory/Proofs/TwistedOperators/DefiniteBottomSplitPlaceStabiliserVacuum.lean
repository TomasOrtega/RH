import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.StabVacSplit

open GlobalTheory.Grid (neg)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D T L sc G W i j A A' WW X hX t e he k hk hsupp`. Use `set om' := (X.ω t).toSgn true with hom'`. Establish `hW : IsWeilDatumO W.ψ (neg A) WW _ _ om'` using `hX.is.weil t`. Establish `hsdS : IsSelfDualC (neg A) X.rA.Λ` using `GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1`. Establish `hsdT : IsSelfDualC WW X.rW.Λ` using `hX.is.rigW.1`.

Establish `hLW : L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) = (X.rW.Λ : Set (Fin WW.rank → D.host.E))`. Use extensionality with `y`. Conclude with `(GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hX.stdW.1 y).trans (hX.stdW.2.1 y).symm`. Establish `fwd : ∀ h : GA D WW, h ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) → actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True)`. Introduce `h hh u hu`.

Establish `h1 : (1 : AE D) • actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True)` using `GlobalTheory.HeckeVacuum.smul_actO_mem _ _ 1 h (fun y hy => by`. Rewrite using `[map_one, one_smul]`. Establish `h2` using `(hh.2.1 y).1 (by rw [hLW]; exact hy)`. Rewrite `h2` using `[hLW]`. Conclude with `h2) u hu`.

Rewrite `h1` using `[one_smul]`. Then use the resulting hypothesis. Establish `hinv : k⁻¹ ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅` using `(GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k⁻¹).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k).2 hk))`. Establish `hback : ∀ u : WO (neg A) WW, actO (neg A) WW 1 k⁻¹ (actO (neg A) WW 1 k u) = u` using `fun u => by`. Rewrite using `[← GlobalTheory.HeckeVacuum.act_mul (S := neg A) (T := WW) k⁻¹ k u, inv_mul_cancel, GlobalTheory.HeckeVacuum.act_one]`. Establish `hlat : ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) ↔ actO (neg A) WW 1 k u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True)` using `fun u => ⟨fwd k hk u, fun hu => (hback u) ▸ fwd k⁻¹ hinv _ hu⟩`.

Establish `h1 : om' (1, k) X.vac = ((splitFacO _ _ (GlobalTheory.VecInv.detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac` using `GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D W.ψ (neg A) WW X.rA.Λ X.rW.Λ _ _ om' hW hsdS hsdT e he 1 k (GlobalTheory.SplitLinear.suppAt_one e _) hsupp hlat _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.isDetAt_detAt e he.1 WW k) X.v …`. Establish `e1 : X.ω t (1, k) = om' (1, k)`. Rewrite using `[hom']`. Use `show X.ω t (1, k) = X.ω t ((GlobalTheory.Grid.ofSgn true A) 1, k)`. Rewrite using `[map_one]`.

Rewrite using `[e1, h1, splitFacO, map_one, map_one, inv_one, one_mul]`.
-/
theorem stab_vac_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he k hk hsupp
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLW : L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) = (X.rW.Λ : Set (Fin WW.rank → D.host.E)) := by
    ext y
    exact (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hX.stdW.1 y).trans (hX.stdW.2.1 y).symm
  have fwd : ∀ h : GA D WW, h ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ →
      ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) →
        actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) := by
    intro h hh u hu
    have h1 : (1 : AE D) • actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
      GlobalTheory.HeckeVacuum.smul_actO_mem _ _ 1 h (fun y hy => by
        rw [map_one, one_smul]
        have h2 := (hh.2.1 y).1 (by rw [hLW]; exact hy)
        rw [hLW] at h2
        exact h2) u hu
    rwa [one_smul] at h1
  have hinv : k⁻¹ ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ :=
    (GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k⁻¹).1
      (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k).2 hk))
  have hback : ∀ u : WO (neg A) WW, actO (neg A) WW 1 k⁻¹ (actO (neg A) WW 1 k u) = u := fun u => by
    rw [← GlobalTheory.HeckeVacuum.act_mul (S := neg A) (T := WW) k⁻¹ k u, inv_mul_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hlat : ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) ↔
      actO (neg A) WW 1 k u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
    fun u => ⟨fwd k hk u, fun hu => (hback u) ▸ fwd k⁻¹ hinv _ hu⟩
  have h1 : om' (1, k) X.vac = ((splitFacO _ _ (GlobalTheory.VecInv.detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac :=
    GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D W.ψ (neg A) WW X.rA.Λ X.rW.Λ _ _ om' hW hsdS hsdT e he 1 k
      (GlobalTheory.SplitLinear.suppAt_one e _) hsupp hlat _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 (neg A) 1)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 WW k) X.vac hX.is.isVac.2.theta hX.is.isVac.2.lat
  have e1 : X.ω t (1, k) = om' (1, k) := by
    rw [hom']
    show X.ω t (1, k) = X.ω t ((GlobalTheory.Grid.ofSgn true A) 1, k)
    rw [map_one]
  rw [e1, h1, splitFacO, map_one, map_one, inv_one, one_mul]

end GlobalTheory.StabVacSplit

end
