import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwistLiftW

/- English proof (translation)
Introduce `D X E Y i j b g κ h`. Establish `P` using `Y.Z.pin`. Establish `rW : (Wc D j).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) j.2`. Establish `hβ` using `P.frT i j b`. Establish `hP` using `P.Pg i j b`.

Establish `tri : ∀ (PP : Pl D.host.E) (r t : ℕ), r = (Wc D j).rank → ∀ x : GL (Fin (Wc D j).rank) (kP PP), x ∈ blockTri (blkOf r t)` using `fun PP r t hr x => mem_blockTri.2 fun a c hac => by`. Establish `ha : a.val < r` using `lt_of_lt_of_eq a.2 hr.symm`. Establish `e : blkOf r t a = 0` using `if_pos ha`. Conclude with `absurd (lt_of_lt_of_eq hac e) (Nat.not_lt_zero _)`. Use `⟨h.1, mem_parLev.2 ⟨parLev_UA h.2.1, ?_, fun PP _ => tri PP _ _ rfl _, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hβ]`. Conclude with `parLev_St h.2.1`. Use function extensionality and compare the values at `PP`. Take `⟨PP, hPP⟩` from `PP`. Establish `hPP' : PP ∈ X.R.Pg` using `hP ▸ hPP`.

Use `Units.ext (Matrix.ext fun a c => ?_)` and prove the remaining obligations. Establish `e1` using `P.grp i j b (X.cG (X.R.eG g)) PP hPP hPP' a c`. Rewrite `e1` using `[MulEquiv.symm_apply_apply]`. Use `Eq.trans ?_ e1.symm` and prove the remaining obligations. Rewrite using `[← h.2.2, hβ]`.

Establish `e2` using `upper_block_val_submatrix (le_refl _) (blockTri_blkOf_le _ 1 (tri PP _ 1 rfl (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))`. Establish `e3` using `upper_block_val_submatrix rW.ge (blockTri_blkOf_le _ 1 (tri PP _ 1 rW.symm (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))`. Conclude with `(congrFun (congrFun e2 a) c).trans (congrFun (congrFun e3 (Fin.cast rW a)) (Fin.cast rW c)).symm`.
-/
theorem isLevelLift_base_of_realisation_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := by
  intro D X E Y i j b g κ h
  have P := Y.Z.pin
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  have hβ := P.frT i j b
  have hP := P.Pg i j b
  have tri : ∀ (PP : Pl D.host.E) (r t : ℕ), r = (Wc D j).rank → ∀ x : GL (Fin (Wc D j).rank) (kP PP),
      x ∈ blockTri (blkOf r t) := fun PP r t hr x => mem_blockTri.2 fun a c hac => by
    have ha : a.val < r := lt_of_lt_of_eq a.2 hr.symm
    have e : blkOf r t a = 0 := if_pos ha
    exact absurd (lt_of_lt_of_eq hac e) (Nat.not_lt_zero _)
  refine ⟨h.1, mem_parLev.2 ⟨parLev_UA h.2.1, ?_, fun PP _ => tri PP _ _ rfl _,
    fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
  · rw [hβ]; exact parLev_St h.2.1
  · funext PP
    obtain ⟨PP, hPP⟩ := PP
    have hPP' : PP ∈ X.R.Pg := hP ▸ hPP
    refine Units.ext (Matrix.ext fun a c => ?_)
    have e1 := P.grp i j b (X.cG (X.R.eG g)) PP hPP hPP' a c
    rw [MulEquiv.symm_apply_apply] at e1
    refine Eq.trans ?_ e1.symm
    rw [← h.2.2, hβ]
    have e2 := upper_block_val_submatrix (le_refl _) (blockTri_blkOf_le _ 1 (tri PP _ 1 rfl (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    have e3 := upper_block_val_submatrix rW.ge (blockTri_blkOf_le _ 1 (tri PP _ 1 rW.symm (redFn (X.R.βW j) PP (Lev.finE (Wc D j) κ))))
    exact (congrFun (congrFun e2 a) c).trans (congrFun (congrFun e3 (Fin.cast rW a)) (Fin.cast rW c)).symm

end GlobalTheory.TwistLiftW

end
