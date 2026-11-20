import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.ZhatRat

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem mapFlag_fvec {D : D7} {r : ℕ} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (h : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : FlagG (VS D) r T) (b : Fin (r + 1)) :
    (Formalism.L2.SG.TermOp.mapFlag γ h F).fvec b = γ (F.fvec b) := by
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.TermOp.mapFlag]
  · simp only [FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.TermOp.mapFlag]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem frm_one {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u 1 v a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  rw [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun a' => ?_) a
  · rw [Fin.snoc_last, FlagG.fvec, Fin.snoc_last, X.flagZVector u]
    rfl
  · rw [Fin.snoc_castSucc, FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u]
    rfl

end GlobalTheory.ZhatRat

open GlobalTheory.ZhatRat in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.zhatRat_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (τ : D.what₂.Tau), (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)).map (embS D τ) = Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 (X.pl.symm τ) := by
  intro D X Y W u u' s τ
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  rw [← mapL_lf W u]
  refine (congrArg (fun Z => Matrix.map Z (embS D τ)) (zhatL_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame)).trans ?_
  ext a b
  simp only [Matrix.map_apply]
  have hM1' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1
  have hM3' : ∀ y, X.crd (s.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3
  have hL : (s.frame).fl.fvec b = s.lin ((X.Fu u').fvec b) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dif_pos hiso]
    exact mapFlag_fvec _ hiso _ _
  change embS D τ (brS (VS D) (s.frame.fl.fvec b) ((X.Fu u).fvec a)) = _
  rw [hL]
  unfold brS Formalism.L2.SG.RealObj.ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_one, frm_one, hM1', Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3', Formalism.L2.SG.Pf.Level.hJ_rv, X.φ_eq,
    X.pl.apply_symm_apply, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
