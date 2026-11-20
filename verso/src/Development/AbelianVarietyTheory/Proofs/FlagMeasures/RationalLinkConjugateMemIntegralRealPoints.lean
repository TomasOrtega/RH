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

namespace GlobalTheory.CoverAct

/- English proof (translation)
Introduce `D X Y W u u' s n hn`. Take `⟨h1, h2⟩` from `hn`. Establish `hδ` using `W.isom u`. Establish `hm1 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam (lf D (X.Fu u))`. Rewrite `h1` using `[← Formalism.L2.SG.TermTieOf.mapL_lf W u]`.

Conclude with `(Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h1`. Establish `hm2 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam s.frame` using `(Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h2`. Establish `hiso : (W.δ u)⁻¹ * n * W.δ u ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `mul_mem (mul_mem (inv_mem hδ) h1.1.1) hδ`. Establish `hlin : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `s.rep.2.2.1`. Establish `hlam : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam` using `s.rep.2.2.2.1`.

Establish `hfr : s.frame = Formalism.L2.SG.Saturated.mapL s.lin hlin (lf D (X.Fu u'))`. Unfold `Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF`. Rewrite using `[dif_pos hlin]`. Both sides reduce to the same expression. Rewrite `hm2` using `[hfr, ← hlam]`.

Establish `hm3` using `(Formalism.L2.SG.Pf.mem_NLam_map s.lin hlin _ _ _).1 hm2`. Take `⟨x, hx⟩` from `Formalism.L2.SG.Pf.ratPt_holds D X _ hiso`. Conclude with `⟨x, hx, x, _, hx, rfl, hm1, hm3⟩`.
-/
theorem ratLink_mem_ROinf : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  intro D X Y W u u' s n hn
  obtain ⟨h1, h2⟩ := hn
  have hδ := W.isom u
  have hm1 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam (lf D (X.Fu u)) := by
    rw [← Formalism.L2.SG.TermTieOf.mapL_lf W u] at h1
    exact (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h1
  have hm2 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam s.frame :=
    (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h2
  have hiso : (W.δ u)⁻¹ * n * W.δ u ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    mul_mem (mul_mem (inv_mem hδ) h1.1.1) hδ
  have hlin : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hlam : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hfr : s.frame = Formalism.L2.SG.Saturated.mapL s.lin hlin (lf D (X.Fu u')) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dif_pos hlin]
    rfl
  rw [hfr, ← hlam] at hm2
  have hm3 := (Formalism.L2.SG.Pf.mem_NLam_map s.lin hlin _ _ _).1 hm2
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X _ hiso
  exact ⟨x, hx, x, _, hx, rfl, hm1, hm3⟩

end GlobalTheory.CoverAct
