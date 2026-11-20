import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ`. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem lact_one_self {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex Csz p hm r h ho i v ψ k`. Establish `hl` using `h.laws v`. Take `⟨-, hA, -, -, -, -, hj⟩` from `GlobalTheory.PinNum.numerics_of_pins D (r.used v).full.Q hl.p.pins`. Take `⟨hpq, hr, -⟩` from `hj ((i : ℕ) + 1) ⟨by omega, by omega⟩`. Establish `hL` using `GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1) (by rw [hpq]; exact hr) hA`.

Use `⟨GlobalTheory.LevelCusp.isMatch_of_isUStab _ ⟨fun x y => by simp, fun x => by simp⟩, fun x hx => ?_, fun w => ?_⟩` and prove the remaining obligations. Establish `e : castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x) = x`. Rewrite using `[lact_one_self]`. Both sides reduce to the same expression. Use `⟨by rw [e]; exact hx, 1, ?_⟩` and prove the remaining obligations.

Establish `ey : (uAt r v i).un k ⟨castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x), by rw [e]; exact hx⟩ = (uAt r v i).un k ⟨x, hx⟩` using `congrArg _ (Subtype.ext e)`. Establish `hf` using `hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩) (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩)) (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)`. Establish `hy : (uAt r v i).un k ⟨x, hx⟩ = mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩)` using `(GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf`. Rewrite using `[ey]`. Conclude with `(congrArg (FrBor 1 ((uAt r v i).un k ⟨x, hx⟩)) hy).mp (GlobalTheory.ShFam.Descent.frBor_one _)`.

Establish `hw : Matrix.mulVec ((1 : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (w : Fin D.R.r → D.host.E) ∈ ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.lattice₂ D ((uAt r v i).X k).Λ`. Rewrite using `[Units.val_one, Matrix.one_mulVec]`. Conclude with `w.2`. Use `⟨hw, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isTransp_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hm r h ho i v ψ k
  have hl := h.laws v
  obtain ⟨-, hA, -, -, -, -, hj⟩ := GlobalTheory.PinNum.numerics_of_pins D (r.used v).full.Q hl.p.pins
  obtain ⟨hpq, hr, -⟩ := hj ((i : ℕ) + 1) ⟨by omega, by omega⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1) (by rw [hpq]; exact hr) hA
  refine ⟨GlobalTheory.LevelCusp.isMatch_of_isUStab _ ⟨fun x y => by simp, fun x => by simp⟩, fun x hx => ?_, fun w => ?_⟩
  · have e : castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x) = x := by
      rw [lact_one_self]; rfl
    refine ⟨by rw [e]; exact hx, 1, ?_⟩
    have ey : (uAt r v i).un k ⟨castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x), by rw [e]; exact hx⟩ =
        (uAt r v i).un k ⟨x, hx⟩ := congrArg _ (Subtype.ext e)
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have hy : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    rw [ey]
    exact (congrArg (FrBor 1 ((uAt r v i).un k ⟨x, hx⟩)) hy).mp (GlobalTheory.ShFam.Descent.frBor_one _)
  · have hw : Matrix.mulVec ((1 : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (w : Fin D.R.r → D.host.E) ∈ ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.lattice₂ D ((uAt r v i).X k).Λ := by
      rw [Units.val_one, Matrix.one_mulVec]; exact w.2
    refine ⟨hw, ?_⟩
    calc Submodule.Quotient.mk ⟨_, hw⟩ = Submodule.Quotient.mk w :=
          congrArg _ (Subtype.ext (Matrix.one_mulVec _))
      _ = ψ k ((ψ k).symm (Submodule.Quotient.mk w)) := ((ψ k).apply_symm_apply _).symm
      _ = _ := rfl
end GlobalTheory.ShareOn

end
