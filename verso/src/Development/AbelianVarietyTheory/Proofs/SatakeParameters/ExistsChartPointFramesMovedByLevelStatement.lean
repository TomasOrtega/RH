import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsChartPointFramesMovedByLevel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsChartPointFramesMovedByLevel.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_chart_point_frames_moved_by_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2)))
    (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    ∃ (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) (κP : GLQ t.X.E (D.R.N t.m2) (rowSG t.Pr t.sel (t.tup μ)))
      (c : rowSG t.Pr t.sel (t.tup μ) → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * ((κP P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG t.m2 (A.ib t.m2 hi β)) ((t.idx μ).levQ t.m2 (A.ib t.m2 hi β)) P (κP P) (c P)) ∧
      q.deco.1.N = p.deco.1.N ∧ q.deco.1.f = p.deco.1.f ∧
      (∀ P, ((c P : t.X.Kˣ) : t.X.K) * z P = 1) ∧
      (∀ P, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det ((κP P)⁻¹).1 : t.X.Eˣ) : t.X.E) =
        rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) ∧
      ∀ P, InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 ((κP P)⁻¹).1) := by
  first | exact @GlobalTheory.LevSrcPt.exists_pt_lev | exact GlobalTheory.LevSrcPt.exists_pt_lev | (intros; apply GlobalTheory.LevSrcPt.exists_pt_lev <;> assumption)
