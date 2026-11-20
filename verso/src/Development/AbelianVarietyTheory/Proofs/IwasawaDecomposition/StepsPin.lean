import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.UpPin

/- English proof (translation)
Introduce `hL cDep`. Use `⟨fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), ?_⟩` and prove the remaining obligations. Introduce `K B f T w _ _ H P x l`. Take `⟨x', hx', -⟩` from `H P x l`. Conclude with `⟨x', hx'⟩`.

Introduce `K B f T w _ _ H P x l`. Take `⟨x', hx', -⟩` from `H P x l`. Conclude with `⟨x', hx'⟩`. Introduce `K B f T w _ _ H P x l`. Take `⟨x', hx', -⟩` from `H P x l`.

Conclude with `⟨x', hx'⟩`. Introduce `hB hA hMt hRat hCu hB0 hB1 hB2 hC hFin S Γ`. Establish `h` using `hB.and (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))`. Use `h.trans (StepW.of_all ?_)` and prove the remaining obligations. Introduce `K B f T w _ _ H`.

Take `⟨⟨P, x, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩` from `H`. Take `⟨x1, ⟨la⟩, -⟩` from `a P x hLoc`. Take `⟨imt⟩` from `mt P x1`. Take `⟨irat⟩` from `rat P x1 la`. Establish `li : LI hL x1` using `{ toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }`.

Take `⟨x2, ⟨l0⟩, p2⟩` from `b0 P x1 li`. Take `⟨x3, ⟨l1⟩, p3⟩` from `b1 P x2 l0`. Take `⟨x4, ⟨l2⟩, p4⟩` from `b2 P x3 l1`. Take `⟨sc⟩` from `c P x4 l2`. Take `⟨Z, v, -, -⟩` from `fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ (p4 (p3 p2))`.

Conclude with `⟨Z, ⟨v⟩⟩`.
-/
theorem steps_pin : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, (SettingsFormsExistList hL cDep → SettingsFormsExist hL) ∧ (SeriesExistList hL cDep → SeriesExist hL) ∧
    (ModuliPointsExistList hL cDep → SB2 hL) ∧ (StepW Start HasBare → SA hL → SMt → SRat hL → SCusp hL → SettingsFormsExistList hL cDep → SeriesExistList hL cDep →
      ModuliPointsExistList hL cDep → SC hL → SFinl hL cDep → ∀ (S : SExt) (Γ : GeoP), StepW Start (Has3 (prmR (NEl hL cDep) S Γ).s)) := by
  intro hL cDep
  refine ⟨fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), ?_⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro hB hA hMt hRat hCu hB0 hB1 hB2 hC hFin S Γ
    have h := hB.and (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
    refine h.trans (StepW.of_all ?_)
    intro K B f T w _ _ H
    obtain ⟨⟨P, x, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
    obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
    obtain ⟨imt⟩ := mt P x1
    obtain ⟨irat⟩ := rat P x1 la
    have li : LI hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
    obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
    obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
    obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
    obtain ⟨sc⟩ := c P x4 l2
    obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ (p4 (p3 p2))
    exact ⟨Z, ⟨v⟩⟩

end GlobalTheory.HeightCounting.UpPin

end
