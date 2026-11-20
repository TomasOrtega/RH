import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

/- English proof (translation)
Unfold `eta`. Rewrite using `[if_pos ⟨1, by simp⟩]`.
-/
theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

/- English proof (translation)
Introduce `F E _ _ _ _ _ M a _`. Use `letI := M.mG`. Use `letI := M.mU`. Establish `hG : M.μG Set.univ = 1`. Rewrite using `[← M.volG]`.

Use `congr 1`. Use extensionality with `g`. Simplify using `[glO]`. Establish `hU : M.μU Set.univ = 1`. Rewrite using `[← M.volU]`.

Use `congr 1`. Use extensionality with `g`. Simplify using `[uO]`. Establish `hw : ∀ Y : Gl 0 F, omega Y = 1`. Introduce `Y`.

Establish `: lastDet Y = 1` using `by simp [lastDet, Fin.last]`. Rewrite using `[omega, this, eta_one']`. Use `⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩` and prove the remaining obligations. Establish `hl : X.2.2 = a.2.2` using `(algebraMap F E).injective (congrArg (fun t => t.2.2) hX)`. Apply the tactic sequence `by_cases hb : ‖a.2.2‖ ≤ 1 <;>`.

Simplify using `[orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]`. Conclude with `Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)`.
-/
theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
