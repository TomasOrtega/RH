import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

open CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.Forms

/- English proof (translation)
Introduce `K A _ _ _ a f`. Use `⟨exteriorPower.alternatingMapLinearEquiv ((exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).curryLeft (KaehlerDifferential.D K A f)), ?_⟩` and prove the remaining obligations. Introduce `g₀ g`. Unfold `CrystallineSemistableComparison.Onto.form`. Rewrite using `[map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.curryLeft_apply_apply]`.

Use `congr 2`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) k <;> simp`.
-/
theorem dWedge_exists : CrystallineSemistableComparison.Onto.DWedge := by
  intro K A _ _ _ a f
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    ((exteriorPower.ιMulti A (a + 1) (M := Ω[A⁄K])).curryLeft (KaehlerDifferential.D K A f)), ?_⟩
  intro g₀ g
  unfold CrystallineSemistableComparison.Onto.form
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  congr 2
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

end GlobalTheory.CompanionTheory.Forms
