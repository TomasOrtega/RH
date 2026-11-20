import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairAdd

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Substitute using the available equality. Supply the required witnesses or components. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem stAdd : CrystallineSemistableComparison.E.StAdd := by
  intro R _ C _ F T j z z' s
  induction s with
  | zero =>
    intro k x x' hx hx'
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨h', rfl⟩ := hx'
    subst h
    exact ⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩⟩
  | succ s ih =>
    intro k x x' hx hx'
    obtain ⟨a, rfl, ha⟩ := hx
    obtain ⟨a', rfl, ha'⟩ := hx'
    obtain ⟨h1, h2⟩ := ih (k + 1) _ _ ha ha'
    refine ⟨⟨a + a', by simp, ?_⟩, ⟨a - a', by simp, ?_⟩⟩
    · simpa [map_add, smul_add] using h1
    · simpa [map_sub, smul_sub] using h2

end GlobalTheory.CompanionTheory.StairAdd
