import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.StairAdd

/- English proof (translation)
Introduce `R _ C _ F T j z z' s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `k x x' hx hx'`. Take `⟨h, rfl⟩` from `hx`.

Take `⟨h', rfl⟩` from `hx'`. Substitute `h` using the available equality. Conclude with `⟨⟨rfl, by simp⟩, ⟨rfl, by simp⟩⟩`. Consider the case `succ s ih`. Introduce `k x x' hx hx'`.

Take `⟨a, rfl, ha⟩` from `hx`. Take `⟨a', rfl, ha'⟩` from `hx'`. Take `⟨h1, h2⟩` from `ih (k + 1) _ _ ha ha'`. Use `⟨⟨a + a', by simp, ?_⟩, ⟨a - a', by simp, ?_⟩⟩` and prove the remaining obligations. Simplify `h1` using `[map_add, smul_add]`.

Simplify `h2` using `[map_sub, smul_sub]`.
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
