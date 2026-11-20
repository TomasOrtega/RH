import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.ConstSt

namespace ReciprocityTheory.ChartRestriction.G.AI

/- English proof (translation)
Introduce `c₁ c₂`. Simplify using `only`. Apply the tactic sequence `constructor <;> ring`.
-/
theorem fl3Test_thm : FlatnessTestCriterion := by
  intro c₁ c₂
  simp only
  constructor <;> ring

end ReciprocityTheory.ChartRestriction.G.AI
