import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.ConstSt

namespace ReciprocityTheory.ChartRestriction.G.AI

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem fl3Test_thm : FlatnessTestCriterion := by
  intro c₁ c₂
  simp only
  constructor <;> ring

end ReciprocityTheory.ChartRestriction.G.AI
