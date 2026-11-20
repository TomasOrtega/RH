import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose

namespace PositivityTheory.CW

/- English proof (translation)
Introduce `n ε g hg`. Establish `hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g` using `hg`. Use `⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g), ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu, ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g, (ReciprocityTheory.ChartRestriction.DS.PolarDec …` and prove the remaining obligations.
-/
theorem d5 : D5 := by
  intro n ε g hg
  have hu : ReciprocityTheory.ChartRestriction.DS.inUJ ε g := hg
  refine ⟨g * NormedSpace.exp (-ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g),
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_k_mem hu,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L g,
    (ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.polar_L_inP hu).1,
    ReciprocityTheory.ChartRestriction.DS.PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩

end PositivityTheory.CW
