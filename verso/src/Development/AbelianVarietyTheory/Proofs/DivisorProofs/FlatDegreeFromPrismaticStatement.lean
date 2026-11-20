import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeFromPrismatic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatDegreeFromPrismatic.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.flat_degree_from_prismatic : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt := by
  first | exact @GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne | exact GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne | (intros; apply GlobalTheory.FlatCore.flatDegreeSt_of_prismaticDieudonne <;> assumption)
