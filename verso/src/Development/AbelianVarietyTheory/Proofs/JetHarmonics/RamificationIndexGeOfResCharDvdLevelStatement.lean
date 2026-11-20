import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RamificationIndexGeOfResCharDvdLevel
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FRamificationIndexGeOfResCharDvdLevel.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.ramificationIndex_ge_of_resChar_dvd_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la ∣ l.M → resCharOf la - 1 ≤ ramOverZ la := by
  first | exact @GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level | exact GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level | (intros; apply GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level <;> assumption)
