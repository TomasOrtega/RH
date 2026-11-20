import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DeRhamSymbol.exists_symbol` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsDeRhamFilGradedSymbolToTateTwist.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI → ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ, (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧ (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a, sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧ (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧ ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a, sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  first | exact @GlobalTheory.DeRhamSymbol.exists_symbol | exact GlobalTheory.DeRhamSymbol.exists_symbol | (intros; apply GlobalTheory.DeRhamSymbol.exists_symbol <;> assumption)
