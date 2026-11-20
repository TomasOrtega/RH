import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RuleIntegral.exists_smul_nonneg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConstantSmulIntegralOfFourthPower.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.exists_constant_smul_integral_of_fourth_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  first | exact @GlobalTheory.RuleIntegral.exists_smul_nonneg | exact GlobalTheory.RuleIntegral.exists_smul_nonneg | (intros; apply GlobalTheory.RuleIntegral.exists_smul_nonneg <;> assumption)
