import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCosetIndicatorExpansionOfDepthPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthPeriodicOfCosetIndicatorExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatProductDepthPeriodicGcdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorDepthConditionsAwayFromTwist

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `_ _`. Take `⟨CF0, h4⟩` from `GlobalTheory.T.flatTensor_depth_conditions_away_from_twist`. Use `⟨CF0, fun CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C0, h4⟩` from `h4 CF hCF`. Use `⟨C0, fun ε C hC => ?_⟩` and prove the remaining obligations.

Take `⟨x₀, h4⟩` from `h4 ε C hC`. Use `⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hi hsc hf => ?_⟩` and prove the remaining obligations. Establish `H` using `h4 D large₂ he hx Γ Pl0 T A Ks R F hS ch hi hsc hf`. Establish `hL : R.toLevCh.Is A.μ0` using `hS.core.lev`. Establish `hde` using `GlobalTheory.RowClaim.Test.pde_ne_q hS`.

Introduce `t Φ β hβ`. Establish `hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `GlobalTheory.RowClaim.Test.guard hS t`. Take `⟨K, hK, hval, hdep⟩` from `H t Φ β hβ`. Take `⟨τ, e, he, hexp⟩` from `GridChoice.sumOK_ex hL ch.S.toGridChoice t Φ hde hc β hβ`. Take `⟨τK, hτK⟩` from `GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic hL ch.S.toGridChoice t Φ β e τ K hK he hexp (hdep e he)`.

Take `⟨τm, hτm⟩` from `hτK.exists_expDepth`. Use `⟨⟨τm, hτm⟩, fun w l hl hlw haw => ?_⟩` and prove the remaining obligations. Establish `hk : 0 < expDepth ch.S.toGridChoice t Φ β` using `hτm.1`. Take `⟨e', he', hexp', hdk⟩` from `GlobalTheory.T.depthPeriodic_of_cosetIndicatorExpansion _ t Φ β _ τm hτm`. Establish `hg` using `GlobalTheory.T.flatProductDepthPeriodic_gcd _ t Φ β e' _ _ hdk (hdep e' he')`.

Take `⟨τg, hτg⟩` from `GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic hL _ t Φ β e' τm _ (Nat.gcd_pos_of_pos_left _ hk) he' hexp' hg`. Establish `hle : expDepth ch.S.toGridChoice t Φ β ≤ Nat.gcd (expDepth ch.S.toGridChoice t Φ β) K` using `Nat.sInf_le ⟨τg, hτg⟩`. Establish `heq` using `le_antisymm (Nat.le_of_dvd hk (Nat.gcd_dvd_left _ _)) hle`. Establish `hdvd : expDepth ch.S.toGridChoice t Φ β ∣ K` using `heq ▸ Nat.gcd_dvd_right _ K`. Use `haveI := Fact.mk hl`.

Conclude with `(padicValNat_dvd_iff_le hK.ne').1 ((pow_padicValNat_dvd).trans hdvd) |>.trans (hval w l hl hlw haw)`.
-/
theorem depthK_of_sumOKK₂ : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → DepthK := by
  intro _ _
  obtain ⟨CF0, h4⟩ := GlobalTheory.T.flatTensor_depth_conditions_away_from_twist
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h4⟩ := h4 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x₀, h4⟩ := h4 ε C hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hi hsc hf => ?_⟩
  have H := h4 D large₂ he hx Γ Pl0 T A Ks R F hS ch hi hsc hf
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q hS
  intro t Φ β hβ
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.RowClaim.Test.guard hS t
  obtain ⟨K, hK, hval, hdep⟩ := H t Φ β hβ
  obtain ⟨τ, e, he, hexp⟩ := GridChoice.sumOK_ex hL ch.S.toGridChoice t Φ hde hc β hβ
  obtain ⟨τK, hτK⟩ := GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic hL ch.S.toGridChoice t Φ β e τ K hK he hexp (hdep e he)
  obtain ⟨τm, hτm⟩ := hτK.exists_expDepth
  refine ⟨⟨τm, hτm⟩, fun w l hl hlw haw => ?_⟩
  have hk : 0 < expDepth ch.S.toGridChoice t Φ β := hτm.1
  obtain ⟨e', he', hexp', hdk⟩ := GlobalTheory.T.depthPeriodic_of_cosetIndicatorExpansion _ t Φ β _ τm hτm
  have hg := GlobalTheory.T.flatProductDepthPeriodic_gcd _ t Φ β e' _ _ hdk (hdep e' he')
  obtain ⟨τg, hτg⟩ := GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic hL _ t Φ β e' τm _ (Nat.gcd_pos_of_pos_left _ hk) he' hexp' hg
  have hle : expDepth ch.S.toGridChoice t Φ β ≤ Nat.gcd (expDepth ch.S.toGridChoice t Φ β) K := Nat.sInf_le ⟨τg, hτg⟩
  have heq := le_antisymm (Nat.le_of_dvd hk (Nat.gcd_dvd_left _ _)) hle
  have hdvd : expDepth ch.S.toGridChoice t Φ β ∣ K := heq ▸ Nat.gcd_dvd_right _ K
  haveI := Fact.mk hl
  exact (padicValNat_dvd_iff_le hK.ne').1 ((pow_padicValNat_dvd).trans hdvd) |>.trans (hval w l hl hlw haw)

end GlobalTheory.DepthUnf

end
