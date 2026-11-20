import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeve
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentRadicalAdelicEqRatMulBoundedRealMulLeve.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (s : ℕ) (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E, ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧ unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  first | exact @GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | exact GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | (intros; apply GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin <;> assumption)
