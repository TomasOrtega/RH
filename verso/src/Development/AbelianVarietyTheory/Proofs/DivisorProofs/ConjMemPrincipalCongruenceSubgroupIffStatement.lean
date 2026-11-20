import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KapOrb.conj_mem_congSet_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConjMemPrincipalCongruenceSubgroupIff.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ) (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  first | exact @GlobalTheory.KapOrb.conj_mem_congSet_iff | exact GlobalTheory.KapOrb.conj_mem_congSet_iff | (intros; apply GlobalTheory.KapOrb.conj_mem_congSet_iff <;> assumption)
