import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassMapConj
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwistedCentralizerMassMapConj.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.twistedCentralizerMass_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T → massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.massC_map_conj | exact GlobalTheory.LKCount.massC_map_conj | (intros; apply GlobalTheory.LKCount.massC_map_conj <;> assumption)
