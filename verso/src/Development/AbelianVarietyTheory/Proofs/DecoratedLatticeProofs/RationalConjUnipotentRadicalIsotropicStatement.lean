import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalConjUnipotentRadicalIsotropic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspGeo.naconj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FRationalConjUnipotentRadicalIsotropic.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.rational_conj_unipotentRadical_isotropic : ∀ (I : AutInst), ∀ γ ∈ I.GFset, ∀ W, I.IsIsot W → ∃ W', I.IsIsot W' ∧ ∀ m ∈ I.NA W', γ⁻¹ * m * γ ∈ I.NA W := by
  first | exact @GlobalTheory.CuspGeo.naconj | exact GlobalTheory.CuspGeo.naconj | (intros; apply GlobalTheory.CuspGeo.naconj <;> assumption)
