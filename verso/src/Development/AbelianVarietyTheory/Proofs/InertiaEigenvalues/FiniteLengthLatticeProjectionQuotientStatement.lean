import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthLatticeProjectionQuotient
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finiteLength_projection_quotient` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteLengthLatticeProjectionQuotient.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.finiteLength_lattice_projection_quotient : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) (G B : Submodule K V), L.FG → Disjoint G B → Module.length O (↥(G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)) ⧸ (L ⊓ G.restrictScalars O).comap (G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)).subtype) ≠ ⊤ ∨ ¬ (Submodule.span K (L : Set V) = ⊤ ∧ G ⊔ B = ⊤) := by
  first | exact @GlobalTheory.finiteLength_projection_quotient | exact GlobalTheory.finiteLength_projection_quotient | (intros; apply GlobalTheory.finiteLength_projection_quotient <;> assumption)
