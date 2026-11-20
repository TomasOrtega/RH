import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariants
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueNormalOfProfiniteInvariants.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.residue_normal_of_profinite_invariants : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by
  first | exact @GlobalTheory.Ideal.Quotient.normal_of_profinite | exact GlobalTheory.Ideal.Quotient.normal_of_profinite | (intros; apply GlobalTheory.Ideal.Quotient.normal_of_profinite <;> assumption)
