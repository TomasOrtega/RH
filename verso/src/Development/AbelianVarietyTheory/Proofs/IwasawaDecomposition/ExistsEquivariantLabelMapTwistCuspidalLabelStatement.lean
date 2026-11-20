import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsEquivariantLabelMapTwistCuspidalLabel.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K), Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C, Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧ ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  first | exact @GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | exact GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel | (intros; apply GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel <;> assumption)
