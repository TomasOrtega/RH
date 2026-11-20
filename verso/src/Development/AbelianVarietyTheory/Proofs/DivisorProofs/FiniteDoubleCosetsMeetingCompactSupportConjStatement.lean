import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetsMeetingCompactSupportConj
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDoubleCosetsMeetingCompactSupportConj.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.finite_doubleCosets_meeting_compact_support_conj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G) (y : G) (f : G → ℂ), IsCompact (K : Set G) → HasCompactSupport f → (∀ C : Set G, IsCompact C → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite) → {q : DoubleCoset.Quotient (T : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * y * (Quotient.out q * k)) ≠ 0}.Finite := by
  first | exact @GlobalTheory.doubleCoset_finite_of_compactSupport | exact GlobalTheory.doubleCoset_finite_of_compactSupport | (intros; apply GlobalTheory.doubleCoset_finite_of_compactSupport <;> assumption)
