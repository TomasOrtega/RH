import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTorsionLatticeCompact
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CountClosedComm.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteTorsionLatticeCompact.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.finite_torsion_lattice_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K T Γ : Subgroup G) (C : Set G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (T : Set G) → (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → Γ ≤ T →
  IsCompact C → (∀ t ∈ T, ∃ γ ∈ Γ, ∃ c ∈ C, t = γ * c) →
  (∀ X : Set G, IsCompact X → ((Γ : Set G) ∩ X).Finite) → {γ : G | γ ∈ Γ ∧ IsOfFinOrder γ}.Finite →
  (∀ x : G, T ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart T ∧
    (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T) ≠ 0) ∧
  (∀ x : G, Finite (Γ ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G)) ∧
  Finite (Γ ⊓ cptPart T : Subgroup G) ∧
  Finite (DoubleCoset.Quotient (((Γ.subgroupOf T) : Subgroup T) : Set T) (((cptPart T).subgroupOf T : Subgroup T) : Set T)) := by
  first | exact @GlobalTheory.CompanionTheory.CountClosedComm.main | exact GlobalTheory.CompanionTheory.CountClosedComm.main | (intros; apply GlobalTheory.CompanionTheory.CountClosedComm.main <;> assumption)
