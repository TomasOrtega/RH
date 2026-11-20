import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryGroupCompactQuotient
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnitaryGroupCompactQuotient.lean&line=201#L201)
-/
theorem _root_.GlobalTheory.T.unitary_group_compact_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E),
  IsUnit H.det → cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H → (∀ τ : E →+* ℂ, (H.map τ).PosDef) →
  (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧
    ∀ g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))),
      ∃ γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H, ∃ k ∈ C, g = ratF E n γ * k) ∧
  ∀ X : Set (GL (Fin n) (Af E)), IsCompact X →
    {γ : GL (Fin n) E | γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ratF E n γ ∈ X}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.DefiniteTransport.cocompact_discrete | exact GlobalTheory.CompanionTheory.DefiniteTransport.cocompact_discrete | (intros; apply GlobalTheory.CompanionTheory.DefiniteTransport.cocompact_discrete <;> assumption)
