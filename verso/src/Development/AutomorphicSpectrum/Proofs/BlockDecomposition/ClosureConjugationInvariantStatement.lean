import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureConjugationInvariant
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FClosureConjugationInvariant.lean&line=157#L157)
-/
theorem _root_.GlobalTheory.T.closure_conjugation_invariant : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
    ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
    a ∈ closure (SAQ d β s) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem | exact GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.MemConj.mem_closure_of_conj_mem <;> assumption)
