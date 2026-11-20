import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaConjMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertiaConj.inertia_conj_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInertiaConjMem.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.conj_mem_inertia_of_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  first | exact @GlobalTheory.InertiaConj.inertia_conj_mem | exact GlobalTheory.InertiaConj.inertia_conj_mem | (intros; apply GlobalTheory.InertiaConj.inertia_conj_mem <;> assumption)
