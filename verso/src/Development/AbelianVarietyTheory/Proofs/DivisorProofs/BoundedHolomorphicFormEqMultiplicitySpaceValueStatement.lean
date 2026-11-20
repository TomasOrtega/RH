import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundedHolomorphicFormEqMultiplicitySpaceValue.lean&line=312#L312)
-/
theorem _root_.GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  first | exact @GlobalTheory.BackForm.exists_multMap | exact GlobalTheory.BackForm.exists_multMap | (intros; apply GlobalTheory.BackForm.exists_multMap <;> assumption)
