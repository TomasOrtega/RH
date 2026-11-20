import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSplitCentreTranslatePreservesCuspSpace.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.split_centre_translate_preserves_cusp_space : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a → ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ, rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧ IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | exact GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | (intros; apply GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem <;> assumption)
