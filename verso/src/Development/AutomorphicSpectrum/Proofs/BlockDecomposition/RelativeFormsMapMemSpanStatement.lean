import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeFormsMapMemSpan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRelativeFormsMapMemSpan.lean&line=306#L306)
-/
theorem _root_.GlobalTheory.T.relative_forms_map_mem_span : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (ω : Om K (R0 K n d S) a), ω ∈ relOm K (I0 n K S) a → omMap (incl le_top) a ω ∈ Submodule.span K {w : Om K (Lr K n d) a | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSub.relOm_image_mem_span <;> assumption)
