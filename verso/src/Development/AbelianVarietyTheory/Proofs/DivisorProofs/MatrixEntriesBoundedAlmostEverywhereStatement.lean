import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixEntriesBoundedAlmostEverywhere.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.matrix_entries_bounded_almost_everywhere : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  first | exact @GlobalTheory.FixedBound.exists_entry_absFin_bound | exact GlobalTheory.FixedBound.exists_entry_absFin_bound | (intros; apply GlobalTheory.FixedBound.exists_entry_absFin_bound <;> assumption)
