import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchAConj.star_mem_schA` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStarMemAdelicSchwartzSpaceNumberField.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.star_mem_adelicSchwartzSpaceNumberField : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchAConj.star_mem_schA | exact GlobalTheory.SchAConj.star_mem_schA | (intros; apply GlobalTheory.SchAConj.star_mem_schA <;> assumption)
