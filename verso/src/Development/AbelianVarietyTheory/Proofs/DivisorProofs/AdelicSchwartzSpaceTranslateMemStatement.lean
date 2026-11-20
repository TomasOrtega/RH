import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdelicSchwartzSpaceTranslateMem.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_translate_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ, (fun x => φ (x + a)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchwartzTranslate.main | exact GlobalTheory.SchwartzTranslate.main | (intros; apply GlobalTheory.SchwartzTranslate.main <;> assumption)
