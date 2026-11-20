import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesExist
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SURepsExist.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpecialUnitaryRepresentativesExist.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.special_unitary_representatives_exist : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSReps (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) 1 s := by
  first | exact @GlobalTheory.SURepsExist.main | exact GlobalTheory.SURepsExist.main | (intros; apply GlobalTheory.SURepsExist.main <;> assumption)
