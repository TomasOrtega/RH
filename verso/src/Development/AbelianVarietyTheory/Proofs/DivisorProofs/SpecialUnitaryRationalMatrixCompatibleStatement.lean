import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRationalMatrixCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MassLink.StabLink.ratStab_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpecialUnitaryRationalMatrixCompatible.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.special_unitary_rational_matrix_compatible : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)), GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s → ∀ (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  first | exact @GlobalTheory.MassLink.StabLink.ratStab_mem | exact GlobalTheory.MassLink.StabLink.ratStab_mem | (intros; apply GlobalTheory.MassLink.StabLink.ratStab_mem <;> assumption)
