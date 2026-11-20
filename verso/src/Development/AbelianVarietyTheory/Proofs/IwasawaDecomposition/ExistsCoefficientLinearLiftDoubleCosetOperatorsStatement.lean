import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientLinearLiftDoubleCosetOperators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeLiftN.heckeLift` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCoefficientLinearLiftDoubleCosetOperators.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), HeckeStdPlain → GenHyp M C.Q → MtInput D M tup C.Q → HeckeLift0 (mt0 M) C.Q := by
  first | exact @GlobalTheory.HeckeLiftN.heckeLift | exact GlobalTheory.HeckeLiftN.heckeLift | (intros; apply GlobalTheory.HeckeLiftN.heckeLift <;> assumption)
