import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjUniformizerIsUniformizerConjPrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.UnifConj.conj_unif_isUnif` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FConjUniformizerIsUniformizerConjPrime.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.conj_uniformizer_isUniformizer_conjPrime : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (Pb : Formalism.L2.DIV.Pl E) (Ut : Formalism.L2.Col.MhlUnif Pb), Formalism.L2.Col.cO E Ut.π ∈ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ∧ Formalism.L2.Col.cO E Ut.π ∉ (Formalism.L2.Col.conjPrime₂ Pb).asIdeal ^ 2 := by
  first | exact @GlobalTheory.Mem.UnifConj.conj_unif_isUnif | exact GlobalTheory.Mem.UnifConj.conj_unif_isUnif | (intros; apply GlobalTheory.Mem.UnifConj.conj_unif_isUnif <;> assumption)
