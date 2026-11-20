import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypePlaces.not_isConjPl` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTypePlacesNotPairwiseConjugate.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.typePlaces_not_pairwise_conjugate : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP' := by
  first | exact @GlobalTheory.TypePlaces.not_isConjPl | exact GlobalTheory.TypePlaces.not_isConjPl | (intros; apply GlobalTheory.TypePlaces.not_isConjPl <;> assumption)
