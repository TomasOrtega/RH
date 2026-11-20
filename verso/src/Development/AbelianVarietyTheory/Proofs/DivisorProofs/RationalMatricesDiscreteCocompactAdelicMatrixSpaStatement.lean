import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdelicMatrixLatticeF.lattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalMatricesDiscreteCocompactAdelicMatrixSpa.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  first | exact @GlobalTheory.AdelicMatrixLatticeF.lattice | exact GlobalTheory.AdelicMatrixLatticeF.lattice | (intros; apply GlobalTheory.AdelicMatrixLatticeF.lattice <;> assumption)
