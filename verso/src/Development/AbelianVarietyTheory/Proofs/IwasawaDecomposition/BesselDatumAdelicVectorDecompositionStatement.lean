import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBesselDatumAdelicVectorDecomposition.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.besselDatum_adelicVector_decomposition : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧ ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) + ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  first | exact @GlobalTheory.BesselDecomp.decomp | exact GlobalTheory.BesselDecomp.decomp | (intros; apply GlobalTheory.BesselDecomp.decomp <;> assumption)
