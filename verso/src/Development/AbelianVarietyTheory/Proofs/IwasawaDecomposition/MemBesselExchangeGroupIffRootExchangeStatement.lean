import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMemBesselExchangeGroupIffRootExchange.lean&line=172#L172)
-/
theorem _root_.GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  first | exact @GlobalTheory.RootExch.ExStruct.mem_Ex_iff | exact GlobalTheory.RootExch.ExStruct.mem_Ex_iff | (intros; apply GlobalTheory.RootExch.ExStruct.mem_Ex_iff <;> assumption)
