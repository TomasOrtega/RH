import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLatticeOfRationalMemCompletionAllPlaces
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt intAt latV latA)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMemLatticeOfRationalMemCompletionAllPlaces.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.mem_lattice_of_rational_mem_completion_all_places : ∀ (D : D7) (S : HSp D) (L : Lat S), Submodule.IsLattice D.host.E L → ∀ z : Fin S.rank → D.host.E, (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ latV S L (fun _ => True) → z ∈ L := by
  first | exact @GlobalTheory.RatLat.mem_of_mem_latV | exact GlobalTheory.RatLat.mem_of_mem_latV | (intros; apply GlobalTheory.RatLat.mem_of_mem_latV <;> assumption)
