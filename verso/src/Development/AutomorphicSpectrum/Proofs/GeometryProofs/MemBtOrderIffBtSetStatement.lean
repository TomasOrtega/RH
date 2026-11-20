import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSet
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FMemBtOrderIffBtSet.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.mem_btOrder_iff_btSet : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → R), f ∈ Γ.btOrder U ↔ f ∈ Γ.btSet U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet | exact GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.mem_btOrder_iff_mem_btSet <;> assumption)
