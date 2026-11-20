import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelVectorBundleOfPresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKernelVectorBundleOfPresentation.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.kernel_vector_bundle_of_presentation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (P₁ P₃ : Pres B) (r : ℕ) (F : B.X.Modules) (j : F ⟶ P₁.mod), GlobalTheory.VB.IsVB F r → Nonempty (cokernel j ≅ P₃.mod) → GlobalTheory.VB.IsVB (kernel j) r := by
  first | exact @GlobalTheory.KerVB.isVB_kernel_of_pres | exact GlobalTheory.KerVB.isVB_kernel_of_pres | (intros; apply GlobalTheory.KerVB.isVB_kernel_of_pres <;> assumption)
