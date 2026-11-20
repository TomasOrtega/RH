import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionNonvanishingPoint.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_point : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB → ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U → (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) → ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | exact GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | (intros; apply GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated <;> assumption)
