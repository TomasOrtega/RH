import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HSNef.exists_isFS | exact GlobalTheory.HSNef.exists_isFS | (intros; apply GlobalTheory.HSNef.exists_isFS <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f → ∃ M : HermLB p, IsFS M f w := by
  first | exact @GlobalTheory.HSNef.exists_isFS | exact GlobalTheory.HSNef.exists_isFS | (intros; apply GlobalTheory.HSNef.exists_isFS <;> assumption)
