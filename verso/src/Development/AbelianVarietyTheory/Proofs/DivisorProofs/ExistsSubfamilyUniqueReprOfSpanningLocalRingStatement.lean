import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSubfamilyUniqueReprOfSpanningLocalRing.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_subfamily_unique_repr_of_spanning_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ), Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M, (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) → ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  first | exact @GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing | exact GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing | (intros; apply GlobalTheory.exists_subfamily_unique_repr_of_spanning_localRing <;> assumption)
