import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhood
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenFan.exists_chart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCompleteLocalEtaleNeighbourhood.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.exists_complete_local_etale_neighbourhood : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F), LocallyOfFiniteType s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ x : X, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ξ : Sp R ⟶ X), IsCN R ∧ ξ (closedPoint R) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ ∀ p, ξ p ⤳ x := by
  first | exact @GlobalTheory.GenFan.exists_chart | exact GlobalTheory.GenFan.exists_chart | (intros; apply GlobalTheory.GenFan.exists_chart <;> assumption)
