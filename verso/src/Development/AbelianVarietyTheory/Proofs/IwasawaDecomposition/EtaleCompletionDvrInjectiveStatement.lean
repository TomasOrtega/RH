import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionDvrInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.cDvr_of_isEtaleCompletion` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FEtaleCompletionDvrInjective.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.etale_completion_dvr_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing R] [IsDomain R] [IsLocalRing R] (φ : A →+* R), IsCN R → IsEtaleCompletion φ → CDvr R ∧ Function.Injective φ ∧ ∀ a b : A, Associated (φ a) (φ b) → Associated a b := by
  first | exact @GlobalTheory.cDvr_of_isEtaleCompletion | exact GlobalTheory.cDvr_of_isEtaleCompletion | (intros; apply GlobalTheory.cDvr_of_isEtaleCompletion <;> assumption)
