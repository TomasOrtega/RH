import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSupportDegree
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCreationProductSupportDegree.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.creation_product_support_degree : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (l : List (Pos n)) (x : Cn n V) (j : ℕ),
    (∀ i ∈ l, P i) → SuppIn P x → Deg j x →
      SuppIn P (((l.map cre).prod : Module.End ℂ (Cn n V)) x) ∧
        Deg (j + l.length) (((l.map cre).prod : Module.End ℂ (Cn n V)) x) := by
  first | exact @GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod | exact GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod | (intros; apply GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod <;> assumption)
