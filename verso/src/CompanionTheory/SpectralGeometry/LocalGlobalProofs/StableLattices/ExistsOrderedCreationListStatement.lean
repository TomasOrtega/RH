import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationList
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FExistsOrderedCreationList.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.exists_ordered_creation_list : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  first | exact @GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order | exact GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order | (intros; apply GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order <;> assumption)
