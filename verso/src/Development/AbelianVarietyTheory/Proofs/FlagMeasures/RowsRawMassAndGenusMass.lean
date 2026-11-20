import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardMiddleLatticesOverGenusLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowBaseLatticesMemSameHermitianGenusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularGe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrimeStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowsRawMass

open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem rowsLift (D : D7) (u : D.what₂.Word) : LiftsConjugateUnderStabilizer D u := by
  intro hp h3 hs F0 he hz
  exact GlobalTheory.T.row_lattices_same_middle_conjugate_unipotent D u hp h3 hs F0 he hz

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem gluingNum (D : D7) (u : D.what₂.Word) : GluingNumber D u := by
  intro hp h3 hs F0 he hz Λ hΛ
  exact GlobalTheory.T.card_middleLattices_over_genus_lattice D u hp h3 hs F0 he hz Λ hΛ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem rowsGenus (D : D7) (u : D.what₂.Word) : OrthLatticesOneGenus D u := by
  intro hp h3 hs F0 he hz Λ hΛ
  exact GlobalTheory.T.rowBaseLattices_mem_same_hermitianGenus D u hp h3 hs F0 he hz Λ hΛ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem main : ∀ (D : D7) (u : D.what₂.Word), UnitaryVolumeMass.stLem3L0 D u := by
  intro D u hp h3 hs F0 he hz s hsr

  have glue := Formalism.MainNotions.BridgeLemma₂.gluing_mass_of_lift_number_genus D u (rowsLift D u) (gluingNum D u) (rowsGenus D u)
  have hT : ((Tu D u : ℝ) - 1) ^ D.R.f ≠ 0 := by
    apply pow_ne_zero
    have : (3 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast h3
    linarith

  have hm := fun Λ (hΛ : IsRowLat D F0 Λ) => GlobalTheory.T.mass_rowLattice_orthogonal_split_prime D u F0 he hz hp hs Λ hΛ

  obtain ⟨Λ₀, hΛ₀⟩ := GlobalTheory.Mass.RowEx.main D u F0 he hz hp hs
  refine ⟨?_, fun Λ hΛ => ⟨?_, (hm Λ hΛ).2⟩⟩
  · rw [glue hp h3 hs F0 he hz Λ₀ hΛ₀ s hsr, (hm Λ₀ hΛ₀).1, div_pow, mul_assoc, div_mul_cancel₀ _ hT]
  · rw [glue hp h3 hs F0 he hz Λ hΛ s hsr, mul_div_cancel_right₀ _ hT]

end GlobalTheory.Mass.RowsRawMass
