import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.W2.kpMem_of :
    UpperTheory.Gal.W2.KpMem := by
  intro p _ G g
  rw [GlobalTheory.HeckeP.inclG_mem_KHT_iff]
  unfold UpperTheory.Gal.W2.IntPt
  have hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ‖(g.1 : ℚ_[p])‖ := norm_pos_iff.2 g.1.ne_zero
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)
    · intro h
      rw [h]
      simp
  rw [hunit]
  apply and_congr_right'
  apply forall_congr'
  intro w
  unfold GlobalTheory.LKLoc.KintK
  rw [GlobalTheory.HeckeP.mem_range_map_subtype]
  simp only [mem_intK_iff]
  rw [← forall_and]
  apply forall_congr'
  intro i
  rw [← forall_and]
