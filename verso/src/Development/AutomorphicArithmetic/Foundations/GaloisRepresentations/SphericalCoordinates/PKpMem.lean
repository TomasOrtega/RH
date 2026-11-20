import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Use `show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _`. Conclude with `ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff`.
-/
private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

/- English proof (translation)
Introduce `p _ G g`. Rewrite using `[GlobalTheory.HeckeP.inclG_mem_KHT_iff]`. Unfold `UpperTheory.Gal.W2.IntPt`. Establish `hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1`. Rewrite using `[Units.val_inv_eq_inv_val, norm_inv]`.

Establish `hpos : 0 < ‖(g.1 : ℚ_[p])‖` using `norm_pos_iff.2 g.1.ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)`. Introduce `h`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Rewrite using `[hunit]`. Apply `and_congr_right'` to reduce the goal to its premises. Apply `forall_congr'` to reduce the goal to its premises.

Introduce `w`. Unfold `GlobalTheory.LKLoc.KintK`. Rewrite using `[GlobalTheory.HeckeP.mem_range_map_subtype]`. Simplify using `only [mem_intK_iff]`. Rewrite using `[← forall_and]`.

Apply `forall_congr'` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← forall_and]`.
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
