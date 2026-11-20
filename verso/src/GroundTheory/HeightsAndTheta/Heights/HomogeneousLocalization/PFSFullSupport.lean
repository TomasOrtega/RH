import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SectionsLatticeFS

/- English proof (translation)
Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma FSFullSupport.inter_chartDomain_nonempty {N : ℕ} {U : Set (CP N)} (hU : IsOpen U)
    (hne : U.Nonempty) : (U ∩ CP.chartDomain 0).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  induction x using Projectivization.ind with
  | h v hv =>
    rw [ProjTopology.isOpen_iff] at hU
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
    let g : ℂ → (Fin (N + 1) → ℂ) := fun t => v + t • Pi.single 0 1
    have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
    have hvO : v ∈ O := by
      have : (⟨v, hv⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Projectivization.mk' ℂ ⁻¹' U := hx
      rw [← hOU] at this
      exact this
    have h0 : (g ⁻¹' O).Nonempty := ⟨0, by simpa [g] using hvO⟩
    obtain ⟨t, htO, ht⟩ :=
      (dense_compl_singleton (-(v 0))).inter_open_nonempty _ (hO.preimage hg) h0
    have hw0 : g t 0 ≠ 0 := by
      intro h
      apply ht
      simp only [g, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
      simp only [mem_singleton_iff]
      linear_combination h
    have hw : g t ≠ 0 := fun h => hw0 (by rw [h]; rfl)
    refine ⟨Projectivization.mk ℂ (g t) hw, ?_, hw0⟩
    have : (⟨g t, hw⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Subtype.val ⁻¹' O := htO
    rw [hOU] at this
    exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem FSFullSupport.proof : FSFullSupport.Statement := by
  intro N U hU hne
  obtain ⟨x, hxU, hx0⟩ := FSFullSupport.inter_chartDomain_nonempty hU hne
  rw [CP.fsMeasure, Measure.map_apply (CP.measurable_chartInv 0) hU.measurableSet, CP.fsChartMeasure,
    pos_iff_ne_zero, Ne,
    withDensity_apply_eq_zero' (CP.measurable_fsVolumeDensity 0).ennreal_ofReal.aemeasurable]
  have hset : {z : Fin N → ℂ | ENNReal.ofReal (CP.fsVolumeDensity 0 z) ≠ 0} = univ := by
    ext z
    simp [CP.fsVolumeDensity_pos 0 z]
  rw [hset, univ_inter, ← Ne, ← pos_iff_ne_zero]
  refine ((CP.continuous_chartInv 0).isOpen_preimage U hU).measure_pos volume
    ⟨CP.chartCoord 0 x, ?_⟩
  simpa [CP.chartInv_chartCoord 0 hx0] using hxU

/- English proof (translation)
A detailed English derivation is pending.
-/
example : 0 < CP.fsMeasure 1 univ := FSFullSupport.proof 1 univ isOpen_univ univ_nonempty

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
