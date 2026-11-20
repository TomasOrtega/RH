import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.KGroup

/- English proof (translation)
Establish `hG` using `Formalism.FourierDecayAlt.P.unitary_group_closed k r`. Use `⟨⟨hG.one_mem, by simp⟩, ?_, ?_, fun a ha => hG.unit a ha.1, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Use `⟨hG.mul_mem a ha.1 b hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha.2, Matrix.one_mul, hb.2]`.

Introduce `a ha`. Use `⟨hG.inv_mem a ha.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.inv_eq_left_inv ha.2, conjTranspose_conjTranspose]`. Conclude with `mul_eq_one_comm.mp ha.2`. Establish `hc : Continuous fun g : Mat k r => gᴴ * g` using `(continuous_id.matrix_conjTranspose).matrix_mul continuous_id`.

Conclude with `hG.closed.inter (isClosed_singleton.preimage hc)`.
-/
theorem closedSubgroup (k r : ℕ) : IsClosedSubgroup (Kset k r) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  refine ⟨⟨hG.one_mem, by simp⟩, ?_, ?_, fun a ha => hG.unit a ha.1, ?_⟩
  · intro a ha b hb
    refine ⟨hG.mul_mem a ha.1 b hb.1, ?_⟩
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha.2, Matrix.one_mul, hb.2]
  · intro a ha
    refine ⟨hG.inv_mem a ha.1, ?_⟩
    rw [Matrix.inv_eq_left_inv ha.2, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp ha.2
  · have hc : Continuous fun g : Mat k r => gᴴ * g :=
      (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
    exact hG.closed.inter (isClosed_singleton.preimage hc)

/- English proof (translation)
Establish `hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `IsCompact.of_isClosed_subset (s := (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)) hB (closedSubgroup k r).closed ?_` and prove the remaining obligations. Introduce `g hg i _ j _`. Establish `hu : Matrix.of g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ` using `Matrix.mem_unitaryGroup_iff'.mpr hg.2`. Simplify using `using entry_norm_bound_of_unitary hu i j`.
-/
theorem compact (k r : ℕ) : IsCompact (Kset k r) := by
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)) hB
      (closedSubgroup k r).closed ?_
  intro g hg i _ j _
  have hu : Matrix.of g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr hg.2
  simpa using entry_norm_bound_of_unitary hu i j

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `hermitian_pos_facts_hold k r`. Use `⟨?_, by rw [h1, h2]⟩` and prove the remaining obligations. Use `show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r`. Rewrite using `[h1, h2, Matrix.one_mul]`.
-/
theorem hpk_mem (k r : ℕ) : Hpk k r ∈ Kset k r := by
  obtain ⟨h1, h2, -⟩ := hermitian_pos_facts_hold k r
  refine ⟨?_, by rw [h1, h2]⟩
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [h1, h2, Matrix.one_mul]

/- English proof (translation)
Use `(closedSubgroup k r).inv_mem κ h` as an intermediate fact. Rewrite `this` using `[Matrix.inv_eq_left_inv h.2]`. Then use the resulting hypothesis.
-/
theorem star_mem {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κᴴ ∈ Kset k r := by
  have := (closedSubgroup k r).inv_mem κ h
  rwa [Matrix.inv_eq_left_inv h.2] at this

/- English proof (translation)
Establish `h1 : κᴴ * Hpk k r * κ = Hpk k r` using `h.1`. Establish `h2 : κ * κᴴ = 1` using `mul_eq_one_comm.mp h.2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comm_hpk {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κ * Hpk k r = Hpk k r * κ := by
  have h1 : κᴴ * Hpk k r * κ = Hpk k r := h.1
  have h2 : κ * κᴴ = 1 := mul_eq_one_comm.mp h.2
  calc κ * Hpk k r = κ * (κᴴ * Hpk k r * κ) := by rw [h1]
    _ = (κ * κᴴ) * Hpk k r * κ := by simp only [Matrix.mul_assoc]
    _ = Hpk k r * κ := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Simplify using `only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Complex.normSq_apply]`.
-/
theorem sum_normSq_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (g i j) = (trace (gᴴ * g)).re := by
  rw [Finset.sum_comm]
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply]

/- English proof (translation)
Establish `h2 : κ' * κ'ᴴ = 1` using `mul_eq_one_comm.mp h'.2`. Unfold `gN`. Rewrite using `[sum_normSq_eq_trace, sum_normSq_eq_trace]`. Establish `e : (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * g * κ')`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h.2, Matrix.mul_one]`. Rewrite using `[e, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
theorem gN_biinv {k r : ℕ} {κ κ' : Mat k r} (h : κ ∈ Kset k r) (h' : κ' ∈ Kset k r) (g : Mat k r) :
    gN (κ * g * κ') = gN g := by
  have h2 : κ' * κ'ᴴ = 1 := mul_eq_one_comm.mp h'.2
  unfold gN
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace]
  have e : (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * g * κ') := by
    calc (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * (κᴴ * κ) * g * κ') := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h.2, Matrix.mul_one]
  rw [e, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Introduce `k r` and use `⟨closedSubgroup k r, compact k r, hpk_mem k r, fun _ h => ⟨star_mem h, comm_hpk h⟩, fun _ h _ h' g => gN_biinv h h' g⟩`.
-/
theorem kset_facts : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g :=
  fun k r => ⟨closedSubgroup k r, compact k r, hpk_mem k r, fun _ h => ⟨star_mem h, comm_hpk h⟩,
    fun _ h _ h' g => gN_biinv h h' g⟩

end GlobalTheory.HCXi.KGroup
