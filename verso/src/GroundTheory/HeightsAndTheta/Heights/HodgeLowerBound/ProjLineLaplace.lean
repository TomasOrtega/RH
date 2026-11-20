import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ProjLineChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianLogGrowth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian MeasureTheory

namespace LineChart

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Split into cases according to the possible forms of the given data. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_nonzero : IsOpen {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have he : {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
      {y : (Σ _ : Unit, Fin 2) → ℂ | ∃ i, y ⟨(), i⟩ ≠ 0} := by
    ext z
    constructor
    · intro h
      exact h ()
    · intro h k
      cases k
      exact h
  rw [he]
  exact Line.isOpen_nonzeroL

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem contDiff_log_h {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A) {g : ℂ → (Σ k : Unit, PBlk 2 k) → ℂ}
    (hg : ContDiff ℝ 2 g) (hne : ∀ w, ∃ i, g w ⟨(), i⟩ ≠ 0) : ContDiff ℝ 2 fun w => Real.log (A.h (g w)) := by
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  have hmem : g w ∈ {z : (Σ k : Unit, PBlk 2 k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun k => by
    cases k
    exact hne w
  have hh : ContDiffAt ℝ 2 A.h (g w) :=
    (hA.contDiffAt (isOpen_nonzero.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top)
  exact (hh.comp w hg.contDiffAt).log (A.pos _ hmem).ne'

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contDiff_cons_one : ContDiff ℂ 2 fun w : ℂ => (Fin.cons 1 (fun _ => w) : Fin (1 + 1) → ℂ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact contDiff_const
  · simp only [Fin.cons_succ]
    exact contDiff_id

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contDiff_cons_last : ContDiff ℂ 2 fun t : ℂ => (Fin.cons t (fun _ => 1) : Fin (1 + 1) → ℂ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact contDiff_id
  · simp only [Fin.cons_succ]
    exact contDiff_const

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem contDiff_lineLift_comp (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    {c : ℂ → Fin (1 + 1) → ℂ} (hc : ContDiff ℂ 2 c) : ContDiff ℝ 2 fun w => lineLift (L (c w)) := by
  have hL : ContDiff ℂ 2 fun w => L (c w) :=
    (LinearMap.toContinuousLinearMap L.toLinearMap).contDiff.comp hc
  have h : ContDiff ℂ 2 fun w => lineLift (L (c w)) :=
    contDiff_pi.2 fun p => (contDiff_apply ℂ ℂ (fun _ => p.2)).comp hL
  exact h.restrict_scalars ℝ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineLift_ne {L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)} {v : Fin (1 + 1) → ℂ}
    (hv : v ≠ 0) : ∃ i, lineLift (L v) ⟨(), i⟩ ≠ 0 :=
  (mem_mcPts_bot _).1 (lineLift_mem ((L.map_ne_zero_iff).mpr hv))

def chartPot (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) (w : ℂ) : ℝ :=
  Real.log (A.h (lineLift (L (Fin.cons 1 fun _ => w))))

def chartPotInf (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    (t : ℂ) : ℝ :=
  Real.log (A.h (lineLift (L (Fin.cons t fun _ => 1))))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem contDiff_chartPot {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A)
    (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) : ContDiff ℝ 2 (chartPot A L) :=
  contDiff_log_h hA (contDiff_lineLift_comp L contDiff_cons_one)
    fun _ => lineLift_ne fun h => one_ne_zero (congrFun h 0)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem contDiff_chartPotInf {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A)
    (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ)) : ContDiff ℝ 2 (chartPotInf A L) :=
  contDiff_log_h hA (contDiff_lineLift_comp L contDiff_cons_last)
    fun _ => lineLift_ne fun h => one_ne_zero (congrFun h 1)

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Split into cases according to the possible forms of the given data.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem chartPot_eq (A : HermLine (PBlk 2)) (L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ))
    {w : ℂ} (hw : w ≠ 0) : chartPot A L w = (A.a () : ℝ) * Real.log ‖w‖ + chartPotInf A L w⁻¹ := by
  have hv : (Fin.cons 1 (fun _ => w) : Fin (1 + 1) → ℂ) = w • Fin.cons w⁻¹ (fun _ => 1) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_inv_cancel₀ hw]
    · simp
  have hz : lineLift (L (Fin.cons 1 (fun _ => w))) =
      fun p => (fun _ : Unit => w) p.1 * lineLift (L (Fin.cons w⁻¹ fun _ => 1)) p := by
    rw [hv, map_smul]
    rfl
  have hmem : ∀ k, ∃ i, lineLift (L (Fin.cons w⁻¹ fun _ => 1)) ⟨k, i⟩ ≠ 0 := fun k => by
    cases k
    exact lineLift_ne fun h => one_ne_zero (congrFun h 1)
  unfold chartPot chartPotInf
  rw [hz, A.smul (fun _ => w) _ (fun _ => hw)]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hw)) (A.pos _ hmem).ne', Real.log_zpow]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem maDensity_eq_laplacian {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (y : Fin 1 → ℂ) :
    maDensity (fun _ y' => u (y' 0)) y = Δ u (y 0) / (2 * Real.pi) := by
  set E : (Fin 1 → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0 with hE
  have hf : (fun y' : Fin 1 → ℂ => u (y' 0)) = u ∘ E := rfl
  have key : ∀ v : Fin 1 → ℂ, fderiv ℝ (fderiv ℝ (fun y' : Fin 1 → ℂ => u (y' 0))) y v v =
      iteratedFDeriv ℝ 2 u (y 0) ![v 0, v 0] := by
    intro v
    have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (u ∘ E) y ![v, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    rw [hf, ← h2, E.iteratedFDeriv_comp_right hu y le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [maDensity_one (fun y' => u (y' 0)) y, key, key, laplacian_eq_iteratedFDeriv_complexPlane]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem geomDeg_eq_degree (hL : LaplacianLogGrowth.Statement) {A : HermLine (PBlk 2)} (hA : IsSmoothHerm A) :
    geomDeg (⊥ : Ideal (MRing (PBlk 2))) A 1 = (A.a () : ℝ) := by
  obtain ⟨L, hEq⟩ := geomDeg_eq_integral A
  rw [hEq]
  have hφ : (fun (_ : Fin 1) (y' : Fin 1 → ℂ) => Real.log (A.h (lineLift (L (Fin.cons 1 y'))))) =
      fun _ y' => chartPot A L (y' 0) := by
    funext j y'
    unfold chartPot
    have hy : (fun _ : Fin 1 => y' 0) = y' := funext fun i => by rw [Subsingleton.elim i 0]
    rw [hy]
  have hu := contDiff_chartPot hA L
  rw [hφ]
  simp_rw [maDensity_eq_laplacian hu]
  have hfu := (volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
    (fun w : ℂ => Δ (chartPot A L) w / (2 * Real.pi))
  rw [show (∫ y : Fin 1 → ℂ, Δ (chartPot A L) (y 0) / (2 * Real.pi)) = _ from hfu, integral_div]
  obtain ⟨-, hint⟩ := hL (chartPot A L) (chartPotInf A L) (A.a () : ℝ) 1 hu one_pos
    (contDiff_chartPotInf hA L).contDiffOn fun w hw => by
      have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw)
      exact chartPot_eq A L hw0
  rw [hint]
  have := Real.pi_pos
  field_simp

end LineChart

end GroundTheory.Heights₂.Heights.LowerBoundFree
