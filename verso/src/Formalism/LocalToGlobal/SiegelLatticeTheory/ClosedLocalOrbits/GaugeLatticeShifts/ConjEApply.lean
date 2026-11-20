import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntTor
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PRhoRw

noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cont_conj (A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous fun x : Mt k r => (fun i j => (A * Matrix.of x * B) i j : Mt k r) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply_apply i j).comp ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

def conjE {μ : ℂ} (hμ : μ ≠ 0) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (torS μ⁻¹ k r * Matrix.of x * torS μ k r) i j
  invFun x := fun i j => (torS μ k r * Matrix.of x * torS μ⁻¹ k r) i j
  left_inv x := by
    funext i j
    show (torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r) i j = x i j
    rw [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  right_inv x := by
    funext i j
    show (torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r) i j = x i j
    rw [show torS μ⁻¹ k r * (torS μ k r * Matrix.of x * torS μ⁻¹ k r) * torS μ k r =
      (torS μ⁻¹ k r * torS μ k r) * Matrix.of x * (torS μ⁻¹ k r * torS μ k r) by simp only [Matrix.mul_assoc],
      torS_inv_mul μ hμ, Matrix.one_mul, Matrix.mul_one]
    rfl
  measurable_toFun := (cont_conj _ _).measurable
  measurable_invFun := (cont_conj _ _).measurable

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjE_apply {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) = torS μ⁻¹ k r * Matrix.of x * torS μ k r := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem conjE_mem_N {μ : ℂ} (hμ : μ ≠ 0) (x : Mt k r) :
    Matrix.of (conjE (k := k) (r := r) hμ x) ∈ Nset k r ↔ Matrix.of x ∈ Nset k r := by
  rw [conjE_apply]
  constructor
  · intro h
    have := tor_conj_N hμ h
    rwa [show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r =
      (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc],
      torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one] at this
  · intro h
    have := tor_conj_N (inv_ne_zero hμ) h
    rwa [inv_inv] at this

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem haarN_tor {μ : ℂ} (hμ : μ ≠ 0) {μN : Measure (Mt k r)} (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN) :
    Formalism.MainNotions.S.IsHaarOn (Nset k r) (μN.map (conjE hμ)) := by
  obtain ⟨hsf, hne, hconc, hleft⟩ := hN
  refine ⟨(conjE hμ).sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h0
    apply hne
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h1
    rw [MeasurableEquiv.map_apply, Set.preimage_univ] at h1
    exact Measure.measure_univ_eq_zero.mp h1
  · rw [MeasurableEquiv.map_apply]
    have e : (conjE (k := k) (r := r) hμ) ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} =
        {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, conjE_mem_N]
    rw [e]; exact hconc
  · have hs' : torS μ k r * s * torS μ⁻¹ k r ∈ Nset k r := tor_conj_N hμ hs
    have hmeas : Measurable (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    have hmeas' : Measurable (lmulM (k := k) (r := r) (torS μ k r * s * torS μ⁻¹ k r)) := by
      unfold lmulM
      exact (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable
    rw [Measure.map_map hmeas (conjE hμ).measurable]
    have e : lmulM (k := k) (r := r) s ∘ (conjE hμ) = (conjE hμ) ∘ lmulM (torS μ k r * s * torS μ⁻¹ k r) := by
      funext x
      simp only [Function.comp_apply]
      change (s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        (torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      calc s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r)
          = (torS μ⁻¹ k r * torS μ k r) * s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) := by
            rw [torS_inv_mul μ hμ, Matrix.one_mul]
        _ = torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r := by
            simp only [Matrix.mul_assoc]
    rw [e, ← Measure.map_map (conjE hμ).measurable hmeas', hleft _ hs']

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem be_tor {μ : ℂ} (hμ : μ ≠ 0) {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (π π' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (σ σ' : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H))
    (hσ : ∀ m, σ' m = σ (torS μ k r * m * torS μ⁻¹ k r)) (hπ : ∀ h ∈ UWset k r z, π' h = π h)
    (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hW : μW {x : Mt k r | Matrix.of x ∉ UWset k r z} = 0) (x y : H) :
    Formalism.FourierDecayAlt.ThreeDimData.be z (c * μ) π' σ' μW (μN.map (conjE hμ)) x y = Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN x y := by
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  have : SigmaFinite (μN.map (conjE hμ)) := (conjE hμ).sigmaFinite_map
  have e : (μW.prod μN).map (Prod.map id (conjE hμ)) = μW.prod (μN.map (conjE hμ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (conjE hμ).measurable, Measure.map_id]
  have hme : MeasurableEmbedding (Prod.map id (conjE (k := k) (r := r) hμ)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Mt k r)) (conjE hμ)).measurableEmbedding
  rw [← e, hme.integral_map]
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ := by
      ext p; simp
    rw [es, Measure.prod_prod, hW, zero_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
  simp only [Prod.map, id]
  have h1 : σ' (Matrix.of p.1 * Matrix.of (conjE hμ p.2)) = σ (Matrix.of p.1 * Matrix.of p.2) := by
    rw [hσ, conjE_apply]
    congr 1
    calc torS μ k r * (Matrix.of p.1 * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r)) * torS μ⁻¹ k r
        = (torS μ k r * Matrix.of p.1 * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.1 * Matrix.of p.2 := by rw [tor_conj_uw hμ hp, torS_mul_inv μ hμ, Matrix.mul_one]
  have h2 : psi k r z (c * μ) (Matrix.of (conjE hμ p.2)) = psi k r z c (Matrix.of p.2) := by
    rw [← psi_tor hμ hz c, conjE_apply]
    congr 1
    calc torS μ k r * (torS μ⁻¹ k r * Matrix.of p.2 * torS μ k r) * torS μ⁻¹ k r
        = (torS μ k r * torS μ⁻¹ k r) * Matrix.of p.2 * (torS μ k r * torS μ⁻¹ k r) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.of p.2 := by rw [torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]
  have h3 : π' (Matrix.of p.1)⁻¹ = π (Matrix.of p.1)⁻¹ := hπ _ (PI.UnitaryGroupMassFormula.JCC.uwset_inv hp)
  rw [h1, h2, h3]

end Formalism.L2.SG.RealObj.EnergyIntTor
