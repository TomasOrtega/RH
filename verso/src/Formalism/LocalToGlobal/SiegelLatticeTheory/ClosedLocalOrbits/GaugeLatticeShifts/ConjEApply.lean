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
The claim follows from `continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)`.
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
Rewrite using `[conjE_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `tor_conj_N hμ h` as an intermediate fact. Rewrite `this` using `[show torS μ k r * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) * torS μ⁻¹ k r = (torS μ k r * torS μ⁻¹ k r) * Matrix.of x * (torS μ k r * torS μ⁻¹ k r) by simp only [Matrix.mul_assoc], torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]`. Then use the resulting hypothesis.

Introduce `h`. Use `tor_conj_N (inv_ne_zero hμ) h` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
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
Take `⟨hsf, hne, hconc, hleft⟩` from `hN`. Use `⟨(conjE hμ).sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `h1` using `congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h0`.

Simplify using `only [Measure.coe_zero, Pi.zero_apply] at h1`. Rewrite `h1` using `[MeasurableEquiv.map_apply, Set.preimage_univ]`. Conclude with `Measure.measure_univ_eq_zero.mp h1`. Rewrite using `[MeasurableEquiv.map_apply]`. Establish `e : (conjE (k` using `k) (r := r) hμ) ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} = {x : Mt k r | Matrix.of x ∉ Nset k r} := by`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, conjE_mem_N]`. Rewrite using `[e]`. Conclude with `hconc`. Establish `hs' : torS μ k r * s * torS μ⁻¹ k r ∈ Nset k r` using `tor_conj_N hμ hs`.

Establish `hmeas : Measurable (lmulM (k` using `k) (r := r) s) := by`. Unfold `lmulM`. Conclude with `(continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable`. Establish `hmeas' : Measurable (lmulM (k` using `k) (r := r) (torS μ k r * s * torS μ⁻¹ k r)) := by`. Unfold `lmulM`.

Conclude with `(continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp (continuous_const.matrix_mul continuous_id)).measurable`. Rewrite using `[Measure.map_map hmeas (conjE hμ).measurable]`. Establish `e : lmulM (k` using `k) (r := r) s ∘ (conjE hμ) = (conjE hμ) ∘ lmulM (torS μ k r * s * torS μ⁻¹ k r) := by`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`.

Express the relevant statement in the definitionally equal form `(s * (torS μ⁻¹ k r * Matrix.of x * torS μ k r) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = (torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[torS_inv_mul μ hμ, Matrix.one_mul]`. Use `_ = torS μ⁻¹ k r * (torS μ k r * s * torS μ⁻¹ k r * Matrix.of x) * torS μ k r := by`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[e, ← Measure.map_map (conjE hμ).measurable hmeas', hleft _ hs']`.
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
Unfold `Formalism.FourierDecayAlt.ThreeDimData.be`. Establish `: SigmaFinite (μN.map (conjE hμ))` using `(conjE hμ).sigmaFinite_map`. Establish `e : (μW.prod μN).map (Prod.map id (conjE hμ)) = μW.prod (μN.map (conjE hμ))`. Rewrite using `[← Measure.map_prod_map _ _ measurable_id (conjE hμ).measurable, Measure.map_id]`. Establish `hme : MeasurableEmbedding (Prod.map id (conjE (k` using `k) (r := r) hμ)) := (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Mt k r)) (conjE hμ)).measurableEmbedding`.

Rewrite using `[← e, hme.integral_map]`. Establish `hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z`. Rewrite using `[ae_iff]`. Establish `es : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} = {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ`. Use extensionality with `p`.

Simplify using the standard rewrite rules. Rewrite using `[es, Measure.prod_prod, hW, zero_mul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with p hp`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.beInt`.

Simplify using `only [Prod.map, id]`. Establish `h1 : σ' (Matrix.of p.1 * Matrix.of (conjE hμ p.2)) = σ (Matrix.of p.1 * Matrix.of p.2)`. Rewrite using `[hσ, conjE_apply]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.of p.1 * Matrix.of p.2 := by rw [tor_conj_uw hμ hp, torS_mul_inv μ hμ, Matrix.mul_one]`. Establish `h2 : psi k r z (c * μ) (Matrix.of (conjE hμ p.2)) = psi k r z c (Matrix.of p.2)`. Rewrite using `[← psi_tor hμ hz c, conjE_apply]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Matrix.of p.2 := by rw [torS_mul_inv μ hμ, Matrix.one_mul, Matrix.mul_one]`. Establish `h3 : π' (Matrix.of p.1)⁻¹ = π (Matrix.of p.1)⁻¹` using `hπ _ (PI.UnitaryGroupMassFormula.JCC.uwset_inv hp)`. Rewrite using `[h1, h2, h3]`.
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
