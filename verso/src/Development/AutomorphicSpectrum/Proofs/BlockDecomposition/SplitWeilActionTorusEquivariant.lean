import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitTorus

open Ad3.K.GL2LocalData
open GlobalTheory.CompanionTheory.WeilSplit (norm_pair)
open GlobalTheory.CompanionTheory.SplitGauss (trace_swap)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem map_torus (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) :
    Measure.map (Prod.map (fun x : F => s * x) (fun x : F => s⁻¹ * x)) (muS χ) = muS χ := by
  have e1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have e2 : MeasurableEmbedding (fun x : F => s⁻¹ * x) :=
    (Homeomorph.mulLeft₀ s⁻¹ (inv_ne_zero hs)).measurableEmbedding
  have hm : (modulus s)⁻¹ * (modulus s⁻¹)⁻¹ = 1 := by
    rw [← mul_inv, ← modulus_mul, mul_inv_cancel₀ hs, modulus_one, inv_one]
  rw [← Measure.map_prod_map _ _ e1.measurable e2.measurable,
    map_mul_left_eq_smul _ hs, map_mul_left_eq_smul _ (inv_ne_zero hs),
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, hm, one_smul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem integral_torus (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G (s * u.1, s⁻¹ * u.2) ∂muS χ = ∫ u, G u ∂muS χ := by
  have e1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have e2 : MeasurableEmbedding (fun x : F => s⁻¹ * x) :=
    (Homeomorph.mulLeft₀ s⁻¹ (inv_ne_zero hs)).measurableEmbedding
  have h := (e1.prodMap e2).integral_map (μ := muS χ) G
  rw [map_torus χ hs] at h
  rw [h]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem rW_torus (χ : AddChar F Circle) (a b c d : F) (f : F × F → ℂ) {s : F} (hs : s ≠ 0) (x : F × F) :
    rW χ swapE (muS χ) 1 a b c d (fun y => f (y * (s, s⁻¹))) x =
      rW χ swapE (muS χ) 1 a b c d f (x * (s, s⁻¹)) := by
  obtain ⟨x1, x2⟩ := x
  have hn : x1 * s * (x2 * s⁻¹) = x1 * x2 := by field_simp
  by_cases hc : c = 0
  · simp only [rW, if_pos hc, norm_pair, Prod.mk_mul_mk, hn]
    have e : algebraMap F (F × F) a * (x1, x2) * (s, s⁻¹) = algebraMap F (F × F) a * (x1 * s, x2 * s⁻¹) := by
      ext <;> simp [mul_assoc]
    rw [e]
  · simp only [rW, if_neg hc, norm_pair, trace_swap, Prod.mk_mul_mk, hn]
    congr 1
    set G : F × F → ℂ := fun v =>
      (χ ((a * (x1 * x2) + d * (v.1 * v.2) - (v.1 * (x2 * s⁻¹) + v.2 * (x1 * s))) / c) : ℂ) * f v with hG
    rw [← integral_torus χ hs G]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e1 : s * u.1 * (s⁻¹ * u.2) = u.1 * u.2 := by field_simp
    have e2 : s * u.1 * (x2 * s⁻¹) + s⁻¹ * u.2 * (x1 * s) = u.1 * x2 + u.2 * x1 := by field_simp
    have e3 : u * ((s, s⁻¹) : F × F) = (s * u.1, s⁻¹ * u.2) := by ext <;> simp [mul_comm]
    simp only [hG, e1, e2, e3]

end GlobalTheory.CompanionTheory.SplitTorus

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities.
-/
theorem GlobalTheory.CompanionTheory.SplitTorus.piS_torus : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) (Φ : F × F → ℂ) (τ : Fˣ) (x : F × F),
  GL2LocalData.piS χ c₁ g (fun y => Φ (y * ((τ : F), ((τ⁻¹ : Fˣ) : F)))) x = GL2LocalData.piS χ c₁ g Φ (x * ((τ : F), ((τ⁻¹ : Fˣ) : F))) := by
  intro F _ _ _ _ _ _ _ χ _ _ c₁ g Φ τ x
  simp only [GL2LocalData.piS, Units.val_inv_eq_inv_val]
  rw [← GlobalTheory.CompanionTheory.SplitTorus.rW_torus χ _ _ _ _ _ τ.ne_zero x]
  congr 2
  funext y
  rw [mul_right_comm]
