import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2 lc)
open scoped NumberField.AdeleRing ValuativeRel
open Ad3.K.GL2LocalData

noncomputable section

namespace GlobalTheory.CompanionTheory.TwistZero

open GlobalTheory.CompanionTheory.SplitRep GlobalTheory.CompanionTheory.SplitPi

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `he1 : MeasurableEmbedding (fun x : F => s * x)` using `(Homeomorph.mulLeft₀ s hs).measurableEmbedding`. Establish `hid : MeasurableEmbedding (id : F → F)` using `MeasurableEmbedding.id`. Establish `he` using `hid.prodMap he1`. Establish `hmap : Measure.map (Prod.map (id : F → F) (fun x : F => s * x)) (muS χ) = (modulus s)⁻¹ • muS χ`. Rewrite using `[← Measure.map_prod_map _ _ measurable_id he1.measurable, map_mul_left_eq_smul _ hs, Measure.map_id, Measure.prod_smul_right]`.

Establish `h` using `he.integral_map (μ := muS χ) G`. Rewrite `h` using `[hmap, integral_smul_nnreal_measure]`. Simplify using `only [Prod.map, id] at h`. Rewrite using `[← h, NNReal.smul_def, Complex.real_smul]`. Use `push_cast`.

Put the polynomial expressions in normal form.
-/
theorem integral_scale_snd (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G (u.1, s * u.2) ∂muS χ = (((modulus s : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, G u ∂muS χ := by
  have he1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have hid : MeasurableEmbedding (id : F → F) := MeasurableEmbedding.id
  have he := hid.prodMap he1
  have hmap : Measure.map (Prod.map (id : F → F) (fun x : F => s * x)) (muS χ) =
      (modulus s)⁻¹ • muS χ := by
    rw [← Measure.map_prod_map _ _ measurable_id he1.measurable,
      map_mul_left_eq_smul _ hs, Measure.map_id, Measure.prod_smul_right]
  have h := he.integral_map (μ := muS χ) G
  rw [hmap, integral_smul_nnreal_measure] at h
  simp only [Prod.map, id] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring_nf

/- English proof (translation)
Establish `h1` using `integral_scale_fst χ hs (fun y : F × F => G (y.1, s⁻¹ * y.2))`. Establish `h2` using `integral_scale_snd χ (inv_ne_zero hs) G`. Establish `e : ∀ y : F × F, y * ((s, s⁻¹) : F × F) = (s * y.1, s⁻¹ * y.2)` using `fun y => by`. Apply the tactic sequence `ext <;> simp [mul_comm]`. Simplify using `only [e]`.

Rewrite using `[h1, h2, ← mul_assoc]`. Establish `hM : ((modulus s : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast modulus_ne_zero hs`. Rewrite using `[modulus_inv]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_norm_one (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ y, G (y * (s, s⁻¹)) ∂muS χ = ∫ y, G y ∂muS χ := by
  have h1 := integral_scale_fst χ hs (fun y : F × F => G (y.1, s⁻¹ * y.2))
  have h2 := integral_scale_snd χ (inv_ne_zero hs) G
  have e : ∀ y : F × F, y * ((s, s⁻¹) : F × F) = (s * y.1, s⁻¹ * y.2) := fun y => by
    ext <;> simp [mul_comm]
  simp only [e]
  rw [h1, h2, ← mul_assoc]
  have hM : ((modulus s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hs
  rw [modulus_inv]
  push_cast
  field_simp

/- English proof (translation)
Distinguish the cases in `hc : m 1 0 = 0`. Rewrite using `[rWS_zero χ hm hc, rWS_zero χ hm hc]`. Simplify using the standard rewrite rules. Rewrite using `[rWS_ne χ hc, rWS_ne χ hc]`. Use `congr 1`.

Establish `h` using `integral_norm_one χ hs (fun u : F × F => (χ ((m 0 0 * ((0 : F × F).1 * (0 : F × F).2) + m 1 1 * (u.1 * u.2) - (u.1 * (0 : F × F).2 + u.2 * (0 : F × F).1)) / m 1 0) : ℂ) * Ψ u)`. Rewrite using `[← h]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `e : (u * ((s, s⁻¹) : F × F)).1 * (u * ((s, s⁻¹) : F × F)).2 = u.1 * u.2`. Simplify using `only [Prod.fst_mul, Prod.snd_mul]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [e, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, add_zero]`.
-/
theorem rWS_zero_point (χ : AddChar F Circle) {m : Matrix (Fin 2) (Fin 2) F} (hm : m.det = 1) {s : F}
    (hs : s ≠ 0) (Ψ : F × F → ℂ) :
    rWS χ m (fun y => Ψ (y * (s, s⁻¹))) 0 = rWS χ m Ψ 0 := by
  by_cases hc : m 1 0 = 0
  · rw [rWS_zero χ hm hc, rWS_zero χ hm hc]
    simp
  · rw [rWS_ne χ hc, rWS_ne χ hc]
    congr 1
    have h := integral_norm_one χ hs (fun u : F × F =>
      (χ ((m 0 0 * ((0 : F × F).1 * (0 : F × F).2) + m 1 1 * (u.1 * u.2) -
        (u.1 * (0 : F × F).2 + u.2 * (0 : F × F).1)) / m 1 0) : ℂ) * Ψ u)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : (u * ((s, s⁻¹) : F × F)).1 * (u * ((s, s⁻¹) : F × F)).2 = u.1 * u.2 := by
      simp only [Prod.fst_mul, Prod.snd_mul]
      field_simp
    simp only [e, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, add_zero]

/- English proof (translation)
Establish `hd : (g.val).det ≠ 0`. Use `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit` as an intermediate fact. Conclude with `this.ne_zero`. Rewrite using `[Matrix.det_fin_two_of]`. Rewrite using `[show g.val 0 0 / (g.val).det * g.val 1 1 - g.val 0 1 * (g.val 1 0 / (g.val).det) = (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) / (g.val).det by ring, ← Matrix.det_fin_two]`.

Conclude with `div_self hd`.
-/
theorem det_normal (g : GL (Fin 2) F) :
    (!![g.val 0 0 / (g.val).det, g.val 0 1; g.val 1 0 / (g.val).det, g.val 1 1] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have hd : (g.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two_of]
  rw [show g.val 0 0 / (g.val).det * g.val 1 1 - g.val 0 1 * (g.val 1 0 / (g.val).det) =
    (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) / (g.val).det by ring, ← Matrix.det_fin_two]
  exact div_self hd

/- English proof (translation)
Unfold `piS`. Use `congr 1`. Establish `h` using `rWS_zero_point χ (det_normal g) u.ne_zero (fun y => Φ (y * ((g.val).det, 1)))`. Simplify using `only [rWS, rWm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h`. Rewrite using `[Units.val_inv_eq_inv_val]`.

Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[mul_right_comm]`.
-/
theorem piS_zero (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) (u : Fˣ) (Φ : F × F → ℂ) :
    piS χ c₁ g (fun x => Φ (x * ((u : F), ((u⁻¹ : Fˣ) : F)))) 0 = piS χ c₁ g Φ 0 := by
  unfold piS
  congr 1
  have h := rWS_zero_point χ (det_normal g) u.ne_zero (fun y => Φ (y * ((g.val).det, 1)))
  simp only [rWS, rWm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  rw [Units.val_inv_eq_inv_val]
  rw [← h]
  congr 1
  funext y
  rw [mul_right_comm]

end Local

open GroundTheory.Global.AdicLiesOver in
/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (Qv v) (Kv K w))` using `(algebraMap (Qv v) (Kv K w)).injective`. Establish `h` using `Function.leftInverse_invFun hinj 0`. Simplify `h` using `[dg1]`.
-/
theorem degreeOneEmbedding_zero {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj 0
  simpa [dg1] using h

end GlobalTheory.CompanionTheory.TwistZero

namespace GlobalTheory.CompanionTheory.TwistZero

/- English proof (translation)
Introduce `K _ _ c v D u g`. Consider the cases of `D with`. Consider the case `sp w₁ w₂ Φ`. Simplify using `only [LM.tw, LM.val, degreeOneEmbedding_zero]`. Conclude with `piS_zero _ _ g u Φ`.

Consider the case `ns w σ η Φ => rfl`.
-/
theorem val_tw_zero : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (D : LM c v)
    (u : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), (D.tw u).val g 0 = D.val g 0 := by
  intro K _ _ c v D u g
  cases D with
  | sp w₁ w₂ Φ =>
    simp only [LM.tw, LM.val, degreeOneEmbedding_zero]
    exact piS_zero _ _ g u Φ
  | ns w σ η Φ => rfl

end GlobalTheory.CompanionTheory.TwistZero
