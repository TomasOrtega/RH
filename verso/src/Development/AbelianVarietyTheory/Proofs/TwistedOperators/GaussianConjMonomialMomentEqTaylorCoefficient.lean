import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.FockJet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFockLSqLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockMoment

variable {ι : Type} [Fintype ι] {a b : ℕ}

def unitPt (r : ι → ℝ) (u : DVar ι a b → ℂ) : VCx ι a b := fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α)

def scalePt (r : ι → ℝ) (z : VCx ι a b) : DVar ι a b → ℂ := fun x => (r x.1 : ℂ) * z x.1 x.2.1 x.2.2

def scaleEquiv (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) : VCx ι a b ≃ᵐ (DVar ι a b → ℂ) where
  toFun := scalePt r
  invFun := unitPt r
  left_inv z := by
    funext τ β α
    have : (r τ : ℂ) ≠ 0 := by exact_mod_cast (hr τ).ne'
    simp [unitPt, scalePt, this]
  right_inv u := by
    funext x
    have : (r x.1 : ℂ) ≠ 0 := by exact_mod_cast (hr x.1).ne'
    simp [unitPt, scalePt, this]
  measurable_toFun := (show Continuous (scalePt (a := a) (b := b) r) by unfold scalePt; fun_prop).measurable
  measurable_invFun := (show Continuous (unitPt (a := a) (b := b) r) by unfold unitPt; fun_prop).measurable

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem scaleEquiv_apply (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    scaleEquiv r hr z = scalePt r z := rfl

/- English proof (translation)
The claim follows from `(scaleEquiv r hr).symm_apply_apply z`.
-/
theorem unitPt_scalePt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (z : VCx ι a b) :
    unitPt r (scalePt r z) = z := (scaleEquiv r hr).symm_apply_apply z

/- English proof (translation)
Rewrite using `[volume_pi]`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.map_apply (scaleEquiv r hr).measurable (MeasurableSet.univ_pi hs), smul_eq_mul]`. Establish `e : (scaleEquiv r hr) ⁻¹' Set.univ.pi s = Set.univ.pi fun τ => Set.univ.pi fun β => Set.univ.pi fun α => (fun w : ℂ => r τ • w) ⁻¹' s (τ, β, α)`. Use extensionality with `z`.

Simplify using `[scaleEquiv_apply, scalePt, Set.mem_univ_pi, Prod.forall, Complex.real_smul]`. Rewrite using `[e, volume_pi, Measure.pi_pi]`. Repeatedly rewrite using `[volume_pi, Measure.pi_pi]`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun x _ => sq_nonneg _)]`. Repeatedly rewrite using `[Fintype.prod_prod_type]`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.addHaar_preimage_smul _ (hr τ).ne', Complex.finrank_real_complex, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (by have := hr τ; positivity), mul_inv_cancel₀ (by have := hr τ; positivity), ENNReal.ofReal_one, one_mul]`.
-/
theorem volume_eq_smul_map (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) :
    (volume : Measure (DVar ι a b → ℂ)) =
      ENNReal.ofReal (∏ x : DVar ι a b, r x.1 ^ 2) • (volume : Measure (VCx ι a b)).map (scaleEquiv r hr) := by
  rw [volume_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.map_apply (scaleEquiv r hr).measurable (MeasurableSet.univ_pi hs), smul_eq_mul]
  have e : (scaleEquiv r hr) ⁻¹' Set.univ.pi s = Set.univ.pi fun τ => Set.univ.pi fun β => Set.univ.pi fun α =>
      (fun w : ℂ => r τ • w) ⁻¹' s (τ, β, α) := by
    ext z
    simp [scaleEquiv_apply, scalePt, Set.mem_univ_pi, Prod.forall, Complex.real_smul]
  rw [e, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [ENNReal.ofReal_prod_of_nonneg (fun x _ => sq_nonneg _)]
  simp_rw [Fintype.prod_prod_type]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun α _ => ?_
  rw [Measure.addHaar_preimage_smul _ (hr τ).ne', Complex.finrank_real_complex, ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (by have := hr τ; positivity), mul_inv_cancel₀ (by have := hr τ; positivity),
    ENNReal.ofReal_one, one_mul]

/- English proof (translation)
Rewrite using `[volume_eq_smul_map r hr, integral_smul_measure, integral_map_equiv]`. Establish `hP : 0 ≤ ∏ x : DVar ι a b, r x.1 ^ 2` using `Finset.prod_nonneg fun _ _ => sq_nonneg _`. Rewrite using `[ENNReal.toReal_ofReal hP, Complex.real_smul]`. Simplify using `only [scaleEquiv_apply, unitPt_scalePt r hr]`.
-/
theorem integral_unitPt (r : ι → ℝ) (hr : ∀ τ, 0 < r τ) (h : VCx ι a b → ℂ) :
    ∫ u : DVar ι a b → ℂ, h (unitPt r u) = ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) * ∫ z, h z := by
  rw [volume_eq_smul_map r hr, integral_smul_measure, integral_map_equiv]
  have hP : 0 ≤ ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_nonneg fun _ _ => sq_nonneg _
  rw [ENNReal.toReal_ofReal hP, Complex.real_smul]
  simp only [scaleEquiv_apply, unitPt_scalePt r hr]

end GlobalTheory.FockMoment

namespace GlobalTheory.FockMoment

open Formalism.DimensionVariation (nsq mono cj mfact)

/- English proof (translation)
Introduce `ι _ a b c hc G hG ⟨M, hM⟩ m`. Use `set r : ι → ℝ := fun τ => Real.sqrt (c τ) with hr_def`. Establish `hr : ∀ τ, 0 < r τ` using `fun τ => Real.sqrt_pos.2 (hc τ)`. Establish `hr2 : ∀ τ, r τ ^ 2 = c τ` using `fun τ => Real.sq_sqrt (hc τ).le`. Establish `hrC : ∀ τ, (r τ : ℂ) ≠ 0` using `fun τ => by exact_mod_cast (hr τ).ne'`.

Use `set F : (DVar ι a b → ℂ) → ℂ := fun u => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α) with hF_def`. Establish `hFd : Differentiable ℂ F` using `hG.comp (by fun_prop)`. Establish `hgq : ∀ u : DVar ι a b → ℂ, gq c (unitPt r u) = nsq u`. Introduce `u`. Simplify using `only [gq, unitPt, nsq, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, hr2, ← mul_assoc, mul_inv_cancel₀ (hc τ).ne', one_mul]`. Establish `hmono : ∀ u : DVar ι a b → ℂ, conjMono m (unitPt r u) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * mono (Formalism.DimensionVariation.cj u) m`. Introduce `u`. Rewrite using `[conjMono, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mono, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `[unitPt, Formalism.DimensionVariation.cj, mul_pow, Complex.conj_ofReal]`. Establish `hgrow : ∀ u : DVar ι a b → ℂ, ‖F u‖ ≤ M * Real.exp (nsq u / 2)` using `fun u => by`. Rewrite using `[← hgq u]`. Conclude with `hM _`.

Establish `hfj` using `(Formalism.DimensionVariation.gaussianCoeffIntegral (DVar ι a b) F (GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F) M hFd.continuous (GlobalTheory.JetFrameCompare.hasSum_taylorCoeff hFd) hgrow m).2`. Establish `htj` using `GlobalTheory.JetBlock.taylor_jetC hG r hr (fun _ => 1) m`. Simplify using `only [Formalism.L2.Ker.jetC, one_pow, one_mul] at htj`. Rewrite `htj` using `[Finsupp.prod_fintype _ _ (fun _ => rfl), Finset.prod_const_one, one_mul]`. Establish `hcov` using `integral_unitPt r hr (fun z => conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)`.

Establish `hint : ∫ u : DVar ι a b → ℂ, conjMono m (unitPt r u) * (Real.exp (-gq c (unitPt r u)) : ℂ) * G (unitPt r u) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * ∫ u, F u * mono (Formalism.DimensionVariation.cj u) m * (Real.exp (-(nsq u)) : ℂ)`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Establish `hFu : F u = G (unitPt r u)` using `rfl`.

Rewrite using `[hmono, hgq, hFu]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hcov` using `[hint, hfj]`. Establish `htj' : GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) * ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x = derivAt0 G m` using `htj`. Establish `hPpos : 0 < ∏ x : DVar ι a b, r x.1 ^ 2` using `Finset.prod_pos fun x _ => by have := hr x.1; positivity`.

Establish `hP : (∏ x : DVar ι a b, r x.1 ^ 2) = ∏ x : DVar ι a b, c x.1` using `Finset.prod_congr rfl fun x _ => hr2 x.1`. Establish `hpi : (∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) = Real.pi ^ Fintype.card (DVar ι a b) * (∏ x : DVar ι a b, r x.1 ^ 2)⁻¹`. Rewrite using `[hP]`. Simplify using `only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod]`. Repeatedly rewrite using `[div_pow]`.

Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, div_eq_mul_inv, mul_comm b a, mul_comm (a * b) (Fintype.card ι)]`. Establish `hmp : ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) ^ 2`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Use `push_cast`. Rewrite using `[← Finset.prod_pow]`.

Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← hr2 x.1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hPC : ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hPpos.ne'`.

Establish `hRR : (∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x) * (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun x _ => by rw [← mul_pow, mul_inv_cancel₀ (hrC x.1), one_pow]`. Establish `hPinv` using `mul_inv_cancel₀ hPC`. Rewrite using `[hpi, hmp, ← htj']`.

Apply `mul_left_cancel₀ hPC` to reduce the goal to its premises. Rewrite using `[← hcov, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]`. Use `set P := ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) with hP_def`. Use `set R := ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x with hR_def`. Use `set Ri := ∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x with hRi_def`.

Use `set TM := GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) with hTM`. Use `set K := (Real.pi : ℂ) ^ Fintype.card (DVar ι a b) with hK`. Take the linear combination `(-(K * TM * Ri)) * hRR + (-(K * TM * Ri ^ 2 * R)) * hPinv`.
-/
theorem gaussMoment : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z) : ℂ) * G z = ((∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) : ℂ) * ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) * derivAt0 G m := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ m
  classical
  set r : ι → ℝ := fun τ => Real.sqrt (c τ) with hr_def
  have hr : ∀ τ, 0 < r τ := fun τ => Real.sqrt_pos.2 (hc τ)
  have hr2 : ∀ τ, r τ ^ 2 = c τ := fun τ => Real.sq_sqrt (hc τ).le
  have hrC : ∀ τ, (r τ : ℂ) ≠ 0 := fun τ => by exact_mod_cast (hr τ).ne'
  set F : (DVar ι a b → ℂ) → ℂ := fun u => G fun τ β α => (r τ : ℂ)⁻¹ * u (τ, β, α) with hF_def
  have hFd : Differentiable ℂ F := hG.comp (by fun_prop)
  have hgq : ∀ u : DVar ι a b → ℂ, gq c (unitPt r u) = nsq u := by
    intro u
    simp only [gq, unitPt, nsq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, hr2, ← mul_assoc,
      mul_inv_cancel₀ (hc τ).ne', one_mul]
  have hmono : ∀ u : DVar ι a b → ℂ, conjMono m (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * mono (Formalism.DimensionVariation.cj u) m := by
    intro u
    rw [conjMono, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [unitPt, Formalism.DimensionVariation.cj, mul_pow, Complex.conj_ofReal]
  have hgrow : ∀ u : DVar ι a b → ℂ, ‖F u‖ ≤ M * Real.exp (nsq u / 2) := fun u => by
    rw [← hgq u]; exact hM _
  have hfj := (Formalism.DimensionVariation.gaussianCoeffIntegral (DVar ι a b) F (GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F) M hFd.continuous
    (GlobalTheory.JetFrameCompare.hasSum_taylorCoeff hFd) hgrow m).2
  have htj := GlobalTheory.JetBlock.taylor_jetC hG r hr (fun _ => 1) m
  simp only [Formalism.L2.Ker.jetC, one_pow, one_mul] at htj
  rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Finset.prod_const_one, one_mul] at htj
  have hcov := integral_unitPt r hr (fun z => conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hint : ∫ u : DVar ι a b → ℂ, conjMono m (unitPt r u) * (Real.exp (-gq c (unitPt r u)) : ℂ) * G (unitPt r u) =
      (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) * ∫ u, F u * mono (Formalism.DimensionVariation.cj u) m * (Real.exp (-(nsq u)) : ℂ) := by
    rw [← integral_const_mul]
    congr 1
    funext u
    have hFu : F u = G (unitPt r u) := rfl
    rw [hmono, hgq, hFu]
    ring
  rw [hint, hfj] at hcov
  have htj' : GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) * ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x = derivAt0 G m := htj
  have hPpos : 0 < ∏ x : DVar ι a b, r x.1 ^ 2 := Finset.prod_pos fun x _ => by have := hr x.1; positivity
  have hP : (∏ x : DVar ι a b, r x.1 ^ 2) = ∏ x : DVar ι a b, c x.1 := Finset.prod_congr rfl fun x _ => hr2 x.1
  have hpi : (∏ τ, (Real.pi / c τ) ^ (a * b) : ℝ) =
      Real.pi ^ Fintype.card (DVar ι a b) * (∏ x : DVar ι a b, r x.1 ^ 2)⁻¹ := by
    rw [hP]
    simp only [Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, div_eq_mul_inv, mul_comm b a,
      mul_comm (a * b) (Fintype.card ι)]
  have hmp : ((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ) : ℂ) = (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) ^ 2 := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    push_cast
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← hr2 x.1]
    push_cast
    ring
  have hPC : ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hRR : (∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x) * (∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => by rw [← mul_pow, mul_inv_cancel₀ (hrC x.1), one_pow]
  have hPinv := mul_inv_cancel₀ hPC
  rw [hpi, hmp, ← htj']
  apply mul_left_cancel₀ hPC
  rw [← hcov, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  set P := ((∏ x : DVar ι a b, r x.1 ^ 2 : ℝ) : ℂ) with hP_def
  set R := ∏ x : DVar ι a b, (r x.1 : ℂ) ^ m x with hR_def
  set Ri := ∏ x : DVar ι a b, ((r x.1 : ℂ)⁻¹) ^ m x with hRi_def
  set TM := GlobalTheory.IndefiniteRowSideFullHecke.TaylorCoefficientForms.taylorCoeff F m * (mfact m : ℂ) with hTM
  set K := (Real.pi : ℂ) ^ Fintype.card (DVar ι a b) with hK
  linear_combination (-(K * TM * Ri)) * hRR + (-(K * TM * Ri ^ 2 * R)) * hPinv
