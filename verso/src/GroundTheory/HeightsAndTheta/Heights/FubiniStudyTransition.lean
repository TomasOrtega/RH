import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate Matrix
open Set

noncomputable section

variable {N : ℕ}

namespace CP

def hpair (V W : Fin (N + 1) → ℂ) : ℂ := ∑ m, V m * conj (W m)

/- English proof (translation)
Simplify using `[hpair, add_mul, Finset.sum_add_distrib]`.
-/
lemma hpair_add_left (V V' W : Fin (N + 1) → ℂ) : hpair (V + V') W = hpair V W + hpair V' W := by
  simp [hpair, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hpair, mul_add, Finset.sum_add_distrib]`.
-/
lemma hpair_add_right (V W W' : Fin (N + 1) → ℂ) : hpair V (W + W') = hpair V W + hpair V W' := by
  simp [hpair, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Rewrite using `[hpair, hpair, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hpair_smul_left (c : ℂ) (V W : Fin (N + 1) → ℂ) : hpair (c • V) W = c * hpair V W := by
  rw [hpair, hpair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[hpair, hpair, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hpair_smul_right (c : ℂ) (V W : Fin (N + 1) → ℂ) :
    hpair V (c • W) = conj c * hpair V W := by
  rw [hpair, hpair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

def fsHerm (p V W : Fin (N + 1) → ℂ) : ℂ :=
  (hpair V W * hpair p p - hpair V p * hpair p W) / ((2 * Real.pi : ℂ) * hpair p p ^ 2)

/- English proof (translation)
Simplify using `only [fsHerm, hpair_smul_left, hpair_smul_right]`. Establish `hr : c * conj c ≠ 0` using `mul_ne_zero hc ((map_ne_zero _).mpr hc)`. Rewrite using `[← mul_div_mul_left (hpair V W * hpair p p - hpair V p * hpair p W) _ (pow_ne_zero 2 hr)]`. Apply the tactic sequence `congr 1 <;> ring`.
-/
lemma fsHerm_smul {c : ℂ} (hc : c ≠ 0) (p V W : Fin (N + 1) → ℂ) :
    fsHerm (c • p) (c • V) (c • W) = fsHerm p V W := by
  simp only [fsHerm, hpair_smul_left, hpair_smul_right]
  have hr : c * conj c ≠ 0 := mul_ne_zero hc ((map_ne_zero _).mpr hc)
  rw [← mul_div_mul_left (hpair V W * hpair p p - hpair V p * hpair p W) _ (pow_ne_zero 2 hr)]
  congr 1 <;> ring

/- English proof (translation)
Simplify using `only [fsHerm, hpair_add_left, hpair_add_right, hpair_smul_left, hpair_smul_right]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma fsHerm_add_smul (p V W : Fin (N + 1) → ℂ) (a b : ℂ) :
    fsHerm p (V + a • p) (W + b • p) = fsHerm p V W := by
  simp only [fsHerm, hpair_add_left, hpair_add_right, hpair_smul_left, hpair_smul_right]
  congr 1
  ring

def liftVec (i : Fin (N + 1)) (ξ : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.insertNth i 0 ξ

/- English proof (translation)
Simplify using `[liftVec]`.
-/
@[simp] lemma liftVec_self (i : Fin (N + 1)) (ξ : Fin N → ℂ) : liftVec i ξ i = 0 := by
  simp [liftVec]

/- English proof (translation)
Simplify using `[liftVec]`.
-/
@[simp] lemma liftVec_succAbove (i : Fin (N + 1)) (ξ : Fin N → ℂ) (k : Fin N) :
    liftVec i ξ (i.succAbove k) = ξ k := by
  simp [liftVec]

/- English proof (translation)
Rewrite using `[hpair, Fin.sum_univ_succAbove _ i]`. Simplify using the standard rewrite rules.
-/
lemma hpair_liftVec_liftVec (i : Fin (N + 1)) (ξ η : Fin N → ℂ) :
    hpair (liftVec i ξ) (liftVec i η) = ∑ k, ξ k * conj (η k) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]; simp

/- English proof (translation)
Rewrite using `[hpair, Fin.sum_univ_succAbove _ i]`. Simplify using the standard rewrite rules.
-/
lemma hpair_liftVec_chartVec (i : Fin (N + 1)) (ξ z : Fin N → ℂ) :
    hpair (liftVec i ξ) (chartVec i z) = ∑ k, ξ k * conj (z k) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]; simp

/- English proof (translation)
Rewrite using `[hpair, Fin.sum_univ_succAbove _ i]`. Simplify using the standard rewrite rules.
-/
lemma hpair_chartVec_liftVec (i : Fin (N + 1)) (z η : Fin N → ℂ) :
    hpair (chartVec i z) (liftVec i η) = ∑ k, z k * conj (η k) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]; simp

/- English proof (translation)
Rewrite using `[hpair, Fin.sum_univ_succAbove _ i]`. Simplify using `[normSqSum, Complex.mul_conj']`.
-/
lemma hpair_chartVec_self (i : Fin (N + 1)) (z : Fin N → ℂ) :
    hpair (chartVec i z) (chartVec i z) = 1 + (normSqSum z : ℂ) := by
  rw [hpair, Fin.sum_univ_succAbove _ i]
  simp [normSqSum, Complex.mul_conj']

/- English proof (translation)
Establish `hS` using `one_add_normSqSum_pos z`. Establish `h1 : ∑ a, ∑ b, (1 : Matrix (Fin N) (Fin N) ℂ) a b * ξ a * conj (η b) = ∑ a, ξ a * conj (η a)`. Simplify using `[Matrix.one_apply]`. Establish `h2 : ∑ a, ∑ b, conj (z a) * z b * ξ a * conj (η b) = (∑ a, ξ a * conj (z a)) * ∑ b, z b * conj (η b)`. Rewrite using `[Finset.sum_mul_sum]`.

Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Establish `hpt : ∀ a b, chernCoeff i z a b * ξ a * conj (η b) = ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) * ((1 : Matrix (Fin N) (Fin N) ℂ) a b * ξ a * conj (η b)) - ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) * (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) * (conj (z a) * z b * ξ a * conj …`. Introduce `a b`. Rewrite using `[chernCoeff_apply]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2]`. Rewrite using `[fsHerm, hpair_liftVec_liftVec, hpair_chartVec_self, hpair_liftVec_chartVec, hpair_chartVec_liftVec]`. Establish `hS' : (1 + (normSqSum z : ℂ)) ≠ 0` using `by exact_mod_cast hS.ne'`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem chernForm_eq_fsHerm (i : Fin (N + 1)) (z ξ η : Fin N → ℂ) :
    ∑ a, ∑ b, chernCoeff i z a b * ξ a * conj (η b) =
      fsHerm (chartVec i z) (liftVec i ξ) (liftVec i η) := by
  have hS := one_add_normSqSum_pos z
  have h1 : ∑ a, ∑ b, (1 : Matrix (Fin N) (Fin N) ℂ) a b * ξ a * conj (η b) =
      ∑ a, ξ a * conj (η a) := by
    simp [Matrix.one_apply]
  have h2 : ∑ a, ∑ b, conj (z a) * z b * ξ a * conj (η b) =
      (∑ a, ξ a * conj (z a)) * ∑ b, z b * conj (η b) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hpt : ∀ a b, chernCoeff i z a b * ξ a * conj (η b) =
      ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) *
          ((1 : Matrix (Fin N) (Fin N) ℂ) a b * ξ a * conj (η b)) -
        ((1 / (2 * Real.pi * (1 + normSqSum z)) : ℝ) : ℂ) * (((1 + normSqSum z)⁻¹ : ℝ) : ℂ) *
          (conj (z a) * z b * ξ a * conj (η b)) := by
    intro a b; rw [chernCoeff_apply]; ring
  simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2]
  rw [fsHerm, hpair_liftVec_liftVec, hpair_chartVec_self, hpair_liftVec_chartVec,
    hpair_chartVec_liftVec]
  have hS' : (1 + (normSqSum z : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

def transition (i j : Fin (N + 1)) (z : Fin N → ℂ) : Fin N → ℂ := chartCoord j (chartInv i z)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma transition_apply (i j : Fin (N + 1)) (z : Fin N → ℂ) (k : Fin N) :
    transition i j z k = chartVec i z (j.succAbove k) / chartVec i z j := rfl

def liftCLM (i : Fin (N + 1)) : (Fin N → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := liftVec i
      map_add' := fun ξ η => by
        funext m
        obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp
      map_smul' := fun c ξ => by
        funext m
        obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp }

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma liftCLM_apply (i : Fin (N + 1)) (ξ : Fin N → ℂ) : liftCLM i ξ = liftVec i ξ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `m`. Apply the tactic sequence `obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp`.
-/
lemma chartVec_eq_add (i : Fin (N + 1)) (z : Fin N → ℂ) :
    chartVec i z = chartVec i 0 + liftVec i z := by
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m <;> simp

/- English proof (translation)
Establish `h : chartVec (N` using `N) i = fun w => chartVec i 0 + liftCLM i w := by`. Use function extensionality and compare the values at `w`. Conclude with `chartVec_eq_add i w`. Rewrite using `[h]`. Conclude with `(liftCLM i).hasFDerivAt.const_add _`.
-/
lemma hasFDerivAt_chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) :
    HasFDerivAt (chartVec (N := N) i) (liftCLM i) z := by
  have h : chartVec (N := N) i = fun w => chartVec i 0 + liftCLM i w := by
    funext w; exact chartVec_eq_add i w
  rw [h]
  exact (liftCLM i).hasFDerivAt.const_add _

/- English proof (translation)
Establish `hc` using `hasFDerivAt_pi'.mp (hasFDerivAt_chartVec (N := N) i z)`. Establish `hfun : transition (N` using `N) i j = fun w k => chartVec i w (j.succAbove k) * (chartVec i w j)⁻¹ := by`. Use function extensionality and compare the values at `w k`. Rewrite using `[transition_apply, div_eq_mul_inv]`. Rewrite using `[hfun]`.

Use `hasFDerivAt_pi.mpr fun k => ?_` and prove the remaining obligations. Conclude with `(hc (j.succAbove k)).mul ((hasDerivAt_inv hz).comp_hasFDerivAt z (hc j))`.
-/
theorem hasFDerivAt_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    HasFDerivAt (transition i j) (ContinuousLinearMap.pi fun k =>
      chartVec i z (j.succAbove k) • ((-(chartVec i z j ^ 2)⁻¹) •
          (ContinuousLinearMap.proj j).comp (liftCLM i)) +
        (chartVec i z j)⁻¹ • (ContinuousLinearMap.proj (j.succAbove k)).comp (liftCLM i)) z := by
  have hc := hasFDerivAt_pi'.mp (hasFDerivAt_chartVec (N := N) i z)
  have hfun : transition (N := N) i j =
      fun w k => chartVec i w (j.succAbove k) * (chartVec i w j)⁻¹ := by
    funext w k; rw [transition_apply, div_eq_mul_inv]
  rw [hfun]
  refine hasFDerivAt_pi.mpr fun k => ?_
  exact (hc (j.succAbove k)).mul ((hasDerivAt_inv hz).comp_hasFDerivAt z (hc j))

/- English proof (translation)
The claim follows from `(hasFDerivAt_transition i j hz).differentiableAt`.
-/
lemma differentiableAt_transition (i j : Fin (N + 1)) {z : Fin N → ℂ}
    (hz : chartVec i z j ≠ 0) : DifferentiableAt ℂ (transition i j) z :=
  (hasFDerivAt_transition i j hz).differentiableAt

/- English proof (translation)
Rewrite using `[(hasFDerivAt_transition i j hz).fderiv]`. Use function extensionality and compare the values at `m`. Take `rfl | ⟨k, rfl⟩` from `Fin.eq_self_or_eq_succAbove j m`. Simplify using `only [liftVec_self, Pi.smul_apply, Pi.add_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [liftVec_succAbove, ContinuousLinearMap.pi_apply, FunLike.coe_add, FunLike.coe_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, liftCLM_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem liftVec_fderiv_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (ξ : Fin N → ℂ) :
    liftVec j (fderiv ℂ (transition i j) z ξ) = (chartVec i z j)⁻¹ •
      (liftVec i ξ + (-(liftVec i ξ j / chartVec i z j)) • chartVec i z) := by
  rw [(hasFDerivAt_transition i j hz).fderiv]
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j m
  · simp only [liftVec_self, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [liftVec_succAbove, ContinuousLinearMap.pi_apply, FunLike.coe_add,
      FunLike.coe_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      liftCLM_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring

/- English proof (translation)
Use function extensionality and compare the values at `m`. Take `rfl | ⟨k, rfl⟩` from `Fin.eq_self_or_eq_succAbove j m`. Simplify using `[hz]`. Simplify using `only [chartVec_succAbove, transition_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[div_eq_mul_inv, mul_comm]`.
-/
lemma chartVec_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    chartVec j (transition i j z) = (chartVec i z j)⁻¹ • chartVec i z := by
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j m
  · simp [hz]
  · simp only [chartVec_succAbove, transition_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]

/- English proof (translation)
Rewrite using `[chernForm_eq_fsHerm, chernForm_eq_fsHerm, chartVec_transition i j hz, liftVec_fderiv_transition i j hz, liftVec_fderiv_transition i j hz, fsHerm_smul (inv_ne_zero hz), fsHerm_add_smul]`.
-/
theorem chernForm_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (ξ η : Fin N → ℂ) :
    ∑ a, ∑ b, chernCoeff i z a b * ξ a * conj (η b) =
      ∑ a, ∑ b, chernCoeff j (transition i j z) a b * fderiv ℂ (transition i j) z ξ a *
        conj (fderiv ℂ (transition i j) z η b) := by
  rw [chernForm_eq_fsHerm, chernForm_eq_fsHerm, chartVec_transition i j hz,
    liftVec_fderiv_transition i j hz, liftVec_fderiv_transition i j hz,
    fsHerm_smul (inv_ne_zero hz), fsHerm_add_smul]

def transitionJac (i j : Fin (N + 1)) (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toMatrix' (fderiv ℂ (transition i j) z : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))

/- English proof (translation)
Simplify using `[transitionJac, LinearMap.toMatrix'_apply]`.
-/
lemma fderiv_transition_single (i j : Fin (N + 1)) (z : Fin N → ℂ) (b a : Fin N) :
    fderiv ℂ (transition i j) z (Pi.single b 1) a = transitionJac i j z a b := by
  simp [transitionJac, LinearMap.toMatrix'_apply]

/- English proof (translation)
Use extensionality with `b d`. Establish `h` using `chernForm_transition i j hz (Pi.single b 1) (Pi.single d 1)`. Simplify using `only [fderiv_transition_single] at h`. Simplify using `[Pi.single_apply] at h`. Rewrite using `[h, Matrix.mul_apply]`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem chernCoeff_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    chernCoeff i z = (transitionJac i j z)ᵀ * chernCoeff j (transition i j z) *
      (transitionJac i j z).map conj := by
  ext b d
  have h := chernForm_transition i j hz (Pi.single b 1) (Pi.single d 1)
  simp only [fderiv_transition_single] at h
  simp [Pi.single_apply] at h
  rw [h, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Rewrite using `[chernCoeff_transition i j hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_chernCoeff_transition (i j : Fin (N + 1)) {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    (chernCoeff i z).det =
      (Complex.normSq (transitionJac i j z).det : ℂ) * (chernCoeff j (transition i j z)).det := by
  rw [chernCoeff_transition i j hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Complex.mul_conj]
  ring

/- English proof (translation)
Rewrite using `[((hasFDerivAt_transition i j hz).restrictScalars ℝ).fderiv, ← (hasFDerivAt_transition i j hz).fderiv, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, transitionJac, LinearMap.det_toMatrix']`.
-/
theorem det_fderiv_real_transition (i j : Fin (N + 1)) {z : Fin N → ℂ}
    (hz : chartVec i z j ≠ 0) :
    (fderiv ℝ (transition i j) z).det = Complex.normSq (transitionJac i j z).det := by
  rw [((hasFDerivAt_transition i j hz).restrictScalars ℝ).fderiv, ← (hasFDerivAt_transition i j hz).fderiv,
    ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, transitionJac, LinearMap.det_toMatrix']

/- English proof (translation)
The claim follows from `|(fderiv ℝ (transition i j) z).det| * fsVolumeDensity j (transition i j z) := by rw [det_fderiv_real_transition i j hz, abs_of_nonneg (Complex.normSq_nonneg _), fsVolumeDensity, fsVolumeDensity, det_chernCoeff_transition i j hz, Complex.re_ofReal_mul] ring`.
-/
theorem fsVolumeDensity_transition (i j : Fin (N + 1)) {z : Fin N → ℂ}
    (hz : chartVec i z j ≠ 0) :
    fsVolumeDensity i z =
      |(fderiv ℝ (transition i j) z).det| * fsVolumeDensity j (transition i j z) := by
  rw [det_fderiv_real_transition i j hz, abs_of_nonneg (Complex.normSq_nonneg _), fsVolumeDensity,
    fsVolumeDensity, det_chernCoeff_transition i j hz, Complex.re_ofReal_mul]
  ring

end CP

end

end GroundTheory.Heights₂.Heights
