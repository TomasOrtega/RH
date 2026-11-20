import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HasDerivAtPhi

noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `a j`. Simplify using `[scal, aH]`.
-/
theorem scal_zero (X : Fin n → ℝ) (y : Fin m → Fin n → ℂ) : scal (aH X 0) y = y := by
  funext a j; simp [scal, aH]

/- English proof (translation)
The claim follows from `continuous_pi fun a => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp (continuous_apply a))`.
-/
theorem continuous_scal (α : Fin n → ℝ) : Continuous (scal (m := m) α) :=
  continuous_pi fun a => continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

/- English proof (translation)
Unfold `gs`. Use `fun_prop`.
-/
theorem continuous_gs (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  unfold gs; fun_prop

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => continuous_evX _`.
-/
theorem continuous_gramX (ε : Fin m → Bool) : Continuous (gramX (n := n) ε) :=
  continuous_pi fun i => continuous_pi fun j => continuous_evX _

/- English proof (translation)
Simplify using `only [aH, ← Real.exp_nat_mul, ← Real.exp_sum]`. Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_aH (X : Fin n → ℝ) (h : ℝ) :
    (∏ j, aH X h j ^ (2 * m) : ℝ) = Real.exp (2 * (h * ((m : ℝ) * ∑ j, X j))) := by
  simp only [aH, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/- English proof (translation)
Introduce `m n ε c t hc X b hb Q`. Use `set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr`. Use `set E : (Fin m → Fin n → ℂ) → ℂ := fun y => Complex.exp (Complex.I * t * (b * gramX ε y).trace) with hEdef`. Establish `hE : ∀ y, ‖E y‖ = 1` using `fun y => norm_phase t _ (trace_im ε y hb)`. Establish `hEc : Continuous E`.

Use `Complex.continuous_exp.comp (continuous_const.mul ?_)` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace`. Use `set A : ℝ := (m : ℝ) * ∑ j, X j with hA`. Use `set P' : PX m n := dil c X Q - ((m : ℂ) * ∑ j, (X j : ℂ)) • Q with hP'`. Set `φ : ℝ → (Fin m → Fin n → ℂ) → ℂ` to `fun s y => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y) * E y`.

Set `φ' : ℝ → (Fin m → Fin n → ℂ) → ℂ` to `fun s y => evX P' (scal (aH X s) y) * gs c (scal (aH X s) y) * E y`. Establish `hφc : ∀ (P : PX m n) (s : ℝ), Continuous fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y` using `fun P s => (((continuous_evX P).comp (continuous_scal _)).mul ((continuous_gs c).comp (continuous_scal _))).mul hEc`. Establish `hH : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `hint : Integrable (fun y : Fin m → Fin n → ℂ => (1 + ‖y‖) ^ (-r))`. Establish `: ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ)) < r` using `by rw [hr]; linarith`.

Conclude with `integrable_one_add_norm this`. Establish `hdomI : ∀ (P : PX m n), ∃ K : ℝ, ∀ s : ℝ, |s| < 1 → ∀ y, ‖evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y‖ ≤ K * (1 + ‖y‖) ^ (-r)`. Introduce `P`. Take `⟨K, -, hK⟩` from `dom_bound c hc X P`. Conclude with `⟨K, fun s hs y => by rw [norm_mul, hE, mul_one]; exact hK s hs y⟩`.

Establish `hintP : ∀ (P : PX m n) (s : ℝ), |s| < 1 → Integrable fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y`. Introduce `P s hs`. Take `⟨K, hK⟩` from `hdomI P`. Conclude with `Integrable.mono' (hint.const_mul K) (hφc P s).aestronglyMeasurable (Eventually.of_forall fun y => hK s hs y)`. Establish `key : ∀ h : ℝ, Complex.exp (-((h * A : ℝ) : ℂ)) * secN ε c t Q (bS X h b) = Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y`.

Introduce `h`. Establish `hpos : ∀ j, 0 < aH X h j` using `fun j => Real.exp_pos _`. Establish `h1 : secN ε c t Q (bS X h b) = ((∏ j, aH X h j ^ (2 * m) : ℝ) : ℂ) * ∫ y, φ h y`. Unfold `secN`. Rewrite using `[integral_scal (aH X h) hpos]`.

Use `congr 1`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [φ, hEdef, trace_scal]`. Rewrite using `[h1, prod_aH, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`.

Rewrite using `[hA]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨K, hK⟩` from `hdomI P'`. Establish `hΨ` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := φ) (F' := φ') (x₀ := (0 : ℝ)) (bound := fun y => K * (1 + ‖y‖) ^ (-r)) (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Eventually.of_forall fun s => (hφc Q s).aestronglyMeasurable) (hintP Q 0 (by simp)) ((hφc P' 0).aest …`.

Use `(hasDerivAt_phi c X Q y s).mul_const (E y)` as an intermediate fact. Use `this.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [φ', hP', evX_eq, map_sub, smul_eval])`. Establish `hexp : HasDerivAt (fun h : ℝ => Complex.exp (((h * A : ℝ) : ℂ))) (Complex.exp (((0 * A : ℝ) : ℂ)) * (A : ℂ)) 0` using `(((hasDerivAt_id (0 : ℝ)).mul_const A).ofReal_comp).cexp.congr_deriv (by simp)`. Establish `hF` using `hexp.mul hΨ.2`.

Establish `hfun : (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) = fun h => Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y` using `funext key`. Rewrite using `[hfun]`. Use `hF.congr_deriv ?_` and prove the remaining obligations. Establish `hφ0 : ∀ y, φ 0 y = evX Q y * gs c y * E y` using `fun y => by simp only [φ, scal_zero]`. Establish `hφ'0 : ∀ y, φ' 0 y = evX P' y * gs c y * E y` using `fun y => by simp only [φ', scal_zero]`.

Establish `hI1` using `hintP Q 0 (by simp)`. Establish `hI2` using `hintP P' 0 (by simp)`. Simplify using `only [scal_zero] at hI1 hI2`. Establish `hdil : ∀ y, evX (dil c X Q) y * gs c y * E y = ((m : ℂ) * ∑ j, (X j : ℂ)) * (evX Q y * gs c y * E y) + evX P' y * gs c y * E y`. Introduce `y`.

Simplify using `only [hP', evX_eq, map_sub, smul_eval]`. Expand and normalize the polynomial expressions, which then agree. Unfold `secN`. Simplify using `only [hφ0, hφ'0, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]`. Rewrite using `[integral_congr_ae (Eventually.of_forall hdil), integral_add (hI1.const_mul _) hI2, integral_const_mul]`.

Simplify using `only [hEdef, hA]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussPart : GaussPart := by
  intro m n ε c t hc X b hb Q
  set r : ℝ := (Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ) + 1 with hr
  set E : (Fin m → Fin n → ℂ) → ℂ := fun y => Complex.exp (Complex.I * t * (b * gramX ε y).trace) with hEdef
  have hE : ∀ y, ‖E y‖ = 1 := fun y => norm_phase t _ (trace_im ε y hb)
  have hEc : Continuous E := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact (continuous_const.matrix_mul (continuous_gramX ε)).matrix_trace
  set A : ℝ := (m : ℝ) * ∑ j, X j with hA
  set P' : PX m n := dil c X Q - ((m : ℂ) * ∑ j, (X j : ℂ)) • Q with hP'
  let φ : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX Q (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  let φ' : ℝ → (Fin m → Fin n → ℂ) → ℂ := fun s y => evX P' (scal (aH X s) y) * gs c (scal (aH X s) y) * E y
  have hφc : ∀ (P : PX m n) (s : ℝ), Continuous fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y :=
    fun P s => (((continuous_evX P).comp (continuous_scal _)).mul ((continuous_gs c).comp (continuous_scal _))).mul hEc
  have hH : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun y : Fin m → Fin n → ℂ => (1 + ‖y‖) ^ (-r)) := by
    have : ((Module.finrank ℝ (Fin m → Fin n → ℂ) : ℝ)) < r := by rw [hr]; linarith
    exact integrable_one_add_norm this
  have hdomI : ∀ (P : PX m n), ∃ K : ℝ, ∀ s : ℝ, |s| < 1 → ∀ y,
      ‖evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y‖ ≤ K * (1 + ‖y‖) ^ (-r) := by
    intro P
    obtain ⟨K, -, hK⟩ := dom_bound c hc X P
    exact ⟨K, fun s hs y => by rw [norm_mul, hE, mul_one]; exact hK s hs y⟩
  have hintP : ∀ (P : PX m n) (s : ℝ), |s| < 1 →
      Integrable fun y => evX P (scal (aH X s) y) * gs c (scal (aH X s) y) * E y := by
    intro P s hs
    obtain ⟨K, hK⟩ := hdomI P
    exact Integrable.mono' (hint.const_mul K) (hφc P s).aestronglyMeasurable
      (Eventually.of_forall fun y => hK s hs y)

  have key : ∀ h : ℝ, Complex.exp (-((h * A : ℝ) : ℂ)) * secN ε c t Q (bS X h b) =
      Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := by
    intro h
    have hpos : ∀ j, 0 < aH X h j := fun j => Real.exp_pos _
    have h1 : secN ε c t Q (bS X h b) = ((∏ j, aH X h j ^ (2 * m) : ℝ) : ℂ) * ∫ y, φ h y := by
      unfold secN
      rw [integral_scal (aH X h) hpos]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [φ, hEdef, trace_scal]
    rw [h1, prod_aH, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hA]; push_cast; ring

  obtain ⟨K, hK⟩ := hdomI P'
  have hΨ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := φ) (F' := φ') (x₀ := (0 : ℝ))
    (bound := fun y => K * (1 + ‖y‖) ^ (-r)) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun s => (hφc Q s).aestronglyMeasurable)
    (hintP Q 0 (by simp)) ((hφc P' 0).aestronglyMeasurable)
    (Eventually.of_forall fun y s hs => hK s (by simpa [Real.dist_eq] using hs) y) (hint.const_mul K)
    (Eventually.of_forall fun y s _ => by
      have := (hasDerivAt_phi c X Q y s).mul_const (E y)
      refine this.congr_deriv ?_
      simp only [φ', hP', evX_eq, map_sub, smul_eval])

  have hexp : HasDerivAt (fun h : ℝ => Complex.exp (((h * A : ℝ) : ℂ))) (Complex.exp (((0 * A : ℝ) : ℂ)) * (A : ℂ)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const A).ofReal_comp).cexp.congr_deriv (by simp)
  have hF := hexp.mul hΨ.2
  have hfun : (fun h : ℝ => Complex.exp (-((h * ((m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) * secN ε c t Q (bS X h b)) =
      fun h => Complex.exp (((h * A : ℝ) : ℂ)) * ∫ y, φ h y := funext key
  rw [hfun]
  refine hF.congr_deriv ?_

  have hφ0 : ∀ y, φ 0 y = evX Q y * gs c y * E y := fun y => by simp only [φ, scal_zero]
  have hφ'0 : ∀ y, φ' 0 y = evX P' y * gs c y * E y := fun y => by simp only [φ', scal_zero]
  have hI1 := hintP Q 0 (by simp)
  have hI2 := hintP P' 0 (by simp)
  simp only [scal_zero] at hI1 hI2
  have hdil : ∀ y, evX (dil c X Q) y * gs c y * E y =
      ((m : ℂ) * ∑ j, (X j : ℂ)) * (evX Q y * gs c y * E y) + evX P' y * gs c y * E y := by
    intro y
    simp only [hP', evX_eq, map_sub, smul_eval]
    ring
  unfold secN
  simp only [hφ0, hφ'0, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
  rw [integral_congr_ae (Eventually.of_forall hdil), integral_add (hI1.const_mul _) hI2, integral_const_mul]
  simp only [hEdef, hA]
  push_cast
  ring

end PositivityTheory.Rg.Sw.AbsSt.DF
