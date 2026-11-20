import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CircleHomEqZpow

open scoped Topology BigOperators

namespace GlobalTheory

open scoped Topology BigOperators in
/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Establish `: Continuous (fun w : Circle => ((w⁻¹ : Circle) : ℂ))` using `continuous_subtype_val.comp continuous_inv`. Use `this using 2 with w` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.
-/
private lemma continuous_circle_toUnits' : Continuous Circle.toUnits := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  have : Continuous (fun w : Circle => ((w⁻¹ : Circle) : ℂ)) :=
    continuous_subtype_val.comp continuous_inv
  convert this using 2 with w
  simp

open scoped Topology BigOperators in
/- English proof (translation)
Establish `h : x * starRingEnd ℂ x = ((‖x‖ : ℂ)) ^ 2`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : starRingEnd ℂ x ≠ 0` using `by simpa using hx`.

Rewrite using `[div_pow, ← h]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma div_norm_sq_eq_div_conj_of_ne_zero (x : ℂ) (hx : x ≠ 0) :
    (x / ‖x‖) ^ 2 = x / starRingEnd ℂ x := by
  have h : x * starRingEnd ℂ x = ((‖x‖ : ℂ)) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc : starRingEnd ℂ x ≠ 0 := by simpa using hx
  rw [div_pow, ← h]
  field_simp

open scoped Topology BigOperators in

/- English proof (translation)
Introduce `ι _ f hf hreal`. Set `g : ι → Circle →* Circle` to `fun i => f.comp ((MonoidHom.mulSingle (fun _ => ℂˣ) i).comp Circle.toUnits)`. Establish `hg : ∀ i, Continuous (g i)` using `fun i => hf.comp ((continuous_mulSingle i).comp continuous_circle_toUnits')`. Use `choose n hn using fun i => _root_.GlobalTheory.circle_hom_eq_zpow (g i) (hg i)`. Establish `heven : ∀ i, Even (n i)`.

Introduce `i`. Establish `h1 : g i (Circle.exp Real.pi) = 1`. Apply `hreal` to reduce the goal to its premises. Introduce `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[Circle.coe_exp, Complex.exp_pi_mul_I]`. Simplify using `[Pi.mulSingle_eq_of_ne hj]`. Rewrite `h1` using `[hn]`. Establish `h2` using `congrArg (fun w : Circle => (w : ℂ)) h1`.

Simplify using `[Circle.coe_exp, Complex.exp_pi_mul_I] at h2`. Break down `Int.even_or_odd (n i) with h | h` into its components or cases. Conclude with `h`. Rewrite `h2` using `[h.neg_one_zpow]`. Evaluate the numerical expressions using `at h2`.

Use `choose k hk using heven`. Use `⟨k, fun z => ?_⟩` and prove the remaining obligations. Establish `hne : ∀ i, ((‖(z i : ℂ)‖ : ℝ) : ℂ) ≠ 0` using `fun i => by simp`. Use `set u : ι → Circle := fun i => Circle.exp (Complex.arg (z i)) with hu_def`. Establish `hu : ∀ i, ((u i : Circle) : ℂ) = (z i : ℂ) / ‖(z i : ℂ)‖`.

Introduce `i`. Rewrite using `[eq_div_iff (hne i), mul_comm]`. Simplify `Complex.norm_mul_exp_arg_mul_I (z i : ℂ)` using `[u, Circle.coe_exp]`. Establish `hz : z = (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) * fun i => Circle.toUnits (u i)`. Use function extensionality and compare the values at `i`.

Use `ext`. Simplify using `only [Pi.mul_apply, Units.val_mul, Units.val_mk0]`. Simplify using `[hu, mul_div_cancel₀ _ (hne i)]`. Establish `hr : f (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) = 1` using `hreal _ fun i => by simp`. Establish `hv : f (fun i => Circle.toUnits (u i)) = ∏ i, g i (u i)` using `by conv_lhs => rw [← Finset.univ_prod_mulSingle (fun i => Circle.toUnits (u i))]`.

Rewrite using `[map_prod]`. Both sides reduce to the same expression. Establish `hfz : f z = ∏ i, g i (u i)` using `by conv_lhs => rw [hz]`. Rewrite using `[map_mul, hr, one_mul, hv]`. Rewrite using `[hfz]`.

Use `(map_prod Circle.coeHom (fun i => g i (u i)) Finset.univ).trans ?_` and prove the remaining obligations. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show ((g i (u i) : Circle) : ℂ) = _`. Rewrite using `[hn, Circle.coe_zpow, hu, hk i, ← two_mul, zpow_mul, zpow_ofNat, div_norm_sq_eq_div_conj_of_ne_zero _ (z i).ne_zero]`.
-/
theorem _root_.GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow :
    ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  intro ι _ f hf hreal
  classical
  let g : ι → Circle →* Circle := fun i =>
    f.comp ((MonoidHom.mulSingle (fun _ => ℂˣ) i).comp Circle.toUnits)
  have hg : ∀ i, Continuous (g i) := fun i =>
    hf.comp ((continuous_mulSingle i).comp continuous_circle_toUnits')
  choose n hn using fun i => _root_.GlobalTheory.circle_hom_eq_zpow (g i) (hg i)
  have heven : ∀ i, Even (n i) := by
    intro i
    have h1 : g i (Circle.exp Real.pi) = 1 := by
      apply hreal
      intro j
      by_cases hj : j = i
      · subst hj
        simp [Circle.coe_exp, Complex.exp_pi_mul_I]
      · simp [Pi.mulSingle_eq_of_ne hj]
    rw [hn] at h1
    have h2 := congrArg (fun w : Circle => (w : ℂ)) h1
    simp [Circle.coe_exp, Complex.exp_pi_mul_I] at h2
    rcases Int.even_or_odd (n i) with h | h
    · exact h
    · rw [h.neg_one_zpow] at h2
      norm_num at h2
  choose k hk using heven
  refine ⟨k, fun z => ?_⟩
  have hne : ∀ i, ((‖(z i : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun i => by simp
  set u : ι → Circle := fun i => Circle.exp (Complex.arg (z i)) with hu_def
  have hu : ∀ i, ((u i : Circle) : ℂ) = (z i : ℂ) / ‖(z i : ℂ)‖ := by
    intro i
    rw [eq_div_iff (hne i), mul_comm]
    simpa [u, Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I (z i : ℂ)
  have hz : z = (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) *
      fun i => Circle.toUnits (u i) := by
    funext i
    ext
    simp only [Pi.mul_apply, Units.val_mul, Units.val_mk0]
    simp [hu, mul_div_cancel₀ _ (hne i)]
  have hr : f (fun i => Units.mk0 ((‖(z i : ℂ)‖ : ℝ) : ℂ) (hne i)) = 1 :=
    hreal _ fun i => by simp
  have hv : f (fun i => Circle.toUnits (u i)) = ∏ i, g i (u i) := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle (fun i => Circle.toUnits (u i))]
    rw [map_prod]
    rfl
  have hfz : f z = ∏ i, g i (u i) := by
    conv_lhs => rw [hz]
    rw [map_mul, hr, one_mul, hv]
  rw [hfz]
  refine (map_prod Circle.coeHom (fun i => g i (u i)) Finset.univ).trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  show ((g i (u i) : Circle) : ℂ) = _
  rw [hn, Circle.coe_zpow, hu, hk i, ← two_mul, zpow_mul, zpow_ofNat,
    div_norm_sq_eq_div_conj_of_ne_zero _ (z i).ne_zero]

end GlobalTheory
