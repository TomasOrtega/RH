import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma pt_val {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

/- English proof (translation)
Simplify using `only [pt_val]`. Use `fun_prop`.
-/
private lemma pt_cont {n : ℕ} (i : Fin n) :
    Continuous fun θ : Fin n → UnitAddCircle => ((pt θ i : ℂˣ) : ℂ) := by
  simp only [pt_val]
  fun_prop

/- English proof (translation)
Rewrite using `[pt_val]`. Conclude with `Circle.norm_coe _`.
-/
private lemma pt_norm {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ‖((pt θ i : ℂˣ) : ℂ)‖ = 1 := by
  rw [pt_val]
  exact Circle.norm_coe _

/- English proof (translation)
Unfold `half`. Use `continuous_finset_prod _ (fun p _ => ?_)` and prove the remaining obligations. Establish `h1` using `hc p.1`. Establish `h2` using `hc p.2`. Establish `hne : ∀ x, ((u x p.2 : ℂˣ) : ℂ) ≠ 0` using `fun x => Units.ne_zero _`.

Establish `hq : Continuous fun x => ((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ)` using `h1.div h2 hne`. Use `(continuous_const.sub hq).div (continuous_const.sub (continuous_const.mul hq)) (fun x => ?_)` and prove the remaining obligations. Introduce `h`. Establish `hnq : ‖((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[norm_div, hn, hn, div_one]`.

Establish `h'` using `congrArg norm (sub_eq_zero.mp h).symm`. Rewrite `h'` using `[norm_one, norm_mul, hnq, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma half_cont {X : Type*} [TopologicalSpace X] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ}
    (u : X → Fin n → ℂˣ) (hc : ∀ i, Continuous fun x => ((u x i : ℂˣ) : ℂ))
    (hn : ∀ x i, ‖((u x i : ℂˣ) : ℂ)‖ = 1) :
    Continuous fun x => half (t : ℂ) (u x) := by
  unfold half
  refine continuous_finset_prod _ (fun p _ => ?_)
  have h1 := hc p.1
  have h2 := hc p.2
  have hne : ∀ x, ((u x p.2 : ℂˣ) : ℂ) ≠ 0 := fun x => Units.ne_zero _
  have hq : Continuous fun x => ((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ) := h1.div h2 hne
  refine (continuous_const.sub hq).div (continuous_const.sub (continuous_const.mul hq)) (fun x => ?_)
  intro h
  have hnq : ‖((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ)‖ = 1 := by
    rw [norm_div, hn, hn, div_one]
  have h' := congrArg norm (sub_eq_zero.mp h).symm
  rw [norm_one, norm_mul, hnq, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at h'
  linarith

/- English proof (translation)
Introduce `n t ht0 ht1`. Establish `hinvc : ∀ i, Continuous fun θ : Fin n → UnitAddCircle => (((pt θ)⁻¹ i : ℂˣ) : ℂ)`. Introduce `i`. Simplify using `only [Pi.inv_apply, Units.val_inv_eq_inv_val]`. Conclude with `(pt_cont i).inv₀ (fun θ => Units.ne_zero _)`.

Establish `hinvn : ∀ (θ : Fin n → UnitAddCircle) i, ‖(((pt θ)⁻¹ i : ℂˣ) : ℂ)‖ = 1`. Introduce `θ i`. Simplify using `only [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, pt_norm, inv_one]`. Use `⟨half_cont ht0 ht1 _ pt_cont pt_norm, ?_, ?_, pt_norm⟩` and prove the remaining obligations. Conclude with `(half_cont ht0 ht1 _ pt_cont pt_norm).mul (half_cont ht0 ht1 _ hinvc hinvn)`.

Introduce `p`. Simplify using `only [evalAt_apply, monomialChar_apply, Units.val_zpow_eq_zpow_val]`. Unfold `Finsupp.sum`. Use `continuous_finset_sum _ (fun l _ => ?_)` and prove the remaining obligations. Use `continuous_const.mul (continuous_finset_prod _ (fun i _ => ?_))` and prove the remaining obligations.

Conclude with `(pt_cont i).zpow₀ _ (fun θ => Or.inl (Units.ne_zero _))`.
-/
theorem UpperTheory.Gal.Gen.densCont_pf :
    UpperTheory.Gal.Gen.DensCont := by
  intro n t ht0 ht1
  have hinvc : ∀ i, Continuous fun θ : Fin n → UnitAddCircle => (((pt θ)⁻¹ i : ℂˣ) : ℂ) := by
    intro i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact (pt_cont i).inv₀ (fun θ => Units.ne_zero _)
  have hinvn : ∀ (θ : Fin n → UnitAddCircle) i, ‖(((pt θ)⁻¹ i : ℂˣ) : ℂ)‖ = 1 := by
    intro θ i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, pt_norm, inv_one]
  refine ⟨half_cont ht0 ht1 _ pt_cont pt_norm, ?_, ?_, pt_norm⟩
  · exact (half_cont ht0 ht1 _ pt_cont pt_norm).mul (half_cont ht0 ht1 _ hinvc hinvn)
  · intro p
    simp only [evalAt_apply, monomialChar_apply, Units.val_zpow_eq_zpow_val]
    unfold Finsupp.sum
    refine continuous_finset_sum _ (fun l _ => ?_)
    refine continuous_const.mul (continuous_finset_prod _ (fun i _ => ?_))
    exact (pt_cont i).zpow₀ _ (fun θ => Or.inl (Units.ne_zero _))
