import ReciprocityTheory.SemistableReduction.SphereTorusA

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

def scaledTorusMean {ι : Type*} [Fintype ι] (r : ι → ℂ) (f : MvPolynomial ι ℂ) : ℝ :=
  ∫ θ, Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖ ∂(torusProb ι)

/- English proof (translation)
Unfold `scaledTorusMean torusMean`. Simplify using `only [one_mul]`.
-/
theorem scaledTorusMean_one {ι : Type*} [Fintype ι] (f : MvPolynomial ι ℂ) :
    scaledTorusMean (fun _ => 1) f = torusMean f := by
  unfold scaledTorusMean torusMean
  simp only [one_mul]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Simplify using the standard rewrite rules. Simplify the hypotheses and the goal together. Name the introduced variables `p j hp`. Simplify using `only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, Polynomial.eval_mul, hp]`.

Use `congr 1`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Function.update_of_ne h]`.
-/
theorem eval_update_eq_eval_aeval {ι : Type*} [DecidableEq ι] (w : ι → ℂ) (i : ι) (z : ℂ)
    (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (Function.update w i z) f =
      (MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (w j)) f).eval z := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  rename_i p j hp
  simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X, Polynomial.eval_mul, hp]
  congr 1
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Function.update_of_ne h]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Simplify using the standard rewrite rules. Simplify the hypotheses and the goal together. Simplify the hypotheses and the goal together.
-/
theorem eval_bind₁_scale {ι : Type*} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  · simp_all

/- English proof (translation)
Introduce `h`. Apply `hf` to reduce the goal to its premises. Use `MvPolynomial.funext fun v => ?_` and prove the remaining obligations. Establish `hv` using `eval_bind₁_scale r (fun j => v j / r j) f`. Rewrite `hv` using `[h, map_zero]`.

Establish `e : (fun j => r j * (v j / r j)) = v`. Use function extensionality and compare the values at `j`. Use `first`. Consider the case `exact mul_div_cancel₀ (v j) (hr j)`. Consider the case `field_simp [hr j]`.

Consider the case `(rw [mul_comm]; exact div_mul_cancel₀ (v j) (hr j))`. Rewrite `hv` using `[e]`. Rewrite using `[← hv, map_zero]`.
-/
private theorem bind1_C_mul_X_ne_zero_of_ne_zero {ι : Type} (r : ι → ℂ) (hr : ∀ j, r j ≠ 0)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f ≠ 0 := by
  intro h
  apply hf
  refine MvPolynomial.funext fun v => ?_
  have hv := eval_bind₁_scale r (fun j => v j / r j) f
  rw [h, map_zero] at hv
  have e : (fun j => r j * (v j / r j)) = v := by
    funext j
    first
      | exact mul_div_cancel₀ (v j) (hr j)
      | field_simp [hr j]
      | (rw [mul_comm]; exact div_mul_cancel₀ (v j) (hr j))
  rw [e] at hv
  rw [← hv, map_zero]

/- English proof (translation)
Establish `h` using `(hBasic ι).1 _ (bind1_C_mul_X_ne_zero_of_ne_zero r hr f hf)`. Simplify `h` using `only [eval_bind₁_scale]`.
-/
theorem integrable_scaled {ι : Type} [Fintype ι] (hBasic : TorusMeanBasicStatement)
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ) (hr : ∀ j, r j ≠ 0) :
    Integrable (fun θ => Real.log ‖MvPolynomial.eval (fun j => r j * torusPoint θ j) f‖)
      (torusProb ι) := by
  have h := (hBasic ι).1 _ (bind1_C_mul_X_ne_zero_of_ne_zero r hr f hf)
  simpa only [eval_bind₁_scale] using h

/- English proof (translation)
Establish `hr' : ∀ j, Function.update r i 1 j ≠ 0`. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne h]`. Conclude with `hr j`. Take `⟨hI1, hE1⟩` from `integral_torus_eq_iter i (integrable_scaled hBasic f hf r hr)`. Take `⟨hI2, hE2⟩` from `integral_torus_eq_iter i (integrable_scaled hBasic f hf _ hr')`. Unfold `scaledTorusMean`.

Rewrite using `[hE1, hE2]`. Use `integral_mono hI1 hI2 fun x => ?_` and prove the remaining obligations. Use `set p : Polynomial ℂ := MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ) else Polynomial.C (r j * torusPoint x j)) f`. Establish `key : ∀ (s : ι → ℂ), (∀ j, j ≠ i → s j = r j) → ∀ t : ℝ, MvPolynomial.eval (fun j => s j * torusPoint (Function.update x i t) j) f = p.eval (s i * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))`. Introduce `s hs t`.

Rewrite using `[← eval_update_eq_eval_aeval]`. Use `congrArg (fun w => MvPolynomial.eval w f) (funext fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[torusPoint]`.

Simplify using `[Function.update_of_ne h, hs j h, torusPoint]`. Establish `k1` using `key r (fun _ _ => rfl)`. Establish `k2` using `key (Function.update r i 1) (fun j h => Function.update_of_ne h _ _)`. Simplify using `only [Function.update_self, one_mul] at k2`. Use `beta_reduce`.

Simplify using `only [k1, k2]`. Conclude with `integral_log_eval_mul_le p (hr i) hri`.
-/
theorem scaledTorusMean_le_update {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (i : ι) (hri : ‖r i‖ ≤ 1) :
    scaledTorusMean r f ≤ scaledTorusMean (Function.update r i 1) f := by
  have hr' : ∀ j, Function.update r i 1 j ≠ 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · rw [Function.update_of_ne h]; exact hr j
  obtain ⟨hI1, hE1⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf r hr)
  obtain ⟨hI2, hE2⟩ := integral_torus_eq_iter i (integrable_scaled hBasic f hf _ hr')
  unfold scaledTorusMean
  rw [hE1, hE2]
  refine integral_mono hI1 hI2 fun x => ?_
  set p : Polynomial ℂ := MvPolynomial.aeval (fun j => if j = i then (Polynomial.X : Polynomial ℂ)
        else Polynomial.C (r j * torusPoint x j)) f
  have key : ∀ (s : ι → ℂ), (∀ j, j ≠ i → s j = r j) → ∀ t : ℝ,
      MvPolynomial.eval (fun j => s j * torusPoint (Function.update x i t) j) f =
        p.eval (s i * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) := by
    intro s hs t
    rw [← eval_update_eq_eval_aeval]
    refine congrArg (fun w => MvPolynomial.eval w f) (funext fun j => ?_)
    by_cases h : j = i
    · subst h; simp [torusPoint]
    · simp [Function.update_of_ne h, hs j h, torusPoint]
  have k1 := key r (fun _ _ => rfl)
  have k2 := key (Function.update r i 1) (fun j h => Function.update_of_ne h _ _)
  simp only [Function.update_self, one_mul] at k2
  beta_reduce
  simp only [k1, k2]
  exact integral_log_eval_mul_le p (hr i) hri

/- English proof (translation)
Establish `key : ∀ s : Finset ι, scaledTorusMean r f ≤ scaledTorusMean (fun j => if j ∈ s then (1 : ℂ) else r j) f`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a s ha ih`.

Use `ih.trans ?_` and prove the remaining obligations. Apply the tactic sequence `have hr' : ∀ j, (fun j => if j ∈ s then (1 : ℂ) else r j) j ≠ 0 := fun j => by dsimp only split_ifs <;> simp [hr j]`. Establish `hra : ‖(fun j => if j ∈ s then (1 : ℂ) else r j) a‖ ≤ 1`. Simplify using `[ha, hr1 a]`. Establish `hle` using `scaledTorusMean_le_update hBasic f hf _ hr' a hra`.

Establish `e : Function.update (fun j => if j ∈ s then (1 : ℂ) else r j) a 1 = fun j => if j ∈ insert a s then (1 : ℂ) else r j`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Finset.mem_insert, hj, Function.update_of_ne hj]`. Rewrite `hle` using `[e]`. Conclude with `hle`. Establish `hu` using `key Finset.univ`. Simplify using `only [Finset.mem_univ, if_true] at hu`.

Rewrite `hu` using `[scaledTorusMean_one]`. Then use the resulting hypothesis.
-/
theorem scaledTorusMean_le_torusMean {ι : Type} [Fintype ι] [DecidableEq ι]
    (hBasic : TorusMeanBasicStatement) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) (r : ι → ℂ)
    (hr : ∀ j, r j ≠ 0) (hr1 : ∀ j, ‖r j‖ ≤ 1) :
    scaledTorusMean r f ≤ torusMean f := by
  classical
  have key : ∀ s : Finset ι, scaledTorusMean r f ≤
      scaledTorusMean (fun j => if j ∈ s then (1 : ℂ) else r j) f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      refine ih.trans ?_
      have hr' : ∀ j, (fun j => if j ∈ s then (1 : ℂ) else r j) j ≠ 0 := fun j => by
        dsimp only
        split_ifs <;> simp [hr j]
      have hra : ‖(fun j => if j ∈ s then (1 : ℂ) else r j) a‖ ≤ 1 := by
        simp [ha, hr1 a]
      have hle := scaledTorusMean_le_update hBasic f hf _ hr' a hra
      have e : Function.update (fun j => if j ∈ s then (1 : ℂ) else r j) a 1 =
          fun j => if j ∈ insert a s then (1 : ℂ) else r j := by
        funext j
        by_cases hj : j = a
        · subst hj
          simp
        · simp [Finset.mem_insert, hj, Function.update_of_ne hj]
      rw [e] at hle
      exact hle
  have hu := key Finset.univ
  simp only [Finset.mem_univ, if_true] at hu
  rwa [scaledTorusMean_one] at hu

end ReciprocityTheory.MultiplicativeHeights
