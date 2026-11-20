import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPosStatement

open GlobalTheory.ShFam.Hor
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `n a g ha ρ₁ τ B hρ0 hρ1 hdiff hpos hmon k v`. Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Use `set j : Fin n := Fin.castLE ha k with hj`.

Establish `hjlt : (j : ℕ) < a` using `by simp [hj]`. Set `s₀ : Fin n → ℂ` to `fun i => if (i : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0`. Set `u : ℂ → Fin n → ℂ` to `fun t => Function.update s₀ j t`. Set `D` to `{s : Fin n → ℂ | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}`. Establish `hlog2 : Real.log (ρ₁ / 2) < 0` using `Real.log_neg (by positivity) (by linarith)`.

Establish `hlogle : Real.log ρ₁ ≤ 0` using `Real.log_nonpos hρ0.le hρ1`. Establish `hexp2 : Real.exp (Real.log (ρ₁ / 2)) = ρ₁ / 2` using `Real.exp_log (by positivity)`. Establish `hmem : ∀ t : ℂ, t.re < Real.log ρ₁ → u t ∈ D`. Introduce `t ht`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `only [u, Function.update_self, hjlt, if_true]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [u, Function.update_of_ne hi, s₀] split_ifs with h`. Simplify using `using hlog2`. Simplify using the standard rewrite rules. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff hρ0]`. Introduce `i`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Simplify using `only [logExp, u, Function.update_self, hjlt, if_true, Complex.norm_exp]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [logExp, u, Function.update_of_ne hi, s₀] split_ifs with h`.

Rewrite using `[Complex.norm_exp, Complex.ofReal_re, hexp2]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using hρ0`. Set `v' : Fin g → ℂ` to `fun i => (v i : ℂ)`. Set `f : ℂ → ℂ` to `fun t => v' ⬝ᵥ (τ (u t) *ᵥ v')`.

Establish `hshift : ∀ t : ℂ, u (t + 2 * Real.pi * Complex.I) = u t + Pi.single j (2 * Real.pi * Complex.I)`. Introduce `t`. Use extensionality with `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality.

Simplify using `[u]`. Simplify using `[u, hi, Function.update_of_ne hi, Pi.single_apply]`. Establish `hcast : v' ⬝ᵥ ((B k).map (Int.cast : ℤ → ℂ) *ᵥ v') = ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ)`. Simplify using `[v', dotProduct, Matrix.mulVec, Matrix.map_apply]`. Establish `hper : ∀ t : ℂ, t.re < Real.log ρ₁ → f (t + 2 * Real.pi * Complex.I) = f t + ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ)`.

Introduce `t ht`. Establish `h1` using `hmon (u t) (hmem t ht).1 (hmem t ht).2 k`. Simplify using `only [f]`. Rewrite using `[hshift t, h1, Matrix.add_mulVec, dotProduct_add, hcast]`. Set `v'' : Fin g → ℝ` to `fun i => (v i : ℝ)`.

Establish `hv'' : v'' ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun h0 i` as an intermediate fact.

Simplify `this` using `[v'']`. Establish `him : ∀ t : ℂ, t.re < Real.log ρ₁ → 0 < (f t).im`. Introduce `t ht`. Establish `hp` using `((hpos (u t) (hmem t ht).1 (hmem t ht).2).2).dotProduct_mulVec_pos hv''`. Establish `heq : (f t).im = star v'' ⬝ᵥ (((τ (u t)).map Complex.im) *ᵥ v'')`.

Simplify using `[f, v', v'', dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum]`. Rewrite using `[heq]`. Conclude with `hp`. Establish `hu : Differentiable ℂ u` using `fun t => (hasFDerivAt_update s₀ t).differentiableAt`. Establish `hent : ∀ i l, DifferentiableOn ℂ (fun t => τ (u t) i l) {t : ℂ | t.re < Real.log ρ₁}` using `fun i l => (hdiff i l).comp hu.differentiableOn (fun t ht => hmem t ht)`.

Establish `hdf : DifferentiableOn ℂ f {t : ℂ | t.re < Real.log ρ₁}`. Simplify using `only [f, dotProduct, Matrix.mulVec]`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `i _`. Apply `DifferentiableOn.const_mul` to reduce the goal to its premises.

Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `l _`. Conclude with `(hent i l).mul_const _`. Conclude with `GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos (Real.log ρ₁) f (v ⬝ᵥ (B k *ᵥ v)) hdf hper him` after adjusting the coercions.
-/
theorem monodromy_dotProduct_nonneg : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  intro n a g ha ρ₁ τ B hρ0 hρ1 hdiff hpos hmon k v
  by_cases hv : v = 0
  · subst hv; simp
  set j : Fin n := Fin.castLE ha k with hj
  have hjlt : (j : ℕ) < a := by simp [hj]
  let s₀ : Fin n → ℂ := fun i => if (i : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0
  let u : ℂ → Fin n → ℂ := fun t => Function.update s₀ j t
  let D := {s : Fin n → ℂ | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}
  have hlog2 : Real.log (ρ₁ / 2) < 0 := Real.log_neg (by positivity) (by linarith)
  have hlogle : Real.log ρ₁ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hexp2 : Real.exp (Real.log (ρ₁ / 2)) = ρ₁ / 2 := Real.exp_log (by positivity)
  have hmem : ∀ t : ℂ, t.re < Real.log ρ₁ → u t ∈ D := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi
        simp only [u, Function.update_self, hjlt, if_true]
        linarith
      · simp only [u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · simpa using hlog2
        · simp
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ0]
      intro i
      by_cases hi : i = j
      · subst hi
        simp only [logExp, u, Function.update_self, hjlt, if_true, Complex.norm_exp]
        calc Real.exp t.re < Real.exp (Real.log ρ₁) := Real.exp_lt_exp.2 ht
          _ = ρ₁ := Real.exp_log hρ0
      · simp only [logExp, u, Function.update_of_ne hi, s₀]
        split_ifs with h
        · rw [Complex.norm_exp, Complex.ofReal_re, hexp2]; linarith
        · simpa using hρ0
  let v' : Fin g → ℂ := fun i => (v i : ℂ)
  let f : ℂ → ℂ := fun t => v' ⬝ᵥ (τ (u t) *ᵥ v')
  have hshift : ∀ t : ℂ, u (t + 2 * Real.pi * Complex.I) = u t + Pi.single j (2 * Real.pi * Complex.I) := by
    intro t
    ext i
    by_cases hi : i = j
    · subst hi; simp [u]
    · simp [u, hi, Function.update_of_ne hi, Pi.single_apply]
  have hcast : v' ⬝ᵥ ((B k).map (Int.cast : ℤ → ℂ) *ᵥ v') = ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    simp [v', dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hper : ∀ t : ℂ, t.re < Real.log ρ₁ → f (t + 2 * Real.pi * Complex.I) = f t + ((v ⬝ᵥ (B k *ᵥ v) : ℤ) : ℂ) := by
    intro t ht
    have h1 := hmon (u t) (hmem t ht).1 (hmem t ht).2 k
    simp only [f]
    rw [hshift t, h1, Matrix.add_mulVec, dotProduct_add, hcast]
  let v'' : Fin g → ℝ := fun i => (v i : ℝ)
  have hv'' : v'' ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa [v''] using this
  have him : ∀ t : ℂ, t.re < Real.log ρ₁ → 0 < (f t).im := by
    intro t ht
    have hp := ((hpos (u t) (hmem t ht).1 (hmem t ht).2).2).dotProduct_mulVec_pos hv''
    have heq : (f t).im = star v'' ⬝ᵥ (((τ (u t)).map Complex.im) *ᵥ v'') := by
      simp [f, v', v'', dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum]
    rw [heq]; exact hp
  have hu : Differentiable ℂ u := fun t => (hasFDerivAt_update s₀ t).differentiableAt
  have hent : ∀ i l, DifferentiableOn ℂ (fun t => τ (u t) i l) {t : ℂ | t.re < Real.log ρ₁} :=
    fun i l => (hdiff i l).comp hu.differentiableOn (fun t ht => hmem t ht)
  have hdf : DifferentiableOn ℂ f {t : ℂ | t.re < Real.log ρ₁} := by
    simp only [f, dotProduct, Matrix.mulVec]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.fun_sum
    intro l _
    exact (hent i l).mul_const _
  exact_mod_cast GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos (Real.log ρ₁) f (v ⬝ᵥ (B k *ᵥ v)) hdf hper him

end GlobalTheory
