import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative

open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

/- English proof (translation)
Rewrite using `[← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Simplify using `[h, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]`.

Simplify using `[h]`.
-/
private theorem exp_smul_diagonal_I_single_eq_diagonal_exp {n : ℕ} (a : Fin n) (t : ℝ) :
    NormedSpace.exp (t • (Matrix.diagonal fun j : Fin n => if j = a then Complex.I else 0)) =
      Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext j
  by_cases h : j = a
  · simp [h, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]
  · simp [h]

open DerivativeRepresentation in
/- English proof (translation)
Introduce `n ε H _ _ _ σ hU _ E hE v a x hv hx`. Use `set Y : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => if j = a then Complex.I else 0 with hY`. Establish `hYG : Y ∈ lieSet ε` using `by show Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0`. Rewrite using `[hY, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Substitute `h` using the available equality. Simplify using `only [if_true, Pi.star_apply, Pi.add_apply, Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `[h]`. Establish `hact : ReciprocityTheory.ChartRestriction.DS.actM E Y = Complex.I • E a a`. Simplify using `[ReciprocityTheory.ChartRestriction.DS.actM, hY, Matrix.diagonal_apply, ite_smul]`. Establish `hv' : (v : H) ≠ 0` using `by simpa using hv`. Establish `hD : dRep σ Y (v : H) = (Complex.I * x) • (v : H)`.

Rewrite using `[← hE Y hYG v, hact]`. Simplify using `only [hx, LinearMap.smul_apply, Submodule.coe_smul]`. Rewrite using `[mul_smul]`. Use `set u : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 with hu`. Establish `hexp : ∀ t : ℝ, NormedSpace.exp (t • Y) = u t` using `fun t => exp_smul_diagonal_I_single_eq_diagonal_exp a t`.

Establish `huU : ∀ t, u t ∈ UJset ε`. Introduce `t`. Use `show (u t)ᴴ * Formalism.REAL.Jm ε * u t = Formalism.REAL.Jm ε`. Rewrite using `[hu, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Substitute `h` using the available equality. Simplify using `only [if_true, Pi.star_apply]`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_comm _ (if ε j = true then (1 : ℂ) else -1), mul_assoc, ← Complex.exp_add]`.

Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hmul : ∀ s t, u (s + t) = u s * u t`. Introduce `s t`. Simplify using `only [hu, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Simplify using `[h, add_mul, Complex.exp_add]`. Simplify using `[h]`.

Establish `hu0 : u 0 = 1` using `by simp [hu]`. Establish `hu2 : u (2 * Real.pi) = 1`. Simplify using `only [hu]`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Simplify using `[h, Complex.exp_two_pi_mul_I]`. Simplify using `[h]`. Use `set F : ℝ → H := fun t => σ (u t) (v : H) with hFdef`.

Establish `hF : ∀ s t, F (s + t) = σ (u s) (F t)`. Introduce `s t`. Simplify using `only [hFdef, hmul, hU.1.2 _ (huU s) _ (huU t), ContinuousLinearMap.comp_apply]`. Establish `hx0 : x ≠ 0 → HasDerivAt F ((Complex.I * x) • (v : H)) 0`. Introduce `hx0`.

Establish `h1 : deriv F 0 = (Complex.I * x) • (v : H)`. Establish `: F = fun t : ℝ => σ (NormedSpace.exp (t • Y)) (v : H)`. Use function extensionality and compare the values at `t`. Simplify using `only [hFdef, hexp]`. Rewrite using `[this]`.

Conclude with `hD`. Establish `hne : deriv F 0 ≠ 0`. Rewrite using `[h1]`. Conclude with `smul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hx0)) hv'`. Establish `hd : DifferentiableAt ℝ F 0`.

Assume the negation of the conclusion as `hnd`. Conclude with `hne (deriv_zero_of_not_differentiableAt hnd)`. Rewrite using `[← h1]`. Conclude with `hd.hasDerivAt`. Distinguish the cases in `hx00 : x = 0`.

Conclude with `⟨0, by simp [hx00]⟩`. Establish `hder0` using `hx0 hx00`. Use `set c : ℂ := Complex.I * x with hc`. Establish `hderF : ∀ s, HasDerivAt F (c • F s) s`. Introduce `s`.

Establish `h2 : HasDerivAt (fun r => F (r - s)) (c • (v : H)) s`. Use `HasDerivAt.comp_sub_const (f := F) (f' := c • (v : H)) s s (by simpa using hder0)` as an intermediate fact. Simplify using `using this`. Establish `h3` using `((σ (u s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2`. Establish `heq : (fun r => σ (u s) (F (r - s))) = F`.

Use function extensionality and compare the values at `r`. Use `hF s (r - s)` as an intermediate fact. Simplify using `only [add_sub_cancel] at this`. Conclude with `this.symm`. Establish `h4 : σ (u s) (c • (v : H)) = c • F s`.

Rewrite using `[map_smul]`. Establish `h5 : HasDerivAt (fun r => σ (u s) (F (r - s))) (c • F s) s`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Conclude with `h4.symm`.

Rewrite `h5` using `[heq]`. Then use the resulting hypothesis. Use `set G : ℝ → H := fun t => Complex.exp (-c * t) • F t with hG`. Establish `hGd : ∀ t, HasDerivAt G 0 t`. Introduce `t`. Establish `h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * t) * (-c)) t`.

Use `(((hasDerivAt_id (t : ℂ)).const_mul (-c)).cexp).comp_ofReal` as an intermediate fact. Simplify using `using this`. Use `h1.smul (hderF t)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.

Use `symm`. Rewrite using `[smul_smul, ← add_smul, show Complex.exp (-c * t) * c + Complex.exp (-c * t) * -c = 0 by ring, zero_smul]`. Establish `hGc` using `is_const_of_deriv_eq_zero (fun t => (hGd t).differentiableAt) (fun t => (hGd t).deriv) (2 * Real.pi) 0`. Establish `hG0 : G 0 = (v : H)`. Simplify using `only [hG, hFdef, hu0, hU.1.1, ContinuousLinearMap.one_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]`.

Establish `hG2 : G (2 * Real.pi) = Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) • (v : H)`. Simplify using `only [hG, hFdef, hu2, hU.1.1, ContinuousLinearMap.one_apply]`. Rewrite `hGc` using `[hG2, hG0]`. Establish `hexp1 : Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) = 1`. Establish `: (Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) - 1) • (v : H) = 0`.

Rewrite using `[sub_smul, hGc, one_smul, sub_self]`. Break down `smul_eq_zero.1 this with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hv'`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 hexp1`.

Use `⟨-m, ?_⟩` and prove the remaining obligations. Establish `h2 : ((x + m : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = 0`. Rewrite `hm` using `[hc]`. Move the coercions through the operations in `at hm ⊢`. Take the linear combination `(-1 : ℂ) * hm`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Establish `: x + m = 0` using `by exact_mod_cast h`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd h Complex.two_pi_I_ne_zero`.
-/
theorem c3b : HighestWeightIntegral := by
  intro n ε H _ _ _ σ hU _ E hE v a x hv hx
  set Y : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => if j = a then Complex.I else 0 with hY
  have hYG : Y ∈ lieSet ε := by
    show Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0
    rw [hY, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [if_true, Pi.star_apply, Pi.add_apply, Pi.zero_apply]
      split_ifs <;> simp
    · simp [h]
  have hact : ReciprocityTheory.ChartRestriction.DS.actM E Y = Complex.I • E a a := by
    simp [ReciprocityTheory.ChartRestriction.DS.actM, hY, Matrix.diagonal_apply, ite_smul]
  have hv' : (v : H) ≠ 0 := by simpa using hv
  have hD : dRep σ Y (v : H) = (Complex.I * x) • (v : H) := by
    rw [← hE Y hYG v, hact]
    simp only [hx, LinearMap.smul_apply, Submodule.coe_smul]
    rw [mul_smul]
  set u : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => Matrix.diagonal fun j => if j = a then Complex.exp (t * Complex.I) else 1 with hu
  have hexp : ∀ t : ℝ, NormedSpace.exp (t • Y) = u t := fun t => exp_smul_diagonal_I_single_eq_diagonal_exp a t
  have huU : ∀ t, u t ∈ UJset ε := by
    intro t
    show (u t)ᴴ * Formalism.REAL.Jm ε * u t = Formalism.REAL.Jm ε
    rw [hu, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · subst h
      simp only [if_true, Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_comm _ (if ε j = true then (1 : ℂ) else -1), mul_assoc, ← Complex.exp_add]
      simp
    · simp [h]
  have hmul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    simp only [hu, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, add_mul, Complex.exp_add]
    · simp [h]
  have hu0 : u 0 = 1 := by simp [hu]
  have hu2 : u (2 * Real.pi) = 1 := by
    simp only [hu]
    rw [← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases h : j = a
    · simp [h, Complex.exp_two_pi_mul_I]
    · simp [h]
  set F : ℝ → H := fun t => σ (u t) (v : H) with hFdef
  have hF : ∀ s t, F (s + t) = σ (u s) (F t) := by
    intro s t
    simp only [hFdef, hmul, hU.1.2 _ (huU s) _ (huU t), ContinuousLinearMap.comp_apply]
  have hx0 : x ≠ 0 → HasDerivAt F ((Complex.I * x) • (v : H)) 0 := by
    intro hx0
    have h1 : deriv F 0 = (Complex.I * x) • (v : H) := by
      have : F = fun t : ℝ => σ (NormedSpace.exp (t • Y)) (v : H) := by
        funext t
        simp only [hFdef, hexp]
      rw [this]
      exact hD
    have hne : deriv F 0 ≠ 0 := by
      rw [h1]
      exact smul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hx0)) hv'
    have hd : DifferentiableAt ℝ F 0 := by
      by_contra hnd
      exact hne (deriv_zero_of_not_differentiableAt hnd)
    rw [← h1]
    exact hd.hasDerivAt
  by_cases hx00 : x = 0
  · exact ⟨0, by simp [hx00]⟩
  have hder0 := hx0 hx00
  set c : ℂ := Complex.I * x with hc
  have hderF : ∀ s, HasDerivAt F (c • F s) s := by
    intro s
    have h2 : HasDerivAt (fun r => F (r - s)) (c • (v : H)) s := by
      have := HasDerivAt.comp_sub_const (f := F) (f' := c • (v : H)) s s (by simpa using hder0)
      simpa using this
    have h3 := ((σ (u s)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h2
    have heq : (fun r => σ (u s) (F (r - s))) = F := by
      funext r
      have := hF s (r - s)
      simp only [add_sub_cancel] at this
      exact this.symm
    have h4 : σ (u s) (c • (v : H)) = c • F s := by
      rw [map_smul]
    have h5 : HasDerivAt (fun r => σ (u s) (F (r - s))) (c • F s) s := by
      convert h3 using 1
      · rfl
      · exact h4.symm
    rwa [heq] at h5
  set G : ℝ → H := fun t => Complex.exp (-c * t) • F t with hG
  have hGd : ∀ t, HasDerivAt G 0 t := by
    intro t
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * t) * (-c)) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul (-c)).cexp).comp_ofReal
      simpa using this
    have := h1.smul (hderF t)
    convert this using 1
    · rfl
    · symm
      rw [smul_smul, ← add_smul, show Complex.exp (-c * t) * c + Complex.exp (-c * t) * -c = 0 by ring,
        zero_smul]
  have hGc := is_const_of_deriv_eq_zero (fun t => (hGd t).differentiableAt)
    (fun t => (hGd t).deriv) (2 * Real.pi) 0
  have hG0 : G 0 = (v : H) := by
    simp only [hG, hFdef, hu0, hU.1.1, ContinuousLinearMap.one_apply, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_smul]
  have hG2 : G (2 * Real.pi) = Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) • (v : H) := by
    simp only [hG, hFdef, hu2, hU.1.1, ContinuousLinearMap.one_apply]
  rw [hG2, hG0] at hGc
  have hexp1 : Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have : (Complex.exp (-c * ((2 * Real.pi : ℝ) : ℂ)) - 1) • (v : H) = 0 := by
      rw [sub_smul, hGc, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
  refine ⟨-m, ?_⟩
  have h2 : ((x + m : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
    rw [hc] at hm
    push_cast at hm ⊢
    linear_combination (-1 : ℂ) * hm
  rcases mul_eq_zero.1 h2 with h | h
  · have : x + m = 0 := by exact_mod_cast h
    push_cast
    linarith
  · exact absurd h Complex.two_pi_I_ne_zero

end PositivityTheory.CW
