import CompanionTheory.HarishChandraModules.NonemptyRepresentations.NonemptyOfAntitone

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.HWRep

variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)

def one' (k : ℕ) : Fin k → Fin k → ℂ := (1 : Matrix (Fin k) (Fin k) ℂ)

def D (Y : Matrix (Fin k) (Fin k) ℂ) : Matrix R.I R.I ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun B : Fin k → Fin k → ℂ => R.ρ (Matrix.of B) i j) (one' k) (fun a b => Y a b)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [D, Matrix.of_apply, Matrix.add_apply]`. Rewrite using `[← map_add]`. Both sides reduce to the same expression.
-/
theorem D_add (Y Z : Matrix (Fin k) (Fin k) ℂ) : R.D (Y + Z) = R.D Y + R.D Z := by
  ext i j
  simp only [D, Matrix.of_apply, Matrix.add_apply]
  rw [← map_add]; rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [D, Matrix.of_apply, Matrix.smul_apply]`. Rewrite using `[← map_smul]`. Both sides reduce to the same expression.
-/
theorem D_smul (c : ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) : R.D (c • Y) = c • R.D Y := by
  ext i j
  simp only [D, Matrix.of_apply, Matrix.smul_apply]
  rw [← map_smul]; rfl

/- English proof (translation)
Establish `hγ' : HasDerivAt (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) (fun a b => Y a b) 0` using `hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hγ a b`. Use `hasDerivAt_pi.2 fun i => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `HasDerivAt.fun_sum fun j _ => HasDerivAt.mul_const ?_ _` and prove the remaining obligations. Establish `hd` using `(R.diff (one' k) (by show (1 : Matrix (Fin k) (Fin k) ℂ).det ≠ 0; simp) i j).hasFDerivAt`.

Establish `e : one' k = (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) 0`. Use function extensionality and compare the values at `a b`. Simplify using `[h0, one']`. Establish `hd'` using `hd.restrictScalars ℝ`. Rewrite `hd'` using `[e]`.

Use `hd'.comp_hasDerivAt (0 : ℝ) hγ'` as an intermediate fact. Rewrite `this` using `[← e]`. Conclude with `this`.
-/
theorem hasDerivAt_curve (γ : ℝ → Matrix (Fin k) (Fin k) ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ a b, HasDerivAt (fun t => γ t a b) (Y a b) 0) (v : R.I → ℂ) :
    HasDerivAt (fun t => R.ρ (γ t) *ᵥ v) (R.D Y *ᵥ v) 0 := by
  have hγ' : HasDerivAt (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) (fun a b => Y a b) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hγ a b
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.mul_const ?_ _
  have hd := (R.diff (one' k) (by show (1 : Matrix (Fin k) (Fin k) ℂ).det ≠ 0; simp) i j).hasFDerivAt
  have e : one' k = (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) 0 := by
    funext a b; simp [h0, one']
  have hd' := hd.restrictScalars ℝ
  rw [e] at hd'
  have := hd'.comp_hasDerivAt (0 : ℝ) hγ'
  rw [← e] at this
  exact this

/- English proof (translation)
Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)).const_add ((1 : Matrix (Fin k) (Fin k) ℂ) c d)`.
-/
theorem curve_deriv (a b c d : Fin k) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)
      ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d) 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
    ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)).const_add ((1 : Matrix (Fin k) (Fin k) ℂ) c d)

/- English proof (translation)
Introduce `c d h`. Establish `h' : d < c` using `h`. Establish `: ¬(a = c ∧ b = d)` using `by rintro ⟨rfl, rfl⟩; exact absurd hab (not_le.2 h')`. Simplify using `[Matrix.one_apply, h'.ne', Matrix.single_apply, this]`.
-/
theorem curve_tri {a b : Fin k} (hab : a ≤ b) (t : ℂ) :
    (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ).BlockTriangular id := by
  intro c d h
  have h' : d < c := h
  have : ¬(a = c ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact absurd hab (not_le.2 h')
  simp [Matrix.one_apply, h'.ne', Matrix.single_apply, this]

/- English proof (translation)
Establish `h` using `R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) _ (by simp) (curve_deriv a b) R.v0`. Establish `hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c = 1`. Introduce `t c`. Establish `: ¬(a = c ∧ b = c)` using `by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab`. Simplify using `[Matrix.single_apply, this]`.

Establish `e : (fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) *ᵥ R.v0) = fun _ => R.v0`. Use function extensionality and compare the values at `t`. Rewrite using `[R.hw _ (curve_tri hab.le _)]`. Simplify using `only [hdiag]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.det_of_upperTriangular (curve_tri hab.le _)]`. Simplify using `only [hdiag]`. Simplify using the standard rewrite rules. Rewrite `h` using `[e]`. Conclude with `h.unique (hasDerivAt_const _ _)`.
-/
theorem D_upper {a b : Fin k} (hab : a < b) : R.D (Matrix.single a b 1) *ᵥ R.v0 = 0 := by
  have h := R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) _ (by simp)
    (curve_deriv a b) R.v0
  have hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c = 1 := by
    intro t c
    have : ¬(a = c ∧ b = c) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    simp [Matrix.single_apply, this]
  have e : (fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) *ᵥ R.v0) = fun _ => R.v0 := by
    funext t
    rw [R.hw _ (curve_tri hab.le _)]
    · simp only [hdiag]; simp
    · rw [Matrix.det_of_upperTriangular (curve_tri hab.le _)]
      simp only [hdiag]; simp
  rw [e] at h
  exact h.unique (hasDerivAt_const _ _)

/- English proof (translation)
Establish `h` using `R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) _ (by simp) (curve_deriv a a) R.v0`. Establish `hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a a (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c = if c = a then 1 + t else 1`. Introduce `t c`. Distinguish the cases in `hc : c = a`. Simplify using `[hc]`.

Simplify using `[Matrix.single_apply, hc, Ne.symm hc]`. Establish `h1 : HasDerivAt (fun t : ℝ => (1 : ℂ) + t) 1 0`. Simplify using `using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add (1 : ℂ)`. Establish `hne : ∀ᶠ t : ℝ in nhds 0, (1 : ℂ) + t ≠ 0` using `h1.continuousAt.eventually_ne (by simp)`. Establish `e : (fun t : ℝ => ((1 : ℂ) + t) ^ ν a • R.v0) =ᶠ[nhds 0] fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) *ᵥ R.v0` using `by filter_upwards [hne] with t ht`.

Rewrite using `[R.hw _ (curve_tri le_rfl _)]`. Use `congr 1`. Simplify using `only [hdiag]`. Apply the tactic sequence `rw [Finset.prod_eq_single a] <;> simp +contextual`. Rewrite using `[Matrix.det_of_upperTriangular (curve_tri le_rfl _)]`.

Simplify using `only [hdiag]`. Apply the tactic sequence `exact Finset.prod_ne_zero_iff.2 fun c _ => by split_ifs <;> simp [ht]`. Establish `hz : HasDerivAt (fun x : ℂ => x ^ ν a) (ν a : ℂ) ((1 : ℂ) + ((0 : ℝ) : ℂ))`. Simplify using `using hasDerivAt_zpow (ν a) (1 : ℂ) (Or.inl one_ne_zero)`. Establish `h2 : HasDerivAt (fun t : ℝ => ((1 : ℂ) + t) ^ ν a) (ν a : ℂ) 0`.

Use `(hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1` as an intermediate fact. Simplify using `only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, one_smul, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply] at this`. Conclude with `this`. Conclude with `(h.congr_of_eventuallyEq e).unique (h2.smul_const R.v0)`.
-/
theorem D_diag (a : Fin k) : R.D (Matrix.single a a 1) *ᵥ R.v0 = (ν a : ℂ) • R.v0 := by
  have h := R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) _ (by simp)
    (curve_deriv a a) R.v0
  have hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a a (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c =
      if c = a then 1 + t else 1 := by
    intro t c
    by_cases hc : c = a
    · simp [hc]
    · simp [Matrix.single_apply, hc, Ne.symm hc]
  have h1 : HasDerivAt (fun t : ℝ => (1 : ℂ) + t) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add (1 : ℂ)
  have hne : ∀ᶠ t : ℝ in nhds 0, (1 : ℂ) + t ≠ 0 :=
    h1.continuousAt.eventually_ne (by simp)
  have e : (fun t : ℝ => ((1 : ℂ) + t) ^ ν a • R.v0) =ᶠ[nhds 0]
      fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) *ᵥ R.v0 := by
    filter_upwards [hne] with t ht
    rw [R.hw _ (curve_tri le_rfl _)]
    · congr 1
      simp only [hdiag]
      rw [Finset.prod_eq_single a] <;> simp +contextual
    · rw [Matrix.det_of_upperTriangular (curve_tri le_rfl _)]
      simp only [hdiag]
      exact Finset.prod_ne_zero_iff.2 fun c _ => by split_ifs <;> simp [ht]
  have hz : HasDerivAt (fun x : ℂ => x ^ ν a) (ν a : ℂ) ((1 : ℂ) + ((0 : ℝ) : ℂ)) := by
    simpa using hasDerivAt_zpow (ν a) (1 : ℂ) (Or.inl one_ne_zero)
  have h2 : HasDerivAt (fun t : ℝ => ((1 : ℂ) + t) ^ ν a) (ν a : ℂ) 0 := by
    have := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply] at this
    exact this
  exact (h.congr_of_eventuallyEq e).unique (h2.smul_const R.v0)

end CompanionTheory.D.Inhab.HWRep
