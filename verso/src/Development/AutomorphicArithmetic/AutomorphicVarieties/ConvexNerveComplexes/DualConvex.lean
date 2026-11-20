import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ q T`. Use `⟨?_, fun h => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `x hx y hy a b ha hb hab`. Simplify using `only [posDual, Set.mem_setOf_eq] at hx hy ⊢`. Introduce `k hk hk0`.

Establish `h1` using `hx k hk hk0`. Establish `h2` using `hy k hk hk0`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Break down `eq_or_lt_of_le ha with ha0 | ha'` into its components or cases. Substitute `ha0` using the available equality.

Establish `hb1 : b = 1` using `by linarith`. Substitute `hb1` using the available equality. Simplify using `using h2`. Use polynomial arithmetic with `[mul_pos ha' h1, mul_nonneg hb h2.le]`. Establish `e : normalCone q h = ⋂ h' ∈ poly q, {x : E →L[ℝ] ℝ | x h ≤ x h'}`.

Use extensionality with `x`. Simplify using `[normalCone]`. Rewrite using `[e]`. Conclude with `isClosed_biInter fun h' _ => isClosed_le (ContinuousLinearMap.apply ℝ ℝ h).continuous (ContinuousLinearMap.apply ℝ ℝ h').continuous`. Introduce `x hx y hy a b ha hb hab`.

Simplify using `only [normalCone, Set.mem_setOf_eq] at hx hy ⊢`. Introduce `h' hh'`. Establish `h1` using `hx h' hh'`. Establish `h2` using `hy h' hh'`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`.

Conclude with `add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.dual_convex : ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Y → E →L[ℝ] ℝ) (T : Set E), Convex ℝ (posDual T) ∧ ∀ h : E, IsClosed (normalCone q h) ∧ Convex ℝ (normalCone q h) := by
  intro E Y _ _ q T
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · intro x hx y hy a b ha hb hab
    simp only [posDual, Set.mem_setOf_eq] at hx hy ⊢
    intro k hk hk0
    have h1 := hx k hk hk0
    have h2 := hy k hk hk0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | ha'
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2
    · nlinarith [mul_pos ha' h1, mul_nonneg hb h2.le]
  · have e : normalCone q h = ⋂ h' ∈ poly q, {x : E →L[ℝ] ℝ | x h ≤ x h'} := by
      ext x
      simp [normalCone]
    rw [e]
    exact isClosed_biInter fun h' _ =>
      isClosed_le (ContinuousLinearMap.apply ℝ ℝ h).continuous (ContinuousLinearMap.apply ℝ ℝ h').continuous
  · intro x hx y hy a b ha hb hab
    simp only [normalCone, Set.mem_setOf_eq] at hx hy ⊢
    intro h' hh'
    have h1 := hx h' hh'
    have h2 := hy h' hh'
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
