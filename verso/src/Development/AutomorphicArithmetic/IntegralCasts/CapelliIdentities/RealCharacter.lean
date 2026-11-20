import Mathlib

/- English proof (translation)
Introduce `f hf hadd hn`. Set `F : C(ℝ, Circle)` to `⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩`. Establish `hF : ∀ s, (F s : ℂ) = f s` using `fun _ => rfl`. Establish `hFadd : ∀ s t, F (s + t) = F s * F t` using `fun s t => by`. Apply `Circle.ext` to reduce the goal to its premises.

Rewrite using `[Circle.coe_mul, hF, hF, hF, hadd]`. Establish `hF0 : F 0 = 1`. Establish `h` using `hFadd 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `left_eq_mul.1 h`.

Establish `cov` using `Circle.isCoveringMap_exp`. Take `⟨g, ⟨hg0, hg⟩, -⟩` from `cov.existsUnique_continuousMap_lifts F 0 0 (by rw [hF0]; exact Circle.exp_zero)`. Establish `hg' : ∀ s, Circle.exp (g s) = F s` using `fun s => congrFun hg s`. Establish `gadd : ∀ s t, g (s + t) = g s + g t` using `fun s t => by`. Establish `h` using `cov.eq_of_comp_eq (g₁ := fun s : ℝ => g (s + t)) (g₂ := fun s : ℝ => g s + g t) (by fun_prop) (by fun_prop) (by`.

Use function extensionality and compare the values at `s`. Use `show Circle.exp (g (s + t)) = Circle.exp (g s + g t)`. Rewrite using `[Circle.exp_add, hg', hg', hg', hFadd]) 0 (by simp [hg0])`. Conclude with `congrFun h s`. Set `G : ℝ →+ ℝ` to `AddMonoidHom.mk' g gadd`.

Use `⟨g 1, fun s => ?_⟩` and prove the remaining obligations. Establish `hs : g s = g 1 * s`. Establish `h` using `map_real_smul G g.continuous s 1`. Simplify using `only [smul_eq_mul, mul_one] at h`. Rewrite using `[mul_comm]`.

Conclude with `h`. Rewrite using `[← hs, ← hF, ← hg', Circle.coe_exp]`.
-/
theorem UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real :
    ∀ (f : ℝ → ℂ),
    Continuous f →
      (∀ (s t : ℝ), f (s + t) = f s * f t) →
        (∀ (s : ℝ), ‖f s‖ = (1 : ℝ)) → ∃ (b : ℝ), ∀ (s : ℝ), f s = Complex.exp ((↑(b * s) : ℂ) * Complex.I) := by
  intro f hf hadd hn
  let F : C(ℝ, Circle) :=
    ⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩
  have hF : ∀ s, (F s : ℂ) = f s := fun _ => rfl
  have hFadd : ∀ s t, F (s + t) = F s * F t := fun s t => by
    apply Circle.ext
    rw [Circle.coe_mul, hF, hF, hF, hadd]
  have hF0 : F 0 = 1 := by
    have h := hFadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have cov := Circle.isCoveringMap_exp
  obtain ⟨g, ⟨hg0, hg⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts F 0 0 (by rw [hF0]; exact Circle.exp_zero)
  have hg' : ∀ s, Circle.exp (g s) = F s := fun s => congrFun hg s
  have gadd : ∀ s t, g (s + t) = g s + g t := fun s t => by
    have h := cov.eq_of_comp_eq (g₁ := fun s : ℝ => g (s + t)) (g₂ := fun s : ℝ => g s + g t)
      (by fun_prop) (by fun_prop)
      (by
        funext s
        show Circle.exp (g (s + t)) = Circle.exp (g s + g t)
        rw [Circle.exp_add, hg', hg', hg', hFadd]) 0 (by simp [hg0])
    exact congrFun h s
  let G : ℝ →+ ℝ := AddMonoidHom.mk' g gadd
  refine ⟨g 1, fun s => ?_⟩
  have hs : g s = g 1 * s := by
    have h := map_real_smul G g.continuous s 1
    simp only [smul_eq_mul, mul_one] at h
    rw [mul_comm]
    exact h
  rw [← hs, ← hF, ← hg', Circle.coe_exp]
