import Mathlib
import GroundTheory.GlobalFields.TateThesis.ArchChars
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnits

namespace GroundTheory.Global

open Complex

/- English proof (translation)
Rewrite `h` using `[Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow]`. Conclude with `Real.exp_eq_one_iff _ |>.mp h`.
-/
theorem re_eq_zero_of_norm_exp_one_cpow {s : ℂ}
    (h : ‖((Real.exp 1 : ℝ) : ℂ) ^ s‖ = 1) : s.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow] at h
  exact Real.exp_eq_one_iff _ |>.mp h

/- English proof (translation)
Take `⟨s, hs, hu⟩` from `h`. Establish `hs' : s = (s.im : ℂ) * I`. Apply the tactic sequence `apply Complex.ext <;> simp [hre s hs]`. Use `⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩` and prove the remaining obligations. Use `congrArg Complex.im (hu _ hτ)` as an intermediate fact.

Simplify using `using this`.
-/
theorem existsUnique_mul_I_of_re_eq_zero {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by
  obtain ⟨s, hs, hu⟩ := h
  have hs' : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre s hs]
  refine ⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩
  have := congrArg Complex.im (hu _ hτ)
  simpa using this

/- English proof (translation)
Take `⟨p, hp, hu⟩` from `h`. Establish `hp' : p = (p.1, (p.2.im : ℂ) * I)`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp [hre p hp]`. Use `⟨(p.1, p.2.im), by show P (p.1, (p.2.im : ℂ) * I); rw [← hp']; exact hp, fun q hq => ?_⟩` and prove the remaining obligations.

Use `hu _ hq` as an intermediate fact. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `using congrArg Prod.fst this`. Simplify using `using congrArg (fun r : α × ℂ => r.2.im) this`.
-/
theorem existsUnique_prod_mul_I_of_re_eq_zero {α : Type*} {P : α × ℂ → Prop}
    (h : ∃! p, P p) (hre : ∀ p, P p → p.2.re = 0) :
    ∃! q : α × ℝ, P (q.1, (q.2 : ℂ) * I) := by
  obtain ⟨p, hp, hu⟩ := h
  have hp' : p = (p.1, (p.2.im : ℂ) * I) := by
    refine Prod.ext rfl ?_
    apply Complex.ext <;> simp [hre p hp]
  refine ⟨(p.1, p.2.im), by show P (p.1, (p.2.im : ℂ) * I); rw [← hp']; exact hp,
    fun q hq => ?_⟩
  have := hu _ hq
  refine Prod.ext ?_ ?_
  · simpa using congrArg Prod.fst this
  · simpa using congrArg (fun r : α × ℂ => r.2.im) this

/- English proof (translation)
Apply `existsUnique_mul_I_of_re_eq_zero (existsUnique_cpow_of_pos (circleToUnits.comp χ))` to reduce the goal to its premises. Introduce `s hs`. Apply `re_eq_zero_of_norm_exp_one_cpow` to reduce the goal to its premises. Establish `h : (χ ⟨Real.exp 1, Real.exp_pos 1⟩ : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ s` using `hs ⟨Real.exp 1, Real.exp_pos 1⟩`. Rewrite using `[← h, Circle.norm_coe]`.
-/
theorem existsUnique_cpow_of_pos_circle (χ : {x : ℝ // 0 < x} →ₜ* Circle) :
    ∃! τ : ℝ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  apply existsUnique_mul_I_of_re_eq_zero (existsUnique_cpow_of_pos (circleToUnits.comp χ))
  intro s hs
  apply re_eq_zero_of_norm_exp_one_cpow
  have h : (χ ⟨Real.exp 1, Real.exp_pos 1⟩ : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ s :=
    hs ⟨Real.exp 1, Real.exp_pos 1⟩
  rw [← h, Circle.norm_coe]

/- English proof (translation)
Apply `existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : Fin 2 × ℂ => ∀ x : ℝˣ, (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2) (existsUnique_realUnits (circleToUnits.comp χ))` to reduce the goal to its premises. Introduce `p hp`. Apply `re_eq_zero_of_norm_exp_one_cpow` to reduce the goal to its premises. Establish `h` using `hp (Units.mk0 (Real.exp 1) (Real.exp_pos 1).ne')`. Simplify using `only [Units.val_mk0, Real.sign_of_pos (Real.exp_pos 1), abs_of_pos (Real.exp_pos 1), Complex.ofReal_one, one_pow, one_mul] at h`.

Rewrite using `[← h, Circle.norm_coe]`.
-/
theorem existsUnique_realUnits_circle (χ : ℝˣ →ₜ* Circle) :
    ∃! p : Fin 2 × ℝ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : Fin 2 × ℂ => ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2)
    (existsUnique_realUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have h := hp (Units.mk0 (Real.exp 1) (Real.exp_pos 1).ne')
  simp only [Units.val_mk0, Real.sign_of_pos (Real.exp_pos 1), abs_of_pos (Real.exp_pos 1),
    Complex.ofReal_one, one_pow, one_mul] at h
  rw [← h, Circle.norm_coe]

/- English proof (translation)
Apply `existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : ℤ × ℂ => ∀ z : ℂˣ, (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2) (existsUnique_complexUnits (circleToUnits.comp χ))` to reduce the goal to its premises. Introduce `p hp`. Apply `re_eq_zero_of_norm_exp_one_cpow` to reduce the goal to its premises. Establish `hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.exp_pos 1).ne'`. Establish `h` using `hp (Units.mk0 _ hne)`.

Rewrite `h` using `[Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1), div_self hne, one_zpow, one_mul]`. Rewrite using `[← h, Circle.norm_coe]`.
-/
theorem existsUnique_complexUnits_circle (χ : ℂˣ →ₜ* Circle) :
    ∃! p : ℤ × ℝ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : ℤ × ℂ => ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2)
    (existsUnique_complexUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  have h := hp (Units.mk0 _ hne)
  rw [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1),
    div_self hne, one_zpow, one_mul] at h
  rw [← h, Circle.norm_coe]

/- English proof (translation)
Rewrite using `[← coe_circleToUnits, map_zpow, Units.val_zpow_eq_zpow_val, coe_circleToUnits]`.
-/
theorem circle_coe_zpow (z : Circle) (m : ℤ) : ((z ^ m : Circle) : ℂ) = (z : ℂ) ^ m := by
  rw [← coe_circleToUnits, map_zpow, Units.val_zpow_eq_zpow_val, coe_circleToUnits]

/- English proof (translation)
Use `(existsUnique_congr fun m => forall_congr' fun z => ?_).mpr (existsUnique_circle_zpow (circleToUnits.comp χ))` and prove the remaining obligations. Use `show χ z = z ^ m ↔ (χ z : ℂ) = (z : ℂ) ^ m`. Rewrite using `[← circle_coe_zpow, Circle.coe_inj]`.
-/
theorem existsUnique_circle_zpow_circle (χ : Circle →ₜ* Circle) :
    ∃! m : ℤ, ∀ z : Circle, χ z = z ^ m := by
  refine (existsUnique_congr fun m => forall_congr' fun z => ?_).mpr
    (existsUnique_circle_zpow (circleToUnits.comp χ))
  show χ z = z ^ m ↔ (χ z : ℂ) = (z : ℂ) ^ m
  rw [← circle_coe_zpow, Circle.coe_inj]

/- English proof (translation)
The claim follows from `existsUnique_circleExp_of_continuous χ hχ χ.map_add_eq_mul`.
-/
theorem existsUnique_addChar_real_circle (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    ∃! τ : ℝ, ∀ t, χ t = Circle.exp (τ * t) :=
  existsUnique_circleExp_of_continuous χ hχ χ.map_add_eq_mul

/- English proof (translation)
The claim follows from `existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul`.
-/
theorem existsUnique_addChar_real_units (χ : AddChar ℝ ℂˣ) (hχ : Continuous χ) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) :=
  existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul

end GroundTheory.Global
