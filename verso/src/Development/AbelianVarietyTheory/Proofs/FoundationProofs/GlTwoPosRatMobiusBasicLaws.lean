import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MobLaws

/- English proof (translation)
Establish `h` using `g.2`. Rewrite `h` using `[Matrix.mem_glpos]`. Simplify `h` using `[ent, Matrix.det_fin_two]`.
-/
theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

/- English proof (translation)
Simplify using `[ent, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Introduce `h0`. Establish `hy : 0 < z.im` using `hz`. Establish `him` using `congrArg Complex.im h0`. Establish `hre` using `congrArg Complex.re h0`. Simplify using `at him hre`.

Establish `hd` using `det_pos g`. Break down `him with hc | hc` into its components or cases. Rewrite `hre`, `hd` using `[hc]`. Simplify using `at hre`. Rewrite `hd` using `[hre]`.

Simplify using `at hd`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h0
  have hy : 0 < z.im := hz
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  have hd := det_pos g
  rcases him with hc | hc
  · rw [hc] at hre hd; simp at hre; rw [hre] at hd; simp at hd
  · linarith

/- English proof (translation)
Rewrite using `[mob, Complex.div_im]`. Simplify using `only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ratCast_re, Complex.ratCast_im]`. Use `push_cast`. Rewrite using `[div_sub_div_same]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem im_mob (g : GQ) (z : ℂ) : (mob g z).im =
    (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
  rw [mob, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  rw [div_sub_div_same]
  congr 1
  ring

/- English proof (translation)
Use `show 0 < (mob g z).im`. Rewrite using `[im_mob]`. Establish `hy : 0 < z.im` using `hz`. Establish `hd : (0:ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ)` using `by exact_mod_cast det_pos g`. Conclude with `div_pos (mul_pos hd hy) (Complex.normSq_pos.2 (den_ne g hz))`.
-/
theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  show 0 < (mob g z).im
  rw [im_mob]
  have hy : 0 < z.im := hz
  have hd : (0:ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast det_pos g
  exact div_pos (mul_pos hd hy) (Complex.normSq_pos.2 (den_ne g hz))

/- English proof (translation)
Establish `e1 : a * (N / D) + b = (a * N + b * D) / D` using `by field_simp`. Establish `e2 : c * (N / D) + d = (c * N + d * D) / D` using `by field_simp`. Rewrite using `[e1, e2, div_div_div_cancel_right₀ hD]`.
-/
theorem complex_mobius_fraction_clear_denom (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  have e1 : a * (N / D) + b = (a * N + b * D) / D := by field_simp
  have e2 : c * (N / D) + d = (c * N + d * D) / D := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hD]

/- English proof (translation)
Establish `h1` using `den_ne h hz`. Unfold `mob`. Rewrite using `[complex_mobius_fraction_clear_denom _ _ _ _ _ _ h1]`. Simplify using `only [ent_mul]`. Use `push_cast`.

Apply the tactic sequence `congr 1 <;> ring`.
-/
theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have h1 := den_ne h hz
  unfold mob
  rw [complex_mobius_fraction_clear_denom _ _ _ _ _ _ h1]
  simp only [ent_mul]
  push_cast
  congr 1 <;> ring

/- English proof (translation)
Simplify using `[mob, ent]`.
-/
theorem mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

/- English proof (translation)
Introduce `z hz`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Unfold `mob`. Conclude with `((differentiableAt_id.const_mul _).add_const _).div ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)`.
-/
theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold mob
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

/- English proof (translation)
Establish `h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det` using `by rw [γ.2]; norm_num`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[toGQ, h, ofSL]`.
-/
theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; norm_num
  apply Subtype.ext; apply Units.ext; ext i j
  simp [toGQ, h, ofSL]

/- English proof (translation)
Establish `h : 0 < (m * m').det` using `by rw [Matrix.det_mul]; exact mul_pos hm hm'`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [toGQ, h, hm, hm', dif_pos]`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply]`.
-/
theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have h : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos hm hm'
  apply Subtype.ext; apply Units.ext
  simp only [toGQ, h, hm, hm', dif_pos]
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.KZ.MobLaws

namespace GlobalTheory.KZ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun g _ hz => MobLaws.mob_mem g hz, fun g h _ hz => MobLaws.mob_mul g h hz, MobLaws.mob_one, MobLaws.mob_diff, MobLaws.toGQ_SL, MobLaws.toGQ_mul⟩`.
-/
theorem mob_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') :=
  ⟨fun g _ hz => MobLaws.mob_mem g hz, fun g h _ hz => MobLaws.mob_mul g h hz, MobLaws.mob_one,
    MobLaws.mob_diff, MobLaws.toGQ_SL, MobLaws.toGQ_mul⟩

end GlobalTheory.KZ
