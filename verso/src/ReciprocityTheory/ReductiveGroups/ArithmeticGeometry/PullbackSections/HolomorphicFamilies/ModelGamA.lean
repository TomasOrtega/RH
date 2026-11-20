import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MG

open Matrix

variable {r : ℕ}

def Eij (i j : Fin r) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a = i ∧ b = j then s else 0

/- English proof (translation)
Simplify using `only [Eij, Matrix.mul_apply, Matrix.of_apply]`. Distinguish the cases in `hb : b = j`. Substitute `hb` using the available equality. Simplify using `[mul_ite]`. Simplify using `[hb]`.
-/
theorem mul_Eij (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (s : ℂ) (a b : Fin r) :
    (H * Eij i j s) a b = if b = j then H a i * s else 0 := by
  simp only [Eij, Matrix.mul_apply, Matrix.of_apply]
  by_cases hb : b = j
  · subst hb
    simp [mul_ite]
  · simp [hb]

/- English proof (translation)
Simplify using `only [Eij, Matrix.mul_apply, Matrix.of_apply]`. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality. Simplify using `[ite_mul]`. Simplify using `[ha]`.
-/
theorem Eij_mul (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (s : ℂ) (a b : Fin r) :
    (Eij i j s * H) a b = if a = i then s * H j b else 0 := by
  simp only [Eij, Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a = i
  · subst ha
    simp [ite_mul]
  · simp [ha]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Eij_mul]`. Simplify using `[Eij, Ne.symm hij]`.
-/
theorem Eij_sq (i j : Fin r) (hij : i ≠ j) (s : ℂ) : Eij i j s * Eij i j s = 0 := by
  ext a b
  rw [Eij_mul]
  simp [Eij, Ne.symm hij]

/- English proof (translation)
Rewrite using `[sub_mul, one_mul, mul_add, mul_one, Eij_sq i j hij, add_zero, add_sub_cancel_right]`.
-/
theorem unip_mul (i j : Fin r) (hij : i ≠ j) (s : ℂ) : (1 - Eij i j s) * (1 + Eij i j s) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, Eij_sq i j hij, add_zero, add_sub_cancel_right]

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.one_apply_eq, Eij, Matrix.of_apply]`. Rewrite using `[if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `lt_irrefl _ hji`. Introduce `a b hab`. Establish `hab' : a < b` using `OrderDual.toDual_lt_toDual.mp hab`. Simplify using `only [Matrix.add_apply, Eij, Matrix.of_apply]`. Rewrite using `[Matrix.one_apply_ne (ne_of_lt hab'), if_neg, add_zero]`.

Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_asymm hji hab'`.
-/
theorem det_unip (i j : Fin r) (hji : j < i) (s : ℂ) : (1 + Eij i j s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Eij, Matrix.of_apply]
    rw [if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ hji
  · intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp only [Matrix.add_apply, Eij, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt hab'), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hji hab'

/- English proof (translation)
Establish `h1 : (1 + Eij i j s) * adjugate (1 + Eij i j s) = 1`. Rewrite using `[Matrix.mul_adjugate, det_unip i j hji, one_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[unip_mul i j (ne_of_gt hji) s, one_mul]`. Use `_ = 1 - Eij i j s := by rw [mul_assoc, h1, mul_one]`.
-/
theorem adj_unip (i j : Fin r) (hji : j < i) (s : ℂ) : adjugate (1 + Eij i j s) = 1 - Eij i j s := by
  have h1 : (1 + Eij i j s) * adjugate (1 + Eij i j s) = 1 := by
    rw [Matrix.mul_adjugate, det_unip i j hji, one_smul]
  calc adjugate (1 + Eij i j s)
      = ((1 - Eij i j s) * (1 + Eij i j s)) * adjugate (1 + Eij i j s) := by
        rw [unip_mul i j (ne_of_gt hji) s, one_mul]
    _ = 1 - Eij i j s := by rw [mul_assoc, h1, mul_one]

/- English proof (translation)
Establish `h : (1 - Eij i j s) * H * (1 + Eij i j s) = H + H * Eij i j s - Eij i j s * H - Eij i j s * (H * Eij i j s)` using `by noncomm_ring`. Rewrite using `[h]`. Simplify using `only [Matrix.add_apply, Matrix.sub_apply, mul_Eij, Eij_mul, if_true, ite_true, eq_self_iff_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_entry (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (hij : i ≠ j) (s : ℂ) :
    ((1 - Eij i j s) * H * (1 + Eij i j s)) i j = H i j + s * (H i i - H j j) - s ^ 2 * H j i := by
  have h : (1 - Eij i j s) * H * (1 + Eij i j s) =
      H + H * Eij i j s - Eij i j s * H - Eij i j s * (H * Eij i j s) := by
    noncomm_ring
  rw [h]
  simp only [Matrix.add_apply, Matrix.sub_apply, mul_Eij, Eij_mul, if_true, ite_true, eq_self_iff_true]
  ring

/- English proof (translation)
Establish `ha : a = 0` using `by simpa using h 0 (by simpa using hδ)`. Establish `htn : ‖((δ / 2 : ℝ) : ℂ)‖ = δ / 2`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Establish `ht : ‖((δ / 2 : ℝ) : ℂ)‖ < δ` using `by rw [htn]; linarith`. Establish `ht2 : ‖((δ / 2 : ℝ) : ℂ) / 2‖ < δ`.

Rewrite using `[norm_div, htn, Complex.norm_two]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htne : ((δ / 2 : ℝ) : ℂ) ≠ 0`. Introduce `h0`. Rewrite `htn` using `[h0, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `h _ ht`. Establish `h2` using `h _ ht2`. Rewrite `h1`, `h2` using `[ha, zero_add]`. Establish `e1 : b - ((δ / 2 : ℝ) : ℂ) * c = 0`.

Establish `h3 : ((δ / 2 : ℝ) : ℂ) * (b - ((δ / 2 : ℝ) : ℂ) * c) = 0` using `by linear_combination h1`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `absurd h4 htne`. Conclude with `h4`. Establish `e2 : b - ((δ / 2 : ℝ) : ℂ) / 2 * c = 0`.

Establish `h3 : ((δ / 2 : ℝ) : ℂ) / 2 * (b - ((δ / 2 : ℝ) : ℂ) / 2 * c) = 0` using `by linear_combination h2`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `absurd h4 (div_ne_zero htne two_ne_zero)`. Conclude with `h4`. Establish `hc : c = 0`.

Establish `h3 : ((δ / 2 : ℝ) : ℂ) / 2 * c = 0` using `by linear_combination e2 - e1`. Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `absurd h4 (div_ne_zero htne two_ne_zero)`. Conclude with `h4`. Use `⟨ha, ?_, hc⟩` and prove the remaining obligations.

Take the linear combination `e1 + ((δ / 2 : ℝ) : ℂ) * hc`.
-/
theorem coeffs_of_small (a b c : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ s : ℂ, ‖s‖ < δ → a + s * b - s ^ 2 * c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have ha : a = 0 := by simpa using h 0 (by simpa using hδ)
  have htn : ‖((δ / 2 : ℝ) : ℂ)‖ = δ / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have ht : ‖((δ / 2 : ℝ) : ℂ)‖ < δ := by rw [htn]; linarith
  have ht2 : ‖((δ / 2 : ℝ) : ℂ) / 2‖ < δ := by
    rw [norm_div, htn, Complex.norm_two]
    linarith
  have htne : ((δ / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at htn
    linarith
  have h1 := h _ ht
  have h2 := h _ ht2
  rw [ha, zero_add] at h1 h2
  have e1 : b - ((δ / 2 : ℝ) : ℂ) * c = 0 := by
    have h3 : ((δ / 2 : ℝ) : ℂ) * (b - ((δ / 2 : ℝ) : ℂ) * c) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 htne
    · exact h4
  have e2 : b - ((δ / 2 : ℝ) : ℂ) / 2 * c = 0 := by
    have h3 : ((δ / 2 : ℝ) : ℂ) / 2 * (b - ((δ / 2 : ℝ) : ℂ) / 2 * c) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (div_ne_zero htne two_ne_zero)
    · exact h4
  have hc : c = 0 := by
    have h3 : ((δ / 2 : ℝ) : ℂ) / 2 * c = 0 := by linear_combination e2 - e1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (div_ne_zero htne two_ne_zero)
    · exact h4
  refine ⟨ha, ?_, hc⟩
  linear_combination e1 + ((δ / 2 : ℝ) : ℂ) * hc

/- English proof (translation)
Establish `key : ∀ i j : Fin r, j < i → H i j = 0 ∧ H i i - H j j = 0 ∧ H j i = 0`. Introduce `i j hji`. Take `⟨δ, hδ, hs⟩` from `h i j hji`. Apply `coeffs_of_small (H i j) (H i i - H j j) (H j i) δ hδ` to reduce the goal to its premises. Introduce `s hs'`.

Establish `h1` using `hs s hs'`. Apply the tactic sequence `rwa [adj_unip i j hji, conj_entry H i j (ne_of_gt hji)] at h1`. Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `hij`.

Break down `lt_or_gt_of_ne hij with hlt | hgt` into its components or cases. Conclude with `(key j i hlt).2.2`. Conclude with `(key i j hgt).1`. Break down `lt_trichotomy i j with hlt | heq | hgt` into its components or cases. Conclude with `(sub_eq_zero.mp (key j i hlt).2.1).symm`.

Rewrite using `[heq]`. Conclude with `sub_eq_zero.mp (key i j hgt).2.1`.
-/
theorem scalar_of_small (H : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ i j : Fin r, j < i → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s‖ < δ →
      ((adjugate (1 + Eij i j s) * H * (1 + Eij i j s) : Matrix (Fin r) (Fin r) ℂ)) i j = 0) :
    ∀ i j : Fin r, (i ≠ j → H i j = 0) ∧ H i i = H j j := by
  have key : ∀ i j : Fin r, j < i → H i j = 0 ∧ H i i - H j j = 0 ∧ H j i = 0 := by
    intro i j hji
    obtain ⟨δ, hδ, hs⟩ := h i j hji
    apply coeffs_of_small (H i j) (H i i - H j j) (H j i) δ hδ
    intro s hs'
    have h1 := hs s hs'
    rwa [adj_unip i j hji, conj_entry H i j (ne_of_gt hji)] at h1
  intro i j
  constructor
  · intro hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (key j i hlt).2.2
    · exact (key i j hgt).1
  · rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (sub_eq_zero.mp (key j i hlt).2.1).symm
    · rw [heq]
    · exact sub_eq_zero.mp (key i j hgt).2.1

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MG
