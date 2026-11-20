import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Matrix

/- English proof (translation)
Establish `e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) = ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k)`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Establish `e0` using `congrFun (congrFun e 0) 0`.

Establish `e1` using `congrFun (congrFun e 1) 0`. Rewrite `e0`, `e1` using `[Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]`. Establish `t : Matrix.GeneralLinearGroup.det (g * r * g⁻¹) = Matrix.GeneralLinearGroup.det r`. Rewrite using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`. Rewrite `e0`, `e1` using `[h10, h00]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← t]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h00, h11, mul_zero, sub_zero]`. Both sides reduce to the same expression.
-/
private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : kˣ) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      Matrix.GeneralLinearGroup.det r = a * b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.GeneralLinearGroup.det (g * r * g⁻¹) = Matrix.GeneralLinearGroup.det r := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [h10, h00] at e0 e1
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; ring
  · rw [e1]; ring
  · rw [← t]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h00, h11, mul_zero, sub_zero]
    rfl

/- English proof (translation)
Establish `: 1 ≤ ‖a - b‖`. Assume the negation of the conclusion as `hlt`. Apply `h` to reduce the goal to its premises. Rewrite `ha` using `[norm_sub_rev]`. Establish `e : x - y = (x - a) + ((a - b) + (b - y))` using `by ring`.

Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha ?_)` and prove the remaining obligations. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) hb)`. Conclude with `⟨this, by rwa [norm_sub_rev]⟩`.
-/
private theorem one_le_norm {K : Type} [NormedField K] [IsUltrametricDist K] {x y a b : K} (h : ¬ ‖x - y‖ < 1)
    (ha : ‖a - x‖ < 1) (hb : ‖b - y‖ < 1) : 1 ≤ ‖a - b‖ ∧ 1 ≤ ‖b - a‖ := by
  have : 1 ≤ ‖a - b‖ := by
    by_contra hlt
    apply h
    rw [norm_sub_rev] at ha
    have e : x - y = (x - a) + ((a - b) + (b - y)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) hb)
  exact ⟨this, by rwa [norm_sub_rev]⟩

/- English proof (translation)
Combine the equalities or inequalities in the calculation `calc ‖q‖ ≤ ‖c‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hc _ = ‖d‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]`.
-/
private theorem norm_le_of {K : Type} [NormedField K] {c d p q : K} (hc : 1 ≤ ‖c‖) (e : c * q = d * p) :
    ‖q‖ ≤ ‖d‖ * ‖p‖ :=
  calc ‖q‖ ≤ ‖c‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hc
    _ = ‖d‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]

/- English proof (translation)
Introduce `l _ S A x κ ⟨s₀, hne⟩ hA ⟨g, hg⟩`. Establish `key` using `fun s => col_eq g (A s) _ _ (hg s).1 ((hg s).2 0) ((hg s).2 1)`. Establish `hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0`. Use `(g⁻¹).det_ne_zero` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis.

Generalize the expression as in `(g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet`. Generalize the expression as in `(g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet`. Establish `hne' : ¬ ‖(x s₀ : Qbar l) - 1‖ < 1` using `hne`. Take `⟨a00, a11, a10, a01⟩` from `hA s₀`. Use `⟨fun s => (key s).2.2, fun hκ => ?_, fun hκ => ?_⟩` and prove the remaining obligations.

Establish `h1 : ‖(κ 0 s₀ : Qbar l) - (x s₀ : Qbar l)‖ < 1` using `hκ s₀`. Establish `hge` using `(one_le_norm hne' h1 a00).1`. Establish `hpq : ‖p‖ ≤ ‖A s₀ 0 1‖ * ‖q‖` using `norm_le_of hge (by linear_combination -(key s₀).1)`. Establish `hq : q ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hpq` using `[norm_zero, mul_zero, norm_le_zero_iff]`. Simplify using `[hpq] at hdet`. Use `⟨p / q, ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, div_le_one (norm_pos_iff.mpr hq)]`. Conclude with `hpq.trans (mul_le_of_le_one_left (norm_nonneg _) a01)`.

Take `⟨k1, k2, -⟩` from `key s`. Use extensionality with `i`. Use `fin_cases i`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `k1`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `k2`. Establish `h1 : ‖(κ 0 s₀ : Qbar l) - 1‖ < 1` using `hκ s₀`.

Establish `hge` using `(one_le_norm hne' a11 h1).2`. Establish `hpq : ‖q‖ ≤ ‖A s₀ 1 0‖ * ‖p‖` using `norm_le_of hge (by linear_combination -(key s₀).2.1)`. Establish `hp : p ≠ 0`. Introduce and unpack `rfl`. Rewrite `hpq` using `[norm_zero, mul_zero, norm_le_zero_iff]`.

Simplify using `[hpq] at hdet`. Use `⟨q / p, ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, div_lt_one (norm_pos_iff.mpr hp)]`. Conclude with `hpq.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr hp) a10)`. Take `⟨k1, k2, -⟩` from `key s`.

Use extensionality with `i`. Use `fin_cases i`. Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `k1`.

Simplify using `[Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `k2`.
-/
theorem UpperTheory.mix_stable_line_local :
    UpperTheory.V.Sd.S2.LocLine := by
  intro l _ S A x κ ⟨s₀, hne⟩ hA ⟨g, hg⟩
  have key := fun s => col_eq g (A s) _ _ (hg s).1 ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hne' : ¬ ‖(x s₀ : Qbar l) - 1‖ < 1 := hne
  obtain ⟨a00, a11, a10, a01⟩ := hA s₀
  refine ⟨fun s => (key s).2.2, fun hκ => ?_, fun hκ => ?_⟩
  · have h1 : ‖(κ 0 s₀ : Qbar l) - (x s₀ : Qbar l)‖ < 1 := hκ s₀
    have hge := (one_le_norm hne' h1 a00).1
    have hpq : ‖p‖ ≤ ‖A s₀ 0 1‖ * ‖q‖ := norm_le_of hge (by linear_combination -(key s₀).1)
    have hq : q ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, norm_le_zero_iff] at hpq
      simp [hpq] at hdet
    refine ⟨p / q, ?_, fun s => ?_⟩
    · rw [norm_div, div_le_one (norm_pos_iff.mpr hq)]
      exact hpq.trans (mul_le_of_le_one_left (norm_nonneg _) a01)
    · obtain ⟨k1, k2, -⟩ := key s
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k1
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k2
  · have h1 : ‖(κ 0 s₀ : Qbar l) - 1‖ < 1 := hκ s₀
    have hge := (one_le_norm hne' a11 h1).2
    have hpq : ‖q‖ ≤ ‖A s₀ 1 0‖ * ‖p‖ := norm_le_of hge (by linear_combination -(key s₀).2.1)
    have hp : p ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, norm_le_zero_iff] at hpq
      simp [hpq] at hdet
    refine ⟨q / p, ?_, fun s => ?_⟩
    · rw [norm_div, div_lt_one (norm_pos_iff.mpr hp)]
      exact hpq.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr hp) a10)
    · obtain ⟨k1, k2, -⟩ := key s
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k1
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k2
