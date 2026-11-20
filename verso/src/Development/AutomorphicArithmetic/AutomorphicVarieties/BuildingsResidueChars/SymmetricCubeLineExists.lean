import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

/- English proof (translation)
Establish `e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) = ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k)`. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Establish `e0` using `congrFun (congrFun e 0) 0`.

Establish `e1` using `congrFun (congrFun e 1) 0`. Rewrite `e0`, `e1` using `[Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]`. Establish `t : Matrix.trace ((g * r * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = Matrix.trace (r : Matrix (Fin 2) (Fin 2) k)`. Rewrite using `[Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, inv_mul_cancel_left]`. Rewrite `t` using `[Matrix.trace_fin_two, Matrix.trace_fin_two]`.

Rewrite `e0`, `e1` using `[h10, h00]`. Rewrite `t` using `[h00, h11]`. Use `⟨?_, ?_, t.symm⟩` and prove the remaining obligations. Rewrite using `[e0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : k) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      r 0 0 + r 1 1 = a + b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.trace ((g * r * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.trace (r : Matrix (Fin 2) (Fin 2) k) := by
    rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, inv_mul_cancel_left]
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at t
  rw [h10, h00] at e0 e1
  rw [h00, h11] at t
  refine ⟨?_, ?_, t.symm⟩
  · rw [e0]; ring
  · rw [e1]; ring

/- English proof (translation)
Introduce `l _ Γ _ H ρ ξ κ hρ ⟨g, hg⟩ hκ ⟨s₀, hs₀, hne⟩`. Establish `key` using `fun s : H => col_eq g (ρ s) _ _ ((hg s).1 1 0 (by decide)) ((hg s).2 0) ((hg s).2 1)`. Establish `hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 - (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0`. Use `(g⁻¹).det_ne_zero` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis.

Generalize the expression as in `(g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet`. Generalize the expression as in `(g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet`. Establish `hge : 1 ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖`. Assume the negation of the conclusion as `hlt`. Apply `hne` to reduce the goal to its premises.

Establish `h1 : ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - (ξ s₀ : Qbar l)‖ < 1` using `hκ ⟨s₀, hs₀⟩`. Rewrite `h1` using `[norm_sub_rev]`. Establish `e : (ξ s₀ : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((ξ s₀ : Qbar l) - (κ 0 ⟨s₀, hs₀⟩ : Qbar l)) + (((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) + (ρ s₀ 1 1 - 1))`. Rewrite using `[Units.val_one]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `Cong`. Rewrite using `[e]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 ?_)` and prove the remaining obligations. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) (hρ s₀).1)`. Establish `hqp : ‖q‖ ≤ ‖p‖`.

Establish `e : ((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) * q = ρ s₀ 1 0 * p`. Use `(key ⟨s₀, hs₀⟩).2.1` as an intermediate fact. Simplify using `only at this`. Take the linear combination `-this`. Combine the equalities or inequalities in the displayed calculation.

Establish `hp : p ≠ 0`. Introduce and unpack `rfl`. Rewrite `hqp` using `[norm_zero, norm_le_zero_iff]`. Simplify using `[hqp] at hdet`. Use `⟨q / p, ?_, fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ hqp (norm_nonneg _)`. Take `⟨k1, k2, k3⟩` from `key s`. Establish `a1 : ρ s 0 0 + ρ s 0 1 * (q / p) = κ 0 s`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `k1`. Use `⟨a1, ?_, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `k2`. Take the linear combination `k3 - a1`.
-/
theorem UpperTheory.symmetric_cube_line_exists :
    UpperTheory.V.Sd.S3.LineEx := by
  intro l _ Γ _ H ρ ξ κ hρ ⟨g, hg⟩ hκ ⟨s₀, hs₀, hne⟩
  have key := fun s : H => col_eq g (ρ s) _ _ ((hg s).1 1 0 (by decide)) ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hge : 1 ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ := by
    by_contra hlt
    apply hne
    have h1 : ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - (ξ s₀ : Qbar l)‖ < 1 := hκ ⟨s₀, hs₀⟩
    rw [norm_sub_rev] at h1
    have e : (ξ s₀ : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) = ((ξ s₀ : Qbar l) - (κ 0 ⟨s₀, hs₀⟩ : Qbar l)) +
        (((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) + (ρ s₀ 1 1 - 1)) := by
      rw [Units.val_one]; ring
    unfold Cong
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) (hρ s₀).1)
  have hqp : ‖q‖ ≤ ‖p‖ := by
    have e : ((κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1) * q = ρ s₀ 1 0 * p := by
      have := (key ⟨s₀, hs₀⟩).2.1
      simp only at this
      linear_combination -this
    calc ‖q‖ ≤ ‖(κ 0 ⟨s₀, hs₀⟩ : Qbar l) - ρ s₀ 1 1‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hge
      _ = ‖ρ s₀ 1 0‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]
      _ ≤ ‖p‖ := mul_le_of_le_one_left (norm_nonneg _) (hρ s₀).2
  have hp : p ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_le_zero_iff] at hqp
    simp [hqp] at hdet
  refine ⟨q / p, ?_, fun s => ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ hqp (norm_nonneg _)
  · obtain ⟨k1, k2, k3⟩ := key s
    have a1 : ρ s 0 0 + ρ s 0 1 * (q / p) = κ 0 s := by
      field_simp
      linear_combination k1
    refine ⟨a1, ?_, ?_⟩
    · field_simp
      linear_combination k2
    · linear_combination k3 - a1
