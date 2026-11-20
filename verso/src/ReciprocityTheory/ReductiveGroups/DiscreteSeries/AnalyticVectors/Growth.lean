import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

/- English proof (translation)
Unfold `actM`. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)`.
-/
theorem actM_mem_layer_succ (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k) :
    actM E X x ∈ layer ε E V (k + 1) := by
  unfold actM
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (apply_mem_layer_succ hE hV a b hx)

/- English proof (translation)
Establish `hs` using `Real.sqrt_nonneg (max 0 (-d))`. Establish `hs2 : √(max 0 (-d)) ^ 2 = max 0 (-d)` using `Real.sq_sqrt (le_max_left _ _)`. Establish `hm : -d ≤ max 0 (-d)` using `le_max_right _ _`. Rewrite using `[Real.sqrt_le_left (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sqrt_sub_le_add {y d : ℝ} (hy : 0 ≤ y) : √(y ^ 2 - d) ≤ y + √(max 0 (-d)) := by
  have hs := Real.sqrt_nonneg (max 0 (-d))
  have hs2 : √(max 0 (-d)) ^ 2 = max 0 (-d) := Real.sq_sqrt (le_max_left _ _)
  have hm : -d ≤ max 0 (-d) := le_max_right _ _
  rw [Real.sqrt_le_left (by positivity)]
  · nlinarith

/- English proof (translation)
Use `set f : Fin n × Fin n → ℝ := fun p => ‖X p.1 p.2‖ with hf`. Use `set g : Fin n × Fin n → ℝ := fun p => if ε p.1 ≠ ε p.2 then ‖E p.1 p.2 x‖ else 0 with hg`. Establish `h1 : ‖actM E X x‖ ≤ ∑ p : Fin n × Fin n, f p * g p`. Unfold `actM`. Rewrite using `[LinearMap.sum_apply, Fintype.sum_prod_type]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, norm_smul]`. Distinguish the cases in `hab : ε a = ε b`.

Simplify using `[hf, hg, hab, inP_apply_eq_zero hX hab]`. Simplify using `[hf, hg, hab]`. Establish `h2` using `Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n × Fin n)) f g`. Establish `hfs : ∑ p : Fin n × Fin n, f p ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2`. Rewrite using `[Fintype.sum_prod_type]`.

Establish `hgs : ∑ p : Fin n × Fin n, g p ^ 2 = ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hab : ε a = ε b <;> simp [hg, hab]`. Rewrite `h2` using `[hfs, hgs]`. Use `set y : ℝ := R + √2 * k with hy`. Establish `hy0 : 0 ≤ y` using `by positivity`. Establish `h3 : √(∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2) ≤ (R + √(max 0 (-d)) + √2 * k) * ‖x‖`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (le_max_left _ _), Real.sqrt_sq (norm_nonneg x)]`. Conclude with `Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))`. Use `_ ≤ (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)` and prove the remaining obligations.

Use `sqrt_sub_le_add (d := d) hy0` as an intermediate fact. Break down `le_total 0 (y ^ 2 - d) with h | h` into its components or cases. Rewrite using `[max_eq_right h]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_left h, Real.sqrt_zero]`.

Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_actM_le {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k) :
    ‖actM E X x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
  set f : Fin n × Fin n → ℝ := fun p => ‖X p.1 p.2‖ with hf
  set g : Fin n × Fin n → ℝ := fun p => if ε p.1 ≠ ε p.2 then ‖E p.1 p.2 x‖ else 0 with hg
  have h1 : ‖actM E X x‖ ≤ ∑ p : Fin n × Fin n, f p * g p := by
    unfold actM
    rw [LinearMap.sum_apply, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [LinearMap.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [LinearMap.smul_apply, norm_smul]
    by_cases hab : ε a = ε b
    · simp [hf, hg, hab, inP_apply_eq_zero hX hab]
    · simp [hf, hg, hab]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset (Fin n × Fin n)) f g
  have hfs : ∑ p : Fin n × Fin n, f p ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hgs : ∑ p : Fin n × Fin n, g p ^ 2 =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : ε a = ε b <;> simp [hg, hab]
  rw [hfs, hgs] at h2
  set y : ℝ := R + √2 * k with hy
  have hy0 : 0 ≤ y := by positivity
  have h3 : √(∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2) ≤
      (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
    calc _ ≤ √((y ^ 2 - d) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt (hR k x hx)
      _ ≤ √(max 0 (y ^ 2 - d)) * ‖x‖ := by
          rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (le_max_left _ _),
            Real.sqrt_sq (norm_nonneg x)]
          exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      _ ≤ (R + √(max 0 (-d)) + √2 * k) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          have := sqrt_sub_le_add (d := d) hy0
          rcases le_total 0 (y ^ 2 - d) with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, Real.sqrt_zero]; positivity
  calc ‖actM E X x‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * ((R + √(max 0 (-d)) + √2 * k) * ‖x‖) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hx`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ← add_assoc]`. Conclude with `actM_mem_layer_succ hE hV hX ih`.
-/
theorem actM_pow_mem_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {k : ℕ} {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) : ((actM E X) ^ m) x ∈ layer ε E V (k + m) := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact actM_mem_layer_succ hE hV hX ih

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Establish `h` using `norm_actM_le hR0 hR hX (k + m) (actM_pow_mem_layer hE hV hX hx m)`.

Establish `hc : 0 ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ))`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_range_succ, pow_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_actM_pow_le (hE : IsGlRep E) (hV : IsKStableSub ε E V) {R d : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 - d) * ‖x‖ ^ 2)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (k : ℕ) {x : M} (hx : x ∈ layer ε E V k)
    (m : ℕ) :
    ‖((actM E X) ^ m) x‖ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
      (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := norm_actM_le hR0 hR hX (k + m) (actM_pow_mem_layer hE hV hX hx m)
    have hc : 0 ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) := by
      positivity
    calc _ ≤ _ := h
      _ ≤ √(∑ a, ∑ b, ‖X a b‖ ^ 2) * (R + √(max 0 (-d)) + √2 * ((k + m : ℕ) : ℝ)) *
          (√(∑ a, ∑ b, ‖X a b‖ ^ 2) ^ m *
            (∏ l ∈ range m, (R + √(max 0 (-d)) + √2 * ((k : ℝ) + l))) * ‖x‖) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = _ := by
          rw [Finset.prod_range_succ, pow_succ]
          push_cast
          ring

end Unitary

end ReciprocityTheory.ChartRestriction.DS
