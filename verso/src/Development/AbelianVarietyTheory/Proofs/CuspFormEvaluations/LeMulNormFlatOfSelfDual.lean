import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate

namespace GlobalTheory.TensorLat

open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

/- English proof (translation)
Use `le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖i.1 (w k)‖) fun k => ‖γ k i‖)` and prove the remaining obligations. Use `pow_le_pow_left₀ (norm_nonneg _) ?_ 2` and prove the remaining obligations. Rewrite using `[contr_apply]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem norm_sq_contr_apply_le (γ : Fin n → Vsp dim) (w : Fin n → E) (i : Idx dim) :
    ‖contr γ w i‖ ^ 2 ≤ (∑ k, ‖i.1 (w k)‖ ^ 2) * ∑ k, ‖γ k i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖i.1 (w k)‖)
    fun k => ‖γ k i‖)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [contr_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

/- English proof (translation)
Rewrite using `[norm_sq_flat, EuclideanSpace.norm_sq_eq]`. Simplify using `only [EuclideanSpace.norm_sq_eq (γ _)]`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => (norm_sq_contr_apply_le γ w i).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (hw i.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)`.
-/
theorem norm_sq_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {R : ℝ}
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ R) :
    ‖contr γ w‖ ^ 2 ≤ R * ‖flat γ‖ ^ 2 := by
  rw [norm_sq_flat, EuclideanSpace.norm_sq_eq]
  simp only [EuclideanSpace.norm_sq_eq (γ _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (norm_sq_contr_apply_le γ w i).trans ?_
  exact mul_le_mul_of_nonneg_right (hw i.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/- English proof (translation)
Use `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[mul_pow]`. Conclude with `norm_sq_contr_le γ w hw`.
-/
theorem norm_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ ρ ^ 2) :
    ‖contr γ w‖ ≤ ρ * ‖flat γ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow]
  exact norm_sq_contr_le γ w hw

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hγ (eq_zero_of_contr_span hspan (by rintro _ ⟨i, rfl⟩; exact h i))`.
-/
theorem exists_contr_ne_zero {ι : Type*} (v : ι → Fin n → E)
    (hspan : Submodule.span E (Set.range v) = ⊤) {γ : Fin n → Vsp dim} (hγ : γ ≠ 0) :
    ∃ i, contr γ (v i) ≠ 0 := by
  by_contra h
  push Not at h
  exact hγ (eq_zero_of_contr_span hspan (by rintro _ ⟨i, rfl⟩; exact h i))

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_contr_ne_zero v hspan h0`. Conclude with `(hlam _ (hγ _ (hv i)) hi).trans (norm_contr_le γ (v i) hρ (hlen i))`.
-/
theorem le_mul_norm_flat (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) {ι : Type*}
    (v : ι → Fin n → E) (hv : ∀ i, v i ∈ Λ') (hspan : Submodule.span E (Set.range v) = ⊤)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hlen : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ ρ * ‖flat γ‖ := by
  obtain ⟨i, hi⟩ := exists_contr_ne_zero v hspan h0
  exact (hlam _ (hγ _ (hv i)) hi).trans (norm_contr_le γ (v i) hρ (hlen i))

omit [IsCMField E] in

/- English proof (translation)
The claim follows from `eq_top_iff.2 fun x _ => Submodule.span_le_restrictScalars ℚ E S (h ▸ Submodule.mem_top (x := x))`.
-/
theorem span_eq_top_of_rat {S : Set (Fin n → E)} (h : Submodule.span ℚ S = ⊤) :
    Submodule.span E S = ⊤ :=
  eq_top_iff.2 fun x _ => Submodule.span_le_restrictScalars ℚ E S (h ▸ Submodule.mem_top (x := x))

/- English proof (translation)
Take `⟨v, hv, -, hspan, hlen⟩` from `exists_short_vectors Λ' hfg hint hdual`. Establish `hr : 0 ≤ rdE E` using `Real.rpow_nonneg (abs_nonneg _) _`. Conclude with `le_mul_norm_flat X Λ' v hv (span_eq_top_of_rat hspan) (by positivity) hlen hlam hγ h0`.
-/
theorem le_mul_norm_flat_of_selfDual (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E * ‖flat γ‖ := by
  obtain ⟨v, hv, -, hspan, hlen⟩ := exists_short_vectors Λ' hfg hint hdual
  have hr : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  exact le_mul_norm_flat X Λ' v hv (span_eq_top_of_rat hspan) (by positivity) hlen hlam hγ h0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Use `mem_tensorLat_stdLat.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using `using hx`.

Simplify using `[h]`. Rewrite using `[norm_sq_flat, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ h`. Simplify using `[h]`.

Simplify using the standard rewrite rules.
-/
example (X : PT E) (x : Vsp X.dim) (hx : x ∈ X.L) (k : Fin n) :
    Pi.single k x ∈ tensorLat X (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n) ∧
      ‖flat (Pi.single k x : Fin n → Vsp X.dim)‖ ^ 2 = ‖x‖ ^ 2 := by
  constructor
  · refine mem_tensorLat_stdLat.2 fun j => ?_
    by_cases h : j = k
    · subst h; simpa using hx
    · simp [h]
  · rw [norm_sq_flat, Finset.sum_eq_single k]
    · simp
    · intro j _ h; simp [h]
    · simp

end GlobalTheory.TensorLat
