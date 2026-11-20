import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

/- English proof (translation)
Establish `hs : ∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2 = 0` using `(Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)).mp hu`. Establish `hz : h.mat *ᵥ u = 0`. Use function extensionality and compare the values at `i`. Establish `hi` using `(Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hs i (Finset.mem_univ i)`. Simplify using `using hi`.

Use `congrArg (fun w => h.mat⁻¹ *ᵥ w) hz` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]`.
-/
theorem eq_zero_of_hermNorm_eq_zero {n : ℕ} (h : HermNorm n) {u : Fin n → ℂ} (hu : h.norm u = 0) :
    u = 0 := by
  have hs : ∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)).mp hu
  have hz : h.mat *ᵥ u = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hs i (Finset.mem_univ i)
    simpa using hi
  have := congrArg (fun w => h.mat⁻¹ *ᵥ w) hz
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using this

/- English proof (translation)
Rewrite using `[eval_eq', eval_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hw` using `hq (mem_support_iff.mp hd)`. Establish `hrow : ∀ i, ∑ j, d (i, j) = δ`. Introduce `i`.

Use `congrFun hw i` as an intermediate fact. Rewrite `this` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `[groupWeight, Fintype.sum_prod_type, Pi.single_apply, Finset.sum_apply] at this`. Rewrite `this` using `[Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]`. Simplify using `using this`.

Establish `hc : ∏ ij : Fin k × Fin n, c ij.1 ^ d ij = ∏ i, c i ^ δ`. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hrow]`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_scale_groups {k n δ : ℕ} {q : MvPolynomial (Fin k × Fin n) ℂ} (hq : IsMultiHomog δ q)
    (c : Fin k → ℂ) (v : Fin k × Fin n → ℂ) :
    eval (fun ij => c ij.1 * v ij) q = (∏ i, c i ^ δ) * eval v q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hq (mem_support_iff.mp hd)
  have hrow : ∀ i, ∑ j, d (i, j) = δ := by
    intro i
    have := congrFun hw i
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simp [groupWeight, Fintype.sum_prod_type, Pi.single_apply, Finset.sum_apply] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)] at this
    simpa using this
  have hc : ∏ ij : Fin k × Fin n, c ij.1 ^ d ij = ∏ i, c i ^ δ := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hrow]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

/- English proof (translation)
Establish `e : nrmGroups h k v = fun ij => (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) ij.1 * v ij` using `rfl`. Rewrite using `[e, eval_scale_groups hq (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) v]`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hv` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos δ with rfl | hpos` into its components or cases. Simplify using the standard rewrite rules.

Use `pow_ne_zero _ fun hc => hv ?_` and prove the remaining obligations. Establish `hn : h.norm (fun j => v (i, j)) = 0` using `by simpa using hc`. Establish `hr` using `eq_zero_of_hermNorm_eq_zero h hn`. Establish `hv' : v = fun ij => (Function.update (1 : Fin k → ℂ) i 0) ij.1 * v ij`. Use function extensionality and compare the values at `⟨a, j⟩`.

Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality. Simplify using `using congrFun hr j`. Simplify using `[Function.update_of_ne ha]`. Rewrite using `[hv', eval_scale_groups hq, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hpos.ne']), zero_mul]`.
-/
theorem eval_nrmGroups_ne_zero {k n δ : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin k × Fin n) ℂ}
    (hq : IsMultiHomog δ q) {v : Fin k × Fin n → ℂ} (hv : eval v q ≠ 0) :
    eval (nrmGroups h k v) q ≠ 0 := by
  classical
  have e : nrmGroups h k v =
      fun ij => (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) ij.1 * v ij := rfl
  rw [e, eval_scale_groups hq (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) v]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hv
  rcases Nat.eq_zero_or_pos δ with rfl | hpos
  · simp
  refine pow_ne_zero _ fun hc => hv ?_
  have hn : h.norm (fun j => v (i, j)) = 0 := by simpa using hc
  have hr := eq_zero_of_hermNorm_eq_zero h hn
  have hv' : v = fun ij => (Function.update (1 : Fin k → ℂ) i 0) ij.1 * v ij := by
    funext ⟨a, j⟩
    by_cases ha : a = i
    · subst ha
      simpa using congrFun hr j
    · simp [Function.update_of_ne ha]
  rw [hv', eval_scale_groups hq, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hpos.ne']), zero_mul]

/- English proof (translation)
Set `f : Fin e × Fin n → MvPolynomial (Fin (e + 1) × Fin n) ℂ` to `fun ij => ∑ k, C (h.mat⁻¹ ij.2 k) * X (ij.1.succ, k)`. Establish `key : ∀ π : Fin (e + 1) → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) (bind₁ f q) = eval (coefRows h π) q`. Introduce `π`. Establish `hf : (fun ij => eval (fun ij => π ij.1 ij.2) (f ij)) = coefRows h π`. Use function extensionality and compare the values at `ij`.

Simplify using `[f, coefRows, Matrix.mulVec, dotProduct]`. Rewrite using `[← hf]`. Conclude with `eval₂Hom_bind₁ _ _ _ _`. Use `⟨bind₁ f q, fun hQ => hq (MvPolynomial.funext fun v => ?_), key⟩` and prove the remaining obligations. Establish `hv : coefRows h (Fin.cons 0 fun i => h.mat *ᵥ fun j => v (i, j)) = v`.

Use function extensionality and compare the values at `ij`. Simplify using `[coefRows, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]`. Rewrite using `[map_zero, ← hv, ← key, hQ, map_zero]`.
-/
theorem exists_poly_eval_coefRows {n e : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) :
    ∃ Q : MvPolynomial (Fin (e + 1) × Fin n) ℂ, Q ≠ 0 ∧
      ∀ π : Fin (e + 1) → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) Q = eval (coefRows h π) q := by
  let f : Fin e × Fin n → MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    fun ij => ∑ k, C (h.mat⁻¹ ij.2 k) * X (ij.1.succ, k)
  have key : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) (bind₁ f q) = eval (coefRows h π) q := by
    intro π
    have hf : (fun ij => eval (fun ij => π ij.1 ij.2) (f ij)) = coefRows h π := by
      funext ij
      simp [f, coefRows, Matrix.mulVec, dotProduct]
    rw [← hf]
    exact eval₂Hom_bind₁ _ _ _ _
  refine ⟨bind₁ f q, fun hQ => hq (MvPolynomial.funext fun v => ?_), key⟩
  have hv : coefRows h (Fin.cons 0 fun i => h.mat *ᵥ fun j => v (i, j)) = v := by
    funext ij
    simp [coefRows, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]
  rw [map_zero, ← hv, ← key, hQ, map_zero]

/- English proof (translation)
Introduce `n e δ h q hq hδ`. Take `⟨Q, hQ, key⟩` from `exists_poly_eval_coefRows h hq`. Use `filter_upwards [ConeFibreDegree.ae_eval_matrix_ne_zero Q hQ] with π hπ`. Rewrite `hπ` using `[key]`. Conclude with `eval_nrmGroups_ne_zero h hδ hπ`.
-/
theorem ae_eval_nrmGroups_coefRows_ne_zero :
    ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
      ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  intro n e δ h q hq hδ
  obtain ⟨Q, hQ, key⟩ := exists_poly_eval_coefRows h hq
  filter_upwards [ConeFibreDegree.ae_eval_matrix_ne_zero Q hQ] with π hπ
  rw [key] at hπ
  exact eval_nrmGroups_ne_zero h hδ hπ

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
