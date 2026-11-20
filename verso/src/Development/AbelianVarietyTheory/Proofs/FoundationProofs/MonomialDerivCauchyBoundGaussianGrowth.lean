import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GaussCauchy

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast h`. Establish `hpi` using `Real.pi_pos`.

Rewrite using `[div_le_iff₀ (by positivity), ← mul_pow]`. Establish `h1 : 2 * Real.exp 1 * Real.pi * B / A * (A * n / Real.pi) = (2 * B) * n * Real.exp 1`. Clear the denominators using the available nonvanishing facts. Establish `h2 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n` using `by exact_mod_cast Nat.factorial_le_pow n`. Establish `h3 : (n : ℝ) ^ n ≤ (2 * B) ^ n` using `pow_le_pow_left₀ hn0.le hn n`.

Rewrite using `[h1, mul_pow, mul_pow (2 * B), ← Real.exp_nat_mul, mul_one, sq]`. Use `mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le` and prove the remaining obligations. Conclude with `mul_le_mul (h2.trans h3) h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n).trans h3)`.
-/
theorem factor_le (A B : ℝ) (hA : 0 < A) (n : ℕ) (hn : (n : ℝ) ≤ 2 * B) :
    ((n.factorial : ℝ)) ^ 2 * Real.exp n / (A * n / Real.pi) ^ n
      ≤ (2 * Real.exp 1 * Real.pi * B / A) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity), ← mul_pow]
  have h1 : 2 * Real.exp 1 * Real.pi * B / A * (A * n / Real.pi) = (2 * B) * n * Real.exp 1 := by
    field_simp
  have h2 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h3 : (n : ℝ) ^ n ≤ (2 * B) ^ n := pow_le_pow_left₀ hn0.le hn n
  rw [h1, mul_pow, mul_pow (2 * B), ← Real.exp_nat_mul, mul_one, sq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul (h2.trans h3) h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n).trans h3)

/- English proof (translation)
Establish `hpi` using `Real.pi_pos`. Establish `hsq : ∀ k, Real.sqrt (A * α k / Real.pi) ^ 2 = A * α k / Real.pi` using `fun k => Real.sq_sqrt (by positivity)`. Establish `h` using `norm_pderivIter_le_of_differentiable (F := F) (a := 0) (r := fun k => Real.sqrt (A * α k / Real.pi)) (M := Real.sqrt (S * Real.exp (∑ k, (α k : ℝ)))) α (fun k => Real.sqrt_nonneg _) (fun k hk => by`. Establish `: (0 : ℝ) < α k` using `by exact_mod_cast Nat.pos_of_ne_zero hk`. Conclude with `Real.sqrt_pos.mpr (by positivity)) hF`.

Use the proof step `(fun z hz => by`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use `(hb z).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 2`. Simplify using `only [Pi.zero_apply, sub_zero] at hz`.

Simplify using `only [hz, hsq, Finset.mul_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use the proof step `field_simp)`. Use `(pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_` and prove the remaining obligations. Rewrite using `[div_pow, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow, ← Finset.prod_pow, Real.exp_sum, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_div_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]`.

Use `mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_) hS` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm (α k) 2, pow_mul, hsq]`. Conclude with `factor_le A B hA _ (hα k)`.
-/
theorem pderivIter_sq_le {ι : Type*} [DecidableEq ι] [Fintype ι] (F : (ι → ℂ) → ℂ) (S A B : ℝ)
    (hA : 0 < A) (hS : 0 ≤ S) (hF : Differentiable ℂ F)
    (hb : ∀ z, ‖F z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ k, ‖z k‖ ^ 2) / A))
    (α : ι →₀ ℕ) (hα : ∀ k, (α k : ℝ) ≤ 2 * B) :
    ‖pderivIter α F 0‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (∑ k, α k) := by
  have hpi := Real.pi_pos
  have hsq : ∀ k, Real.sqrt (A * α k / Real.pi) ^ 2 = A * α k / Real.pi := fun k =>
    Real.sq_sqrt (by positivity)
  have h := norm_pderivIter_le_of_differentiable (F := F) (a := 0)
    (r := fun k => Real.sqrt (A * α k / Real.pi))
    (M := Real.sqrt (S * Real.exp (∑ k, (α k : ℝ)))) α (fun k => Real.sqrt_nonneg _)
    (fun k hk => by
      have : (0 : ℝ) < α k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact Real.sqrt_pos.mpr (by positivity)) hF
    (fun z hz => by
      apply Real.le_sqrt_of_sq_le
      refine (hb z).trans (le_of_eq ?_)
      congr 2
      simp only [Pi.zero_apply, sub_zero] at hz
      simp only [hz, hsq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow, ← Finset.prod_pow,
    Real.exp_sum, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_div_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_) hS
  rw [← pow_mul, mul_comm (α k) 2, pow_mul, hsq]
  exact factor_le A B hA _ (hα k)

noncomputable def curry (D : D7) (N N' : ℕ) :
    (D.what₂.Tau × Fin N' × Fin N → ℂ) →ₗ[ℂ] VC D N N' where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Take `⟨a, b, c⟩` from `k`. Simplify using `[curry, coordV, Pi.single_apply, Prod.ext_iff]`.
-/
theorem curry_single (D : D7) (N N' : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    curry D N N' (Pi.single k 1) = coordV D k := by
  funext τ i j
  obtain ⟨a, b, c⟩ := k
  simp [curry, coordV, Pi.single_apply, Prod.ext_iff]

/- English proof (translation)
Establish `hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Establish `han : AnalyticAt ℂ G 0` using `SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)`. Rewrite using `[taylor, mul_div_cancel₀ _ hne, pderivIter, pderivList, lineDerivList_comp_linearMap, ← lineDerivList_ofFn han]`. Simplify using `only [map_zero, List.map_map]`. Use `congr 1`.

Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `i h1 h2`. Simplify using `[curry_single]`.
-/
theorem factorial_mul_taylor (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α
      = pderivIter α (fun w => G (curry D N N' w)) 0 := by
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [taylor, mul_div_cancel₀ _ hne, pderivIter, pderivList, lineDerivList_comp_linearMap,
    ← lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curry_single]

/- English proof (translation)
Introduce `D N N' G S A B hA _ hS hG hb α hα`. Rewrite using `[factorial_mul_taylor D N N' G hG, Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Use `pderivIter_sq_le _ S A B hA hS (hG.comp (LinearMap.toContinuousLinearMap (curry D N N')).differentiable) (fun z => ?_) α hα` and prove the remaining obligations. Simplify using `only [Fintype.sum_prod_type]`. Conclude with `hb (curry D N N' z)`.
-/
theorem monomial_deriv_bound : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  intro D N N' G S A B hA _ hS hG hb α hα
  rw [factorial_mul_taylor D N N' G hG, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine pderivIter_sq_le _ S A B hA hS
    (hG.comp (LinearMap.toContinuousLinearMap (curry D N N')).differentiable) (fun z => ?_) α hα
  simp only [Fintype.sum_prod_type]
  exact hb (curry D N N' z)

end GlobalTheory.GaussCauchy
