import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceWeight

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_` and prove the remaining obligations. Rewrite using `[one_mul]`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `inl i => simp [inrL]`.

Consider the case `inr j => simpa [inrL] using norm_le_pi_norm y j`.
-/
theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] : ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inl j)`.
-/
theorem norm_le_norm_elim_left {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖x‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inl j)

/- English proof (translation)
Establish `hfun : (sliceR f x : (κ' → V) → ℂ) = (fun z => f (Sum.elim x 0 + z)) ∘ (inrL (V` using `V) κ κ') := by`. Use function extensionality and compare the values at `y'`. Simplify using `only [sliceR_apply, Function.comp_apply]`. Conclude with `congrArg f (congrFun (elim_eq_add (V := V) (κ' := κ') x) y')`. Establish `hg : ContDiff ℝ ∞ (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z))` using `(f.smooth ⊤).comp (contDiff_const.add contDiff_id)`.

Rewrite using `[hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top)]`. Establish `h2 : iteratedFDeriv ℝ n (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) (inrL κ κ' y) = iteratedFDeriv ℝ n f (Sum.elim x y)`. Rewrite using `[iteratedFDeriv_comp_add_left]`. Use `congr 1`. Conclude with `(congrFun (elim_eq_add (V := V) (κ' := κ') x) y).symm`.

Rewrite using `[h2]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∏ _i : Fin n, ‖(inrL (V` using `V) κ κ')‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem iteratedFDeriv_sliceR_norm_le {κ κ' : Type} [Fintype κ] [Fintype κ']
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (n : ℕ) (y : κ' → V) :
    ‖iteratedFDeriv ℝ n (sliceR f x) y‖ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
  have hfun : (sliceR f x : (κ' → V) → ℂ) = (fun z => f (Sum.elim x 0 + z)) ∘ (inrL (V := V) κ κ') := by
    funext y'
    simp only [sliceR_apply, Function.comp_apply]
    exact congrArg f (congrFun (elim_eq_add (V := V) (κ' := κ') x) y')
  have hg : ContDiff ℝ ∞ (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top)]
  have h2 : iteratedFDeriv ℝ n (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) (inrL κ κ' y)
      = iteratedFDeriv ℝ n f (Sum.elim x y) := by
    rw [iteratedFDeriv_comp_add_left]
    congr 1
    exact (congrFun (elim_eq_add (V := V) (κ' := κ') x) y).symm
  rw [h2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖(inrL (V := V) κ κ')‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
  calc _ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ * 1 := by gcongr
    _ = _ := mul_one _

/- English proof (translation)
Establish `hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖) ≤ SchwartzMap.seminorm ℂ (a + k) n f`. Introduce `y`. Establish `h1` using `iteratedFDeriv_sliceR_norm_le f x n y`. Establish `hx` using `norm_le_norm_elim_left x y`. Establish `hy` using `norm_le_norm_elim x y`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_add, mul_assoc]`. Use `_ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _`. Break down `eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos` into its components or cases. Rewrite using `[← h0, zero_mul]`.

Conclude with `apply_nonneg _ _`. Rewrite using `[mul_comm, ← le_div_iff₀ hpos]`. Use `SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hpos, mul_comm]`. Conclude with `hpt y`.
-/
theorem pow_norm_mul_seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
  have hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
      ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
    intro y
    have h1 := iteratedFDeriv_sliceR_norm_le f x n y
    have hx := norm_le_norm_elim_left x y
    have hy := norm_le_norm_elim x y
    calc ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
        ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ a * (‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ k
            * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖) := by gcongr
      _ = ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ (a + k) * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
          rw [pow_add, mul_assoc]
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos
  · rw [← h0, zero_mul]; exact apply_nonneg _ _
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt y

end GlobalTheory.SliceWeight
