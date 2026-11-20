import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Establish `hl' : l ≠ 0` using `hl.ne'`. Use `set ζ : ℂ := cexp (2 * π * Complex.I / l)`. Establish `hζ : IsPrimitiveRoot ζ l` using `Complex.isPrimitiveRoot_exp l hl'`. Establish `e : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℂ) * m) / l) = (ζ ^ m) ^ j`. Introduce `j`.

Rewrite using `[← pow_mul, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]`. Use `split_ifs with h`. Rewrite using `[(hζ.pow_eq_one_iff_dvd m).2 h]`. Simplify using the standard rewrite rules. Establish `h1 : ζ ^ m ≠ 1` using `fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')`.

Rewrite using `[geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]`.
-/
theorem sum_exp_fin_div (l : ℕ) (hl : 0 < l) (m : ℕ) :
    ∑ j : Fin l, cexp (2 * π * Complex.I * ((j : ℕ) * m : ℂ) / l) = if l ∣ m then (l : ℂ) else 0 := by
  have hl' : l ≠ 0 := hl.ne'
  set ζ : ℂ := cexp (2 * π * Complex.I / l)
  have hζ : IsPrimitiveRoot ζ l := Complex.isPrimitiveRoot_exp l hl'
  have e : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℂ) * m) / l) = (ζ ^ m) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

/- English proof (translation)
Establish `hl' : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`. Take `⟨k', rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Simplify using `[slz, repU, Matrix.det_fin_two_of, pow_succ]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem slz_repU (k l : ℕ) (hk : 1 ≤ k) (hl : 0 < l) (j : Fin l) (f : ℍ → ℂ) (τ : ℍ) :
    slz k (repU l j) f τ = (l : ℂ)⁻¹ * f (ofComplex (((τ : ℂ) + (j : ℕ)) / l)) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [slz, repU, Matrix.det_fin_two_of, pow_succ]
  field_simp
  simp

/- English proof (translation)
Take `⟨C, A, hC⟩` from `h`. Establish `C0 : 0 ≤ C`. Use `hC 0` as an intermediate fact. Simplify using `at this`. Combine the linear relations using `[norm_nonneg (a 0)]`.

Use `⟨C * (l : ℝ) ^ A, A, fun n => ?_⟩` and prove the remaining obligations. Establish `h1` using `hC (l * n)`. Establish `hlr : (1 : ℝ) ≤ l` using `by exact_mod_cast hl`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = C * (l : ℝ) ^ A * ((n : ℝ) + 1) ^ A := by rw [mul_pow]; ring`.
-/
theorem polyB_Uo (l : ℕ) (a : ℕ → ℂ) (hl : 0 < l) (h : PolyB a) : PolyB (Uo l a) := by
  obtain ⟨C, A, hC⟩ := h
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    linarith [norm_nonneg (a 0)]
  refine ⟨C * (l : ℝ) ^ A, A, fun n => ?_⟩
  have h1 := hC (l * n)
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  calc ‖Uo l a n‖ = ‖a (l * n)‖ := rfl
    _ ≤ C * (((l * n : ℕ) : ℝ) + 1) ^ A := h1
    _ ≤ C * ((l : ℝ) * ((n : ℝ) + 1)) ^ A := by
        gcongr
        push_cast
        nlinarith
    _ = C * (l : ℝ) ^ A * ((n : ℝ) + 1) ^ A := by rw [mul_pow]; ring

/- English proof (translation)
Introduce `k l a hk hl ha`. Use `⟨polyB_Uo l a hl ha, fun τ => ?_⟩` and prove the remaining obligations. Establish `hl' : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`. Establish `hpos : ∀ j : Fin l, 0 < (((τ : ℂ) + (j : ℕ)) / l).im`. Introduce `j`.

Rewrite using `[Complex.div_natCast_im]`. Conclude with `div_pos (by simpa using τ.im_pos) (by exact_mod_cast hl)`. Repeatedly rewrite using `[slz_repU k l hk hl _ (qs a) τ]`. Establish `hqs : ∀ j : Fin l, qs a (ofComplex (((τ : ℂ) + (j : ℕ)) / l)) = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l))`. Introduce `j`.

Rewrite using `[ofComplex_apply_of_im_pos (hpos j)]`. Both sides reduce to the same expression. Repeatedly rewrite using `[hqs]`. Establish `hsum : ∀ j ∈ (Finset.univ : Finset (Fin l)), Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l))` using `fun j _ => ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 ⟨_, hpos j⟩).of_norm`. Rewrite using `[← Finset.mul_sum, ← Summable.tsum_finsetSum hsum]`.

Establish `hinner : ∀ n : ℕ, ∑ j : Fin l, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) = a n * cexp (2 * π * Complex.I * n * τ / l) * (if l ∣ n then (l : ℂ) else 0)`. Introduce `n`. Rewrite using `[← sum_exp_fin_div l hl n, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc (a n), ← Complex.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hinner, ← tsum_mul_left]`. Establish `hg : Function.Injective (fun m : ℕ => l * m)` using `fun x y h => Nat.eq_of_mul_eq_mul_left hl h`. Rewrite using `[← hg.tsum_eq]`.

Use `show ∑' m : ℕ, Uo l a m * cexp (2 * π * Complex.I * m * τ) = _`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Simplify using `only [Uo, dvd_mul_right, if_true]`. Rewrite using `[show (2 * π * Complex.I * ((l * m : ℕ) : ℂ) * τ / l : ℂ) = 2 * π * Complex.I * m * τ by`. Use `push_cast`.

Use the proof step `field_simp]`. Clear the denominators using the available nonvanishing facts. Introduce `n hn`. Distinguish the cases in `hd : l ∣ n`. Conclude with `⟨n / l, Nat.mul_div_cancel' hd⟩`.

Conclude with `(hn (by simp [hd])).elim`.
-/
theorem Uo_qs_sum_slz : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧
    ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  intro k l a hk hl ha
  refine ⟨polyB_Uo l a hl ha, fun τ => ?_⟩
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hpos : ∀ j : Fin l, 0 < (((τ : ℂ) + (j : ℕ)) / l).im := by
    intro j
    rw [Complex.div_natCast_im]
    exact div_pos (by simpa using τ.im_pos) (by exact_mod_cast hl)
  simp_rw [slz_repU k l hk hl _ (qs a) τ]
  have hqs : ∀ j : Fin l, qs a (ofComplex (((τ : ℂ) + (j : ℕ)) / l))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) := by
    intro j
    rw [ofComplex_apply_of_im_pos (hpos j)]
    rfl
  simp_rw [hqs]
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin l)),
      Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) :=
    fun j _ => ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 ⟨_, hpos j⟩).of_norm
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsum]
  have hinner : ∀ n : ℕ, ∑ j : Fin l, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l))
      = a n * cexp (2 * π * Complex.I * n * τ / l) * (if l ∣ n then (l : ℂ) else 0) := by
    intro n
    rw [← sum_exp_fin_div l hl n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hinner, ← tsum_mul_left]
  have hg : Function.Injective (fun m : ℕ => l * m) := fun x y h => Nat.eq_of_mul_eq_mul_left hl h
  rw [← hg.tsum_eq]
  · show ∑' m : ℕ, Uo l a m * cexp (2 * π * Complex.I * m * τ) = _
    refine tsum_congr fun m => ?_
    simp only [Uo, dvd_mul_right, if_true]
    rw [show (2 * π * Complex.I * ((l * m : ℕ) : ℂ) * τ / l : ℂ) = 2 * π * Complex.I * m * τ by
      push_cast
      field_simp]
    field_simp
  · intro n hn
    by_cases hd : l ∣ n
    · exact ⟨n / l, Nat.mul_div_cancel' hd⟩
    · exact (hn (by simp [hd])).elim

end GlobalTheory.EisM
