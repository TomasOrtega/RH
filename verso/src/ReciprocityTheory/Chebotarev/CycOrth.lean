import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `Nrm`. Rewrite using `[Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `q.ne_bot`.
-/
theorem cyor_nrm_pos (q : Prm E) : 0 < Nrm q := by
  unfold Nrm
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact q.ne_bot

/- English proof (translation)
Rewrite using `[Complex.norm_natCast_cpow_of_pos (cyor_nrm_pos q)]`. Simplify using the standard rewrite rules.
-/
theorem cyor_norm_cpow (q : Prm E) (s : ℝ) :
    ‖((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ = ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_pos (cyor_nrm_pos q)]
  simp

/- English proof (translation)
Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.
-/
theorem cyor_cast_rpow (q : Prm E) (s : ℝ) :
    ((((Nrm q : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) = ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

/- English proof (translation)
Rewrite using `[norm_mul, cyor_norm_cpow]`. Establish `h1` using `DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)`. Establish `h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s)` using `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Use polynomial arithmetic with `[norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]`.
-/
theorem cyor_term_norm_le {l : ℕ} (χ : DirichletCharacter ℂ l) (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [norm_mul, cyor_norm_cpow]
  have h1 := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]

/- English proof (translation)
The claim follows from `Summable.of_norm_bounded hS (fun q => cyor_term_norm_le χ q s)`.
-/
theorem cyor_summable {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Summable (fun q : Prm E => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
  Summable.of_norm_bounded hS (fun q => cyor_term_norm_le χ q s)

/- English proof (translation)
Unfold `Psum Pcl`. Repeatedly rewrite using `[← tsum_mul_left]`. Rewrite using `[← Summable.tsum_finsetSum (fun χ _ => (cyor_summable χ s hS).mul_left _)]`. Rewrite using `[Complex.ofReal_tsum, ← tsum_mul_left]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Establish `hinv : (((a⁻¹ : (ZMod l)ˣ) : ZMod l)) = ((a : ZMod l))⁻¹`. Rewrite using `[ZMod.inv_coe_unit]`. Repeatedly rewrite using `[← mul_assoc]`. Rewrite using `[← Finset.sum_mul]`.

Repeatedly rewrite using `[hinv]`. Rewrite using `[DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]`. Distinguish the cases in `h : (a : ZMod l) = ((Nrm q : ℕ) : ZMod l)`. Rewrite using `[if_pos h, if_pos h.symm, cyor_cast_rpow]`. Rewrite using `[if_neg h, if_neg (Ne.symm h)]`.

Simplify using the standard rewrite rules.
-/
theorem psum_orth (l : ℕ) [NeZero l] (a : (ZMod l)ˣ) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ∑ χ : DirichletCharacter ℂ l, χ ((a⁻¹ : (ZMod l)ˣ) : ZMod l) * Psum E χ s
      = ((Nat.totient l : ℕ) : ℂ) * (Pcl E l (a : ZMod l) s : ℂ) := by
  unfold Psum Pcl
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun χ _ => (cyor_summable χ s hS).mul_left _)]
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  congr 1
  funext q
  have hinv : (((a⁻¹ : (ZMod l)ˣ) : ZMod l)) = ((a : ZMod l))⁻¹ := by
    rw [ZMod.inv_coe_unit]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp_rw [hinv]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit]
  by_cases h : (a : ZMod l) = ((Nrm q : ℕ) : ZMod l)
  · rw [if_pos h, if_pos h.symm, cyor_cast_rpow]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

/- English proof (translation)
Unfold `Psum PE`. Use `(norm_tsum_le_tsum_norm (cyor_summable χ s hS).norm).trans ?_` and prove the remaining obligations. Conclude with `Summable.tsum_le_tsum (fun q => cyor_term_norm_le χ q s) (cyor_summable χ s hS).norm hS`.
-/
theorem norm_psum_le {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ‖Psum E χ s‖ ≤ PE E s := by
  unfold Psum PE
  refine (norm_tsum_le_tsum_norm (cyor_summable χ s hS).norm).trans ?_
  exact Summable.tsum_le_tsum (fun q => cyor_term_norm_le χ q s) (cyor_summable χ s hS).norm hS

/- English proof (translation)
Unfold `Pcl Psum`. Rewrite using `[Complex.re_tsum (cyor_summable _ s hS)]`. Establish `hS2 : Summable (fun q : Prm E => if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0)`. Use `Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS` and prove the remaining obligations. Use `split_ifs`.

Conclude with `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Conclude with `le_rfl`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `Real.rpow_nonneg (Nat.cast_nonneg _) _`.

Use `Summable.tsum_le_tsum (fun q => ?_) hS2 (Complex.reCLM.summable (cyor_summable _ s hS))` and prove the remaining obligations. Rewrite using `[← cyor_cast_rpow]`. Use `split_ifs with h`. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Distinguish the cases in `hu : IsUnit ((Nrm q : ℕ) : ZMod l)`. Rewrite using `[MulChar.one_apply hu, one_mul, Complex.ofReal_re]`. Conclude with `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Rewrite using `[MulChar.map_nonunit _ hu]`. Simplify using the standard rewrite rules.
-/
theorem pcl_one_le_re_psum_one (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    Pcl E l 1 s ≤ (Psum E (1 : DirichletCharacter ℂ l) s).re := by
  unfold Pcl Psum
  rw [Complex.re_tsum (cyor_summable _ s hS)]
  have hS2 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine Summable.tsum_le_tsum (fun q => ?_) hS2 (Complex.reCLM.summable (cyor_summable _ s hS))
  rw [← cyor_cast_rpow]
  split_ifs with h
  · rw [h]; simp
  · by_cases hu : IsUnit ((Nrm q : ℕ) : ZMod l)
    · rw [MulChar.one_apply hu, one_mul, Complex.ofReal_re]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [MulChar.map_nonunit _ hu]; simp

/- English proof (translation)
The claim follows from `(Complex.re_le_norm _).trans (norm_psum_le _ s hS)`.
-/
theorem re_psum_one_le (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ PE E s :=
  (Complex.re_le_norm _).trans (norm_psum_le _ s hS)

/- English proof (translation)
Unfold `Pcl`. Use `tsum_nonneg (fun q => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Conclude with `le_rfl`.
-/
theorem pcl_nonneg (l : ℕ) (a : ZMod l) (s : ℝ) : 0 ≤ Pcl E l a s := by
  unfold Pcl
  refine tsum_nonneg (fun q => ?_)
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact le_rfl

end ReciprocityTheory.Cheb
