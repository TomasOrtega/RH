import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.GramWindow2
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.TieFPowMulFree
import Formalism.PolynomialDimension.ChangeLatticeGoodRank

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM

section Alg

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} (w e : Fin r → σ)

def mX (J l : ℕ) (u v : MvPolynomial σ ℚ_[p]) : ℚ_[p] :=
  M.fockK (((tieE w e) ^ l) (((tieF w e) ^ l) u)) v / (((l.factorial : ℚ_[p]) ^ 2) * (J.choose l : ℚ_[p]))

/- English proof (translation)
Establish `hz` using `Formalism.InvariantFactorPaths.KP.LL.tieF_pow_apply_eq_zero_of_min_lt w e hw he hwe hv`. Unfold `tiePhi`. Rewrite using `[LinearMap.sum_apply, ProjS.fockK_sum_left, Finset.mul_sum]`. Establish `hsub : range (min o n + 1) ⊆ range (o + 1)`. Introduce `l hl`.

Simplify using `only [mem_range] at hl ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.sum_subset hsub]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hl' : l ≤ min o n` using `by simp only [mem_range] at hl; omega`.

Establish `hJM : min o n ≤ o + n + r + z - 1` using `by omega`. Establish `hch` using `Nat.choose_mul (n := o + n + r + z - 1) hl'`. Establish `hch' : ((o + n + r + z - 1).choose (min o n) : ℚ_[p]) * ((min o n).choose l : ℚ_[p]) = ((o + n + r + z - 1).choose l : ℚ_[p]) * ((o + n + r + z - 1 - l).choose (min o n - l) : ℚ_[p])`. Conclude with `hch` after adjusting the coercions. Establish `h1 : ((min o n).choose l : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Nat.choose_pos hl').ne'`.

Establish `h2 : ((o + n + r + z - 1).choose l : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Nat.choose_pos (hl'.trans hJM)).ne'`. Establish `h3 : (l.factorial : ℚ_[p]) ≠ 0` using `by exact_mod_cast l.factorial_ne_zero`. Rewrite using `[LinearMap.smul_apply, ProjS.fockK_smul_left, LinearMap.comp_apply]`. Unfold `mX`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(M.fockK (((tieE w e) ^ l) (((tieF w e) ^ l) u)) v) * hch'`. Introduce `l _ hl`. Establish `hl' : min o n < l` using `by simp only [mem_range] at hl; omega`. Rewrite using `[LinearMap.smul_apply, ProjS.fockK_smul_left, LinearMap.comp_apply, ProjS.fockK_tieE_pow, hz l hl', ProjS.fockK_zero_right, mul_zero, mul_zero]`.
-/
theorem phi_pair (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (hr : 1 ≤ r)
    (o n z : ℕ) (u v : MvPolynomial σ ℚ_[p]) (hv : BiHom w e o n v) :
    ((o + n + r + z - 1).choose (min o n) : ℚ_[p]) * M.fockK (tiePhi w e o n z u) v =
      ∑ l ∈ range (min o n + 1), (-1 : ℚ_[p]) ^ l * ((o + n + r + z - 1 - l).choose (min o n - l) : ℚ_[p]) *
        mX w e (min o n) l u v := by
  have hz := Formalism.InvariantFactorPaths.KP.LL.tieF_pow_apply_eq_zero_of_min_lt w e hw he hwe hv
  unfold tiePhi
  rw [LinearMap.sum_apply, ProjS.fockK_sum_left, Finset.mul_sum]
  have hsub : range (min o n + 1) ⊆ range (o + 1) := by
    intro l hl; simp only [mem_range] at hl ⊢; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ min o n := by simp only [mem_range] at hl; omega
    have hJM : min o n ≤ o + n + r + z - 1 := by omega
    have hch := Nat.choose_mul (n := o + n + r + z - 1) hl'
    have hch' : ((o + n + r + z - 1).choose (min o n) : ℚ_[p]) * ((min o n).choose l : ℚ_[p]) =
        ((o + n + r + z - 1).choose l : ℚ_[p]) * ((o + n + r + z - 1 - l).choose (min o n - l) : ℚ_[p]) := by
      exact_mod_cast hch
    have h1 : ((min o n).choose l : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hl').ne'
    have h2 : ((o + n + r + z - 1).choose l : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hl'.trans hJM)).ne'
    have h3 : (l.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
    rw [LinearMap.smul_apply, ProjS.fockK_smul_left, LinearMap.comp_apply]
    unfold mX
    field_simp
    linear_combination (M.fockK (((tieE w e) ^ l) (((tieF w e) ^ l) u)) v) * hch'
  · intro l _ hl
    have hl' : min o n < l := by simp only [mem_range] at hl; omega
    rw [LinearMap.smul_apply, ProjS.fockK_smul_left, LinearMap.comp_apply, ProjS.fockK_tieE_pow, hz l hl',
      ProjS.fockK_zero_right, mul_zero, mul_zero]

end Alg

def cW {K : Type} [Field K] (q J : ℕ) (mm : ℕ → K) (i : ℕ) : K :=
  ∑ l ∈ range (J + 1), if i + l ≤ J then (-1 : K) ^ l * ((q - l).choose (J - l - i) : K) * mm l else 0

/- English proof (translation)
Unfold `cW`. Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hl' : l ≤ J` using `by simp only [mem_range] at hl; omega`.

Establish `hv : (q + z - l).choose (J - l) = ∑ i ∈ range (J - l + 1), z.choose i * (q - l).choose (J - l - i)`. Rewrite using `[show q + z - l = z + (q - l) by omega, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Rewrite using `[hv]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Establish `hsub : range (J - l + 1) ⊆ range (J + 1)`. Introduce `i hi`. Simplify using `only [mem_range] at hi ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.sum_subset hsub]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `: i + l ≤ J` using `by simp only [mem_range] at hi; omega`. Rewrite using `[if_pos this]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i _ hi`.

Establish `: ¬ (i + l ≤ J)` using `by simp only [mem_range] at hi; omega`. Rewrite using `[if_neg this, zero_mul]`.
-/
theorem cW_sum {K : Type} [Field K] (q J z : ℕ) (hq : J ≤ q) (mm : ℕ → K) :
    ∑ i ∈ range (J + 1), cW q J mm i * (z.choose i : K) =
      ∑ l ∈ range (J + 1), (-1 : K) ^ l * ((q + z - l).choose (J - l) : K) * mm l := by
  unfold cW
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ J := by simp only [mem_range] at hl; omega
  have hv : (q + z - l).choose (J - l) = ∑ i ∈ range (J - l + 1), z.choose i * (q - l).choose (J - l - i) := by
    rw [show q + z - l = z + (q - l) by omega, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [hv]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  have hsub : range (J - l + 1) ⊆ range (J + 1) := by
    intro i hi; simp only [mem_range] at hi ⊢; omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : i + l ≤ J := by simp only [mem_range] at hi; omega
    rw [if_pos this]; ring
  · intro i _ hi
    have : ¬ (i + l ≤ J) := by simp only [mem_range] at hi; omega
    rw [if_neg this, zero_mul]

/- English proof (translation)
Unfold `cW`. Rewrite using `[Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Rewrite using `[if_neg (by omega)]`.

Introduce `h`. Simplify using `at h`.
-/
theorem cW_top {K : Type} [Field K] (q J : ℕ) (mm : ℕ → K) : cW q J mm J = mm 0 := by
  unfold cW
  rw [Finset.sum_eq_single 0]
  · simp
  · intro l _ hl
    rw [if_neg (by omega)]
  · intro h; simp at h

/- English proof (translation)
Unfold `cW`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l hl => ?_` and prove the remaining obligations. Establish `hl' : l ≤ J` using `by simp only [mem_range] at hl; omega`. Use `split_ifs`. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`.

Establish `h1 : ‖(((q - l).choose (J - l - i) : ℕ) : ℚ_[p])‖ ≤ 1`. Rewrite using `[← PadicInt.coe_natCast, ← PadicInt.norm_def]`. Conclude with `PadicInt.norm_le_one _`. Combine the equalities or inequalities in the displayed calculation. Simplify using the standard rewrite rules.
-/
theorem cW_norm {p : ℕ} [Fact p.Prime] (q J : ℕ) (mm : ℕ → ℚ_[p]) (h : ∀ l ≤ J, ‖mm l‖ ≤ 1) (i : ℕ) :
    ‖cW q J mm i‖ ≤ 1 := by
  unfold cW
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l hl => ?_
  have hl' : l ≤ J := by simp only [mem_range] at hl; omega
  split_ifs
  · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖(((q - l).choose (J - l - i) : ℕ) : ℚ_[p])‖ ≤ 1 := by
      rw [← PadicInt.coe_natCast, ← PadicInt.norm_def]; exact PadicInt.norm_le_one _
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul h1 (h l hl') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp

end Formalism.MainNotions.G.GramWindowAlt

end
