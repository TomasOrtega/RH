import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnramifiedNearIntegralComplexPadicStatement

noncomputable section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda.KurUnr

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `e : y ^ (i + 1) - z ^ (i + 1) = y * (y ^ i - z ^ i) + (y - z) * z ^ i` using `by ring`. Rewrite using `[e]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pow_sub_pow_le {y z : K} (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (i : ℕ) :
    ‖y ^ i - z ^ i‖ ≤ ‖y - z‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : y ^ (i + 1) - z ^ (i + 1) = y * (y ^ i - z ^ i) + (y - z) * z ^ i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖y‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
            mul_le_mul hy ih (norm_nonneg _) zero_le_one
        _ = ‖y - z‖ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖y - z‖ * ‖z‖ ^ i ≤ ‖y - z‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
        _ = ‖y - z‖ := mul_one _

/- English proof (translation)
Rewrite using `[Polynomial.eval_eq_sum_range y, Polynomial.eval_eq_sum_range z, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_eval_sub_eval_le (f : Polynomial K) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {y z : K}
    (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) : ‖f.eval y - f.eval z‖ ≤ ‖y - z‖ := by
  rw [Polynomial.eval_eq_sum_range y, Polynomial.eval_eq_sum_range z, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  rw [← mul_sub, norm_mul]
  calc ‖f.coeff i‖ * ‖y ^ i - z ^ i‖ ≤ 1 * ‖y - z‖ :=
        mul_le_mul (hf i) (norm_pow_sub_pow_le hy hz i) (norm_nonneg _) zero_le_one
    _ = ‖y - z‖ := one_mul _

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `set n := f.natDegree`. Establish `e` using `hm.as_sum`. Establish `h0 : z ^ n = -∑ i ∈ Finset.range n, f.coeff i * z ^ i`.

Use `congrArg (Polynomial.eval z) e` as an intermediate fact. Rewrite `this` using `[hz]`. Simplify using `only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C] at this`. Take the linear combination `-this`. Establish `hz0 : (0 : ℝ) ≤ ‖z‖ ^ (n - 1)` using `by positivity`.

Establish `hb : ‖∑ i ∈ Finset.range n, f.coeff i * z ^ i‖ ≤ ‖z‖ ^ (n - 1)`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hz0 fun i hi => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i ≤ n - 1`. Use `Finset.mem_range.mp hi` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite `hb` using `[← norm_neg, ← h0, norm_pow]`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Simplify using `[hn] at h0`.

Establish `: ‖z‖ ^ (n - 1) < ‖z‖ ^ n` using `pow_lt_pow_right₀ h (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_root_le_one (f : Polynomial K) (hm : f.Monic) (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {z : K}
    (hz : f.eval z = 0) : ‖z‖ ≤ 1 := by
  by_contra h
  push_neg at h
  set n := f.natDegree
  have e := hm.as_sum
  have h0 : z ^ n = -∑ i ∈ Finset.range n, f.coeff i * z ^ i := by
    have := congrArg (Polynomial.eval z) e
    rw [hz] at this
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C] at this
    linear_combination -this
  have hz0 : (0 : ℝ) ≤ ‖z‖ ^ (n - 1) := by positivity
  have hb : ‖∑ i ∈ Finset.range n, f.coeff i * z ^ i‖ ≤ ‖z‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hz0 fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖f.coeff i‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ (n - 1) :=
          mul_le_mul (hf i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖z‖ ^ (n - 1) := one_mul _
  rw [← norm_neg, ← h0, norm_pow] at hb
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn] at h0
  · have : ‖z‖ ^ (n - 1) < ‖z‖ ^ n := pow_lt_pow_right₀ h (by omega)
    linarith

/- English proof (translation)
Take `⟨hp, hl2, hnl, hval, hfr⟩` from `h`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hp.one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hlinv : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`. Establish `hlK : (l : K) ≠ 0`.

Introduce `h0`. Rewrite `hnl` using `[h0, norm_zero]`. Conclude with `(inv_pos.mpr hl0).ne' hnl.symm`. Establish `hiso : ∀ a : K, ‖σ a‖ = ‖a‖`. Introduce `a`.

Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Simplify using the standard rewrite rules. Take `⟨k, hk⟩` from `hval a ha`. Use `set u := a * (l : K) ^ k with hu`. Establish `hc : ‖((l : K) ^ k)‖ = (l : ℝ)⁻¹ ^ k` using `by rw [norm_zpow, hnl]`.

Establish `hun : ‖u‖ = 1`. Rewrite using `[hu, norm_mul, hc, hk, inv_zpow', ← zpow_add₀ hl0.ne', add_neg_cancel, zpow_zero]`. Establish `hsu : ‖σ u‖ = 1`. Establish `h1` using `hfr u hun.le`. Establish `hup : ‖u ^ l‖ = 1` using `by rw [norm_pow, hun, one_pow]`.

Establish `hne : ‖σ u - u ^ l‖ ≠ ‖u ^ l‖` using `by rw [hup]; linarith`. Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, hup, max_eq_right (by linarith)]`. Conclude with `this`. Establish `hσu : σ u = σ a * (l : K) ^ k` using `by rw [hu, map_mul, map_zpow₀, map_natCast]`.

Establish `hcne : ‖((l : K) ^ k)‖ ≠ 0` using `by rw [norm_ne_zero_iff]; exact zpow_ne_zero _ hlK`. Establish `e1 : ‖σ a‖ * ‖((l : K) ^ k)‖ = ‖a‖ * ‖((l : K) ^ k)‖`. Rewrite using `[← norm_mul, ← norm_mul, ← hσu, ← hu, hsu, hun]`. Conclude with `mul_right_cancel₀ hcne e1`. Use `⟨hp, hl2, by rw [hnl]; exact hlinv, ?_, hiso, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Simplify using the standard rewrite rules. Take `⟨k, hk⟩` from `hval x hx0`. Rewrite using `[hnl, hk]`.

Establish `hkneg : k ≤ -1`. Assume the negation of the conclusion as `hk1`. Use `push_neg at hk1`. Establish `: (1 : ℝ) ≤ (l : ℝ) ^ k` using `one_le_zpow₀ hl1.le (by omega)`. Rewrite `this` using `[← hk]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Introduce `x hx`. Conclude with `(hfr x hx).trans_lt hlinv`.
-/
theorem unr_of_unrOK (l : ℕ) (σ : K →+* K) (h : Formalism.InvariantFactorPaths.G7.UnrOK K l σ) : Unr K l σ := by
  obtain ⟨hp, hl2, hnl, hval, hfr⟩ := h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnl
    exact (inv_pos.mpr hl0).ne' hnl.symm

  have hiso : ∀ a : K, ‖σ a‖ = ‖a‖ := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    obtain ⟨k, hk⟩ := hval a ha
    set u := a * (l : K) ^ k with hu
    have hc : ‖((l : K) ^ k)‖ = (l : ℝ)⁻¹ ^ k := by rw [norm_zpow, hnl]
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_mul, hc, hk, inv_zpow', ← zpow_add₀ hl0.ne', add_neg_cancel, zpow_zero]
    have hsu : ‖σ u‖ = 1 := by
      have h1 := hfr u hun.le
      have hup : ‖u ^ l‖ = 1 := by rw [norm_pow, hun, one_pow]
      have hne : ‖σ u - u ^ l‖ ≠ ‖u ^ l‖ := by rw [hup]; linarith
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [sub_add_cancel, hup, max_eq_right (by linarith)] at this
      exact this
    have hσu : σ u = σ a * (l : K) ^ k := by rw [hu, map_mul, map_zpow₀, map_natCast]
    have hcne : ‖((l : K) ^ k)‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact zpow_ne_zero _ hlK
    have e1 : ‖σ a‖ * ‖((l : K) ^ k)‖ = ‖a‖ * ‖((l : K) ^ k)‖ := by
      rw [← norm_mul, ← norm_mul, ← hσu, ← hu, hsu, hun]
    exact mul_right_cancel₀ hcne e1
  refine ⟨hp, hl2, by rw [hnl]; exact hlinv, ?_, hiso, ?_⟩
  · intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    obtain ⟨k, hk⟩ := hval x hx0
    rw [hnl, hk]
    have hkneg : k ≤ -1 := by
      by_contra hk1
      push_neg at hk1
      have : (1 : ℝ) ≤ (l : ℝ) ^ k := one_le_zpow₀ hl1.le (by omega)
      rw [← hk] at this
      linarith
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le hkneg
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  · intro x hx
    exact (hfr x hx).trans_lt hlinv

end GlobalTheory.Honda.KurUnr

open GlobalTheory.Honda.KurUnr in

/- English proof (translation)
Introduce `l _ _`. Use `⟨?_, fun σ hσ => unr_of_unrOK l σ hσ⟩` and prove the remaining obligations. Introduce `f hm hdeg hf`. Use `set g : Polynomial ℂ_[l] := f.map (MaximalUnramifiedExtension l).subtype with hg`. Establish `hgm : g.Monic` using `hm.map _`.

Establish `hgdeg : g.natDegree = f.natDegree` using `Polynomial.natDegree_map _`. Establish `hgc : ∀ n, ‖g.coeff n‖ ≤ 1` using `fun n => by`. Rewrite using `[hg, Polynomial.coeff_map]`. Conclude with `hf n`. Establish `hdg : g.degree ≠ 0`.

Rewrite using `[Polynomial.degree_eq_natDegree hgm.ne_zero, hgdeg]`. Conclude with `hdeg.ne'` after adjusting the coercions. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root g hdg`. Establish `hz1 : ‖z‖ ≤ 1` using `norm_root_le_one g hgm hgc hz`. Take `⟨y, hyK, hy1, hzy⟩` from `GlobalTheory.T.exists_unramified_near_integral_complexPadic l z hz1`.

Use `⟨⟨y, hyK⟩, hy1, ?_⟩` and prove the remaining obligations. Establish `hev : ((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l]) = g.eval y`. Rewrite using `[hg, Polynomial.eval_map]`. Conclude with `(Polynomial.eval₂_hom (MaximalUnramifiedExtension l).subtype ⟨y, hyK⟩).symm`. Express the relevant statement in the definitionally equal form `‖((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1`.

Rewrite using `[hev, ← sub_zero (g.eval y), ← hz]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.Honda.kur_resAlg_unr : ∀ (l : ℕ) [Fact l.Prime], 2 < l →
    ResAlg (MaximalUnramifiedExtension l) ∧ ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension l) l σ → Unr (MaximalUnramifiedExtension l) l σ := by
  intro l _ _
  refine ⟨?_, fun σ hσ => unr_of_unrOK l σ hσ⟩
  intro f hm hdeg hf
  set g : Polynomial ℂ_[l] := f.map (MaximalUnramifiedExtension l).subtype with hg
  have hgm : g.Monic := hm.map _
  have hgdeg : g.natDegree = f.natDegree := Polynomial.natDegree_map _
  have hgc : ∀ n, ‖g.coeff n‖ ≤ 1 := fun n => by
    rw [hg, Polynomial.coeff_map]
    exact hf n
  have hdg : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hgdeg]
    exact_mod_cast hdeg.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdg
  have hz1 : ‖z‖ ≤ 1 := norm_root_le_one g hgm hgc hz
  obtain ⟨y, hyK, hy1, hzy⟩ := GlobalTheory.T.exists_unramified_near_integral_complexPadic l z hz1
  refine ⟨⟨y, hyK⟩, hy1, ?_⟩
  have hev : ((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l]) = g.eval y := by
    rw [hg, Polynomial.eval_map]
    exact (Polynomial.eval₂_hom (MaximalUnramifiedExtension l).subtype ⟨y, hyK⟩).symm
  change ‖((f.eval ⟨y, hyK⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ < 1
  rw [hev, ← sub_zero (g.eval y), ← hz]
  calc ‖g.eval y - g.eval z‖ ≤ ‖y - z‖ := norm_eval_sub_eval_le g hgc hy1 hz1
    _ = ‖z - y‖ := norm_sub_rev _ _
    _ < 1 := hzy
