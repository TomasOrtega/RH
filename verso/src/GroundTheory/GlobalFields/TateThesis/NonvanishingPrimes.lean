import Mathlib
import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
import GroundTheory.GlobalFields.LocalFieldAtPlace

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Complex Topology Filter

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

/- English proof (translation)
Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0` using `fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1` using `fun h ↦ v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)`. Use linear arithmetic over natural numbers and integers.
-/
theorem one_lt_absNorm_asIdeal (v : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h ↦ v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

/- English proof (translation)
Rewrite using `[← normalizedAbv_apply, normalizedAbv_eq_zpow v π.ne_zero, hπ, WithZero.log_exp, zpow_neg, zpow_one]`.
-/
theorem norm_uniformizer {v : HeightOneSpectrum (𝓞 K)} {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ‖(π : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [← normalizedAbv_apply, normalizedAbv_eq_zpow v π.ne_zero, hπ, WithZero.log_exp, zpow_neg,
    zpow_one]

/- English proof (translation)
Rewrite using `[ideleModule_finiteEmbedding, norm_uniformizer hπ]`.
-/
theorem ideleModule_finiteEmbedding_of_uniformizer {v : HeightOneSpectrum (𝓞 K)}
    {π : (v.adicCompletion K)ˣ} (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    (ideleModule K (finiteEmbedding v π) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [ideleModule_finiteEmbedding, norm_uniformizer hπ]

/- English proof (translation)
Rewrite using `[norm_natCast_cpow_of_pos hn]`. Simplify using the standard rewrite rules.
-/
theorem norm_natCast_cpow_neg_mul_I {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by
  rw [norm_natCast_cpow_of_pos hn]
  simp

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih => rw [pow_succ, pow_succ, ← ih]`. Both sides reduce to the same expression.
-/
theorem pow_toIdele (n : ℕ) (x : IdeleGroup K) : (χ ^ n).toIdele x = χ.toIdele x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

/- English proof (translation)
Rewrite using `[χ.coeff_asIdeal_of_not_dvd hv, χ.idealCharacter_primeIdealUnit hv hπ, localComponent_apply]`.
-/
theorem coeff_asIdeal_eq_toIdele {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor)
    {π : (v.adicCompletion K)ˣ} (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    χ.coeff v.asIdeal = χ.toIdele (finiteEmbedding v π) := by
  rw [χ.coeff_asIdeal_of_not_dvd hv, χ.idealCharacter_primeIdealUnit hv hπ, localComponent_apply]

/- English proof (translation)
Rewrite using `[χ.coeff_asIdeal_of_not_dvd hv, Circle.norm_coe]`.
-/
theorem norm_coeff_asIdeal_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) : ‖χ.coeff v.asIdeal‖ = 1 := by
  rw [χ.coeff_asIdeal_of_not_dvd hv, Circle.norm_coe]

/- English proof (translation)
Rewrite `hv`, the goal using `[not_dvd_conductor_iff]`. Introduce `a ha`. Establish `h : χ.localComponent v a = 1` using `hv ha`. Rewrite using `[MonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `(χ ^ n).localComponent v a = 1`.

Rewrite `h`, the goal using `[localComponent_apply]`. Rewrite using `[pow_toIdele, h, one_pow]`.
-/
theorem not_dvd_conductor_pow {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor)
    (n : ℕ) : ¬ v.asIdeal ∣ (χ ^ n).conductor := by
  rw [not_dvd_conductor_iff] at hv ⊢
  intro a ha
  have h : χ.localComponent v a = 1 := hv ha
  rw [MonoidHom.mem_ker]
  change (χ ^ n).localComponent v a = 1
  rw [localComponent_apply] at h ⊢
  rw [pow_toIdele, h, one_pow]

/- English proof (translation)
Take `⟨π, hπ⟩` from `exists_uniformizer v`. Rewrite using `[(χ ^ n).coeff_asIdeal_eq_toIdele (χ.not_dvd_conductor_pow hv n) hπ, χ.coeff_asIdeal_eq_toIdele hv hπ, pow_toIdele, Circle.coe_pow]`.
-/
theorem coeff_pow_asIdeal {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor)
    (n : ℕ) : (χ ^ n).coeff v.asIdeal = χ.coeff v.asIdeal ^ n := by
  obtain ⟨π, hπ⟩ := exists_uniformizer v
  rw [(χ ^ n).coeff_asIdeal_eq_toIdele (χ.not_dvd_conductor_pow hv n) hπ,
    χ.coeff_asIdeal_eq_toIdele hv hπ, pow_toIdele, Circle.coe_pow]

/- English proof (translation)
Establish `hN : (0 : ℝ) < Ideal.absNorm v.asIdeal` using `Nat.cast_pos.2 (zero_lt_one.trans (one_lt_absNorm_asIdeal v))`. Rewrite using `[χ.coeff_asIdeal_eq_toIdele hv hπ, ideleModule_finiteEmbedding_of_uniformizer hπ, ofReal_inv_cpow_of_pos hN, ofReal_natCast]`.
-/
theorem coeff_mul_cpow_eq {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor)
    {π : (v.adicCompletion K)ˣ} (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (t : ℝ) :
    χ.coeff v.asIdeal * (Ideal.absNorm v.asIdeal : ℂ) ^ (-((t : ℂ) * I)) =
      χ.toIdele (finiteEmbedding v π) *
        ((ideleModule K (finiteEmbedding v π) : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal :=
    Nat.cast_pos.2 (zero_lt_one.trans (one_lt_absNorm_asIdeal v))
  rw [χ.coeff_asIdeal_eq_toIdele hv hπ, ideleModule_finiteEmbedding_of_uniformizer hπ,
    ofReal_inv_cpow_of_pos hN, ofReal_natCast]

end HeckeCharacter

/- English proof (translation)
Establish `hac₀ : ‖(a : ℂ)‖ < 1`. Simplify using `only [Complex.norm_of_nonneg ha₀, ha₁]`. Establish `hac₁ : ‖a * z‖ < 1` using `by rwa [norm_mul, hz, mul_one]`. Establish `hac₂ : ‖a * z ^ 2‖ < 1` using `by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]`. Rewrite using `[← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]`.

Use `tsum_nonneg fun n ↦ ?_` and prove the remaining obligations. Simplify using `only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul, sub_zero]`. Break down `n.eq_zero_or_pos with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [← mul_div_assoc, ← add_div]`.

Use `div_nonneg ?_ n.cast_nonneg` and prove the remaining obligations. Rewrite using `[← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]`. Use `convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_neg_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

/- English proof (translation)
Establish `hw1 : ‖w‖ ≤ 1`. Break down `h with ⟨hz, rfl⟩ | ⟨_, hw⟩` into its components or cases. Rewrite using `[norm_pow, hz, one_pow]`. Conclude with `hw`. Establish `hz1 : ‖z‖ ≤ 1`.

Break down `h with ⟨hz, _⟩ | ⟨rfl, _⟩` into its components or cases. Conclude with `hz.le`. Simplify using the standard rewrite rules. Establish `ha : ‖(a : ℂ)‖ = a` using `Complex.norm_of_nonneg ha₀`. Establish `hlt : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖(a : ℂ) * u‖ < 1` using `fun u hu ↦ by`.

Rewrite using `[norm_mul, ha]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos : ∀ u : ℂ, ‖u‖ ≤ 1 → 0 < ‖1 - (a : ℂ) * u‖` using `fun u hu ↦ by`. Use `norm_pos_iff.2 fun h0 ↦ ?_` and prove the remaining obligations. Establish `h1 : (a : ℂ) * u = 1` using `(sub_eq_zero.1 h0).symm`.

Establish `h2` using `hlt u hu`. Rewrite `h2` using `[h1, norm_one]`. Conclude with `lt_irrefl _ h2`. Establish `h0 : ‖(1 : ℂ) - a‖ = 1 - a`. Rewrite using `[← ofReal_one, ← ofReal_sub, Complex.norm_of_nonneg (by linarith)]`.

Establish `hA : 0 < ‖(1 : ℂ) - a‖` using `by rw [h0]; linarith`. Establish `hB` using `hpos z hz1`. Establish `hC` using `hpos w hw1`. Use `set P := ‖(1 : ℂ) - a‖ ^ 3 * ‖1 - (a : ℂ) * z‖ ^ 4 * ‖1 - (a : ℂ) * w‖ with hP`. Establish `hP0 : 0 < P` using `by positivity`.

Establish `hP1 : P ≤ 1`. Break down `h with ⟨hz, rfl⟩ | ⟨rfl, hw⟩` into its components or cases. Establish `hc` using `re_neg_log_comb_nonneg ha₀ ha₁ hz`. Simplify using `only [neg_re, log_re] at hc`. Establish `hlog : Real.log P ≤ 0`.

Rewrite using `[hP, Real.log_mul (by positivity) hC.ne', Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(Real.log_nonpos_iff hP0.le).1 hlog`. Establish `hC' : ‖1 - (a : ℂ) * w‖ ≤ 1 + a`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_one, norm_mul, ha]`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hP, h0, mul_zero, sub_zero, norm_one, one_pow, mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_inv, inv_pow, inv_pow, ← mul_inv, ← mul_inv]`. Conclude with `one_le_inv_iff₀.2 ⟨hP0, hP1⟩`.
-/
theorem one_le_norm_euler_comb {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z w : ℂ}
    (h : (‖z‖ = 1 ∧ w = z ^ 2) ∨ (z = 0 ∧ ‖w‖ ≤ 1)) :
    1 ≤ ‖(1 - (a : ℂ))⁻¹ ^ 3 * (1 - a * z)⁻¹ ^ 4 * (1 - a * w)⁻¹‖ := by
  have hw1 : ‖w‖ ≤ 1 := by
    rcases h with ⟨hz, rfl⟩ | ⟨_, hw⟩
    · rw [norm_pow, hz, one_pow]
    · exact hw
  have hz1 : ‖z‖ ≤ 1 := by
    rcases h with ⟨hz, _⟩ | ⟨rfl, _⟩
    · exact hz.le
    · simp
  have ha : ‖(a : ℂ)‖ = a := Complex.norm_of_nonneg ha₀
  have hlt : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖(a : ℂ) * u‖ < 1 := fun u hu ↦ by
    rw [norm_mul, ha]
    calc a * ‖u‖ ≤ a * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  have hpos : ∀ u : ℂ, ‖u‖ ≤ 1 → 0 < ‖1 - (a : ℂ) * u‖ := fun u hu ↦ by
    refine norm_pos_iff.2 fun h0 ↦ ?_
    have h1 : (a : ℂ) * u = 1 := (sub_eq_zero.1 h0).symm
    have h2 := hlt u hu
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have h0 : ‖(1 : ℂ) - a‖ = 1 - a := by
    rw [← ofReal_one, ← ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  have hA : 0 < ‖(1 : ℂ) - a‖ := by rw [h0]; linarith
  have hB := hpos z hz1
  have hC := hpos w hw1
  set P := ‖(1 : ℂ) - a‖ ^ 3 * ‖1 - (a : ℂ) * z‖ ^ 4 * ‖1 - (a : ℂ) * w‖ with hP
  have hP0 : 0 < P := by positivity
  have hP1 : P ≤ 1 := by
    rcases h with ⟨hz, rfl⟩ | ⟨rfl, hw⟩
    · have hc := re_neg_log_comb_nonneg ha₀ ha₁ hz
      simp only [neg_re, log_re] at hc
      have hlog : Real.log P ≤ 0 := by
        rw [hP, Real.log_mul (by positivity) hC.ne', Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow]
        push_cast
        linarith
      exact (Real.log_nonpos_iff hP0.le).1 hlog
    · have hC' : ‖1 - (a : ℂ) * w‖ ≤ 1 + a := by
        calc ‖1 - (a : ℂ) * w‖ ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) * w‖ := norm_sub_le _ _
          _ ≤ 1 + a := by
            rw [norm_one, norm_mul, ha]
            gcongr
            calc a * ‖w‖ ≤ a * 1 := by gcongr
              _ = a := mul_one a
      rw [hP, h0, mul_zero, sub_zero, norm_one, one_pow, mul_one]
      calc (1 - a) ^ 3 * ‖1 - (a : ℂ) * w‖ ≤ (1 - a) ^ 3 * (1 + a) := by
            gcongr
        _ ≤ 1 := by nlinarith [mul_nonneg ha₀ ha₀, mul_nonneg (mul_nonneg ha₀ ha₀) ha₀]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_inv, inv_pow, inv_pow,
    ← mul_inv, ← mul_inv]
  exact one_le_inv_iff₀.2 ⟨hP0, hP1⟩

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

/- English proof (translation)
Establish `h0 : 1 < (σ : ℂ).re` using `by simpa using hσ`. Establish `h1 : 1 < ((σ : ℂ) + t * I).re` using `by simpa using hσ`. Establish `h2 : 1 < ((σ : ℂ) + 2 * t * I).re` using `by simpa using hσ`. Establish `P0` using `(1 : HeckeCharacter K).LFunction_hasProd_all h0`. Rewrite `P0` using `[LFunction_one]`.

Establish `P` using `((P0.pow 3).mul ((χ.LFunction_hasProd_all h1).pow 4)).mul ((χ ^ 2).LFunction_hasProd_all h2)`. Establish `hcl : IsClosed {x : ℂ | 1 ≤ ‖x‖}` using `isClosed_le continuous_const continuous_norm`. Use `hcl.mem_of_tendsto (show Tendsto _ _ _ from P) (Eventually.of_forall fun S ↦ ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, norm_prod]`. Use `Finset.one_le_prod fun v _ ↦ ?_` and prove the remaining obligations.

Establish `hN1` using `one_lt_absNorm_asIdeal v`. Establish `hNpos : (0 : ℝ) < Ideal.absNorm v.asIdeal` using `Nat.cast_pos.2 (zero_lt_one.trans hN1)`. Use `set N : ℕ := Ideal.absNorm v.asIdeal with hN`. Use `set a : ℝ := (N : ℝ) ^ (-σ) with ha`. Establish `ha₀ : 0 ≤ a` using `Real.rpow_nonneg hNpos.le _`.

Establish `ha₁ : a < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (by linarith)`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hNpos.ne'`. Establish `hac : (N : ℂ) ^ (-(σ : ℂ)) = a`. Rewrite using `[ha, ofReal_cpow hNpos.le, ofReal_natCast, ofReal_neg]`. Use `set u : ℂ := (N : ℂ) ^ (-((t : ℂ) * I)) with hu`.

Establish `hu1 : ‖u‖ = 1` using `norm_natCast_cpow_neg_mul_I (zero_lt_one.trans hN1) t`. Establish `e1 : (N : ℂ) ^ (-((σ : ℂ) + t * I)) = a * u`. Rewrite using `[neg_add, cpow_add _ _ hNc, hac]`. Establish `e2 : (N : ℂ) ^ (-((σ : ℂ) + 2 * t * I)) = a * u ^ 2`. Rewrite using `[show -((σ : ℂ) + 2 * t * I) = -(σ : ℂ) + (2 : ℕ) * (-((t : ℂ) * I)) by push_cast; ring, cpow_add _ _ hNc, cpow_nat_mul, hac]`.

Establish `hone : (1 : HeckeCharacter K).coeff v.asIdeal = 1` using `coeff_one v.ne_bot`. Rewrite using `[hone, one_mul, hac, e1, e2]`. Establish `key : ∀ z w : ℂ, (‖z‖ = 1 ∧ w = z ^ 2) ∨ (z = 0 ∧ ‖w‖ ≤ 1) → 1 ≤ ‖(1 - (a : ℂ))⁻¹ ^ 3 * (1 - a * z)⁻¹ ^ 4 * (1 - a * w)⁻¹‖` using `fun z w h ↦ one_le_norm_euler_comb ha₀ ha₁ h`. Establish `k` using `key (χ.coeff v.asIdeal * u) ((χ ^ 2).coeff v.asIdeal * u ^ 2) ?_`. Establish `e : (1 - (a : ℂ))⁻¹ ^ 3 * (1 - χ.coeff v.asIdeal * (a * u))⁻¹ ^ 4 * (1 - (χ ^ 2).coeff v.asIdeal * (a * u ^ 2))⁻¹ = (1 - (a : ℂ))⁻¹ ^ 3 * (1 - a * (χ.coeff v.asIdeal * u))⁻¹ ^ 4 * (1 - a * ((χ ^ 2).coeff v.asIdeal * u ^ 2))⁻¹` using `by ring`.

Rewrite using `[e]`. Conclude with `k`. Distinguish the cases in `hv : v.asIdeal ∣ χ.conductor`. Use `right`. Use `⟨by rw [χ.coeff_asIdeal_of_dvd hv, zero_mul], ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_pow, hu1, one_pow, mul_one]`. Conclude with `(χ ^ 2).norm_coeff_le _`. Use `left`. Use `⟨by rw [norm_mul, χ.norm_coeff_asIdeal_of_not_dvd hv, hu1, one_mul], ?_⟩` and prove the remaining obligations. Rewrite using `[χ.coeff_pow_asIdeal hv, mul_pow]`.
-/
theorem one_le_norm_dedekindZeta_pow_mul {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖dedekindZeta K σ ^ 3 * χ.LFunction (σ + t * I) ^ 4 *
      (χ ^ 2).LFunction (σ + 2 * t * I)‖ := by
  have h0 : 1 < (σ : ℂ).re := by simpa using hσ
  have h1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simpa using hσ
  have P0 := (1 : HeckeCharacter K).LFunction_hasProd_all h0
  rw [LFunction_one] at P0
  have P := ((P0.pow 3).mul ((χ.LFunction_hasProd_all h1).pow 4)).mul
    ((χ ^ 2).LFunction_hasProd_all h2)
  have hcl : IsClosed {x : ℂ | 1 ≤ ‖x‖} := isClosed_le continuous_const continuous_norm
  refine hcl.mem_of_tendsto (show Tendsto _ _ _ from P) (Eventually.of_forall fun S ↦ ?_)
  simp only [Set.mem_ofPred_eq, norm_prod]
  refine Finset.one_le_prod fun v _ ↦ ?_

  have hN1 := one_lt_absNorm_asIdeal v
  have hNpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := Nat.cast_pos.2 (zero_lt_one.trans hN1)
  set N : ℕ := Ideal.absNorm v.asIdeal with hN
  set a : ℝ := (N : ℝ) ^ (-σ) with ha
  have ha₀ : 0 ≤ a := Real.rpow_nonneg hNpos.le _
  have ha₁ : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (by linarith)
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hac : (N : ℂ) ^ (-(σ : ℂ)) = a := by
    rw [ha, ofReal_cpow hNpos.le, ofReal_natCast, ofReal_neg]
  set u : ℂ := (N : ℂ) ^ (-((t : ℂ) * I)) with hu
  have hu1 : ‖u‖ = 1 := norm_natCast_cpow_neg_mul_I (zero_lt_one.trans hN1) t
  have e1 : (N : ℂ) ^ (-((σ : ℂ) + t * I)) = a * u := by
    rw [neg_add, cpow_add _ _ hNc, hac]
  have e2 : (N : ℂ) ^ (-((σ : ℂ) + 2 * t * I)) = a * u ^ 2 := by
    rw [show -((σ : ℂ) + 2 * t * I) = -(σ : ℂ) + (2 : ℕ) * (-((t : ℂ) * I)) by push_cast; ring,
      cpow_add _ _ hNc, cpow_nat_mul, hac]
  have hone : (1 : HeckeCharacter K).coeff v.asIdeal = 1 := coeff_one v.ne_bot
  rw [hone, one_mul, hac, e1, e2]
  have key : ∀ z w : ℂ, (‖z‖ = 1 ∧ w = z ^ 2) ∨ (z = 0 ∧ ‖w‖ ≤ 1) →
      1 ≤ ‖(1 - (a : ℂ))⁻¹ ^ 3 * (1 - a * z)⁻¹ ^ 4 * (1 - a * w)⁻¹‖ :=
    fun z w h ↦ one_le_norm_euler_comb ha₀ ha₁ h
  have k := key (χ.coeff v.asIdeal * u) ((χ ^ 2).coeff v.asIdeal * u ^ 2) ?_
  · have e : (1 - (a : ℂ))⁻¹ ^ 3 * (1 - χ.coeff v.asIdeal * (a * u))⁻¹ ^ 4 *
        (1 - (χ ^ 2).coeff v.asIdeal * (a * u ^ 2))⁻¹ =
        (1 - (a : ℂ))⁻¹ ^ 3 * (1 - a * (χ.coeff v.asIdeal * u))⁻¹ ^ 4 *
          (1 - a * ((χ ^ 2).coeff v.asIdeal * u ^ 2))⁻¹ := by ring
    rw [e]
    exact k
  by_cases hv : v.asIdeal ∣ χ.conductor
  · right
    refine ⟨by rw [χ.coeff_asIdeal_of_dvd hv, zero_mul], ?_⟩
    rw [norm_mul, norm_pow, hu1, one_pow, mul_one]
    exact (χ ^ 2).norm_coeff_le _
  · left
    refine ⟨by rw [norm_mul, χ.norm_coeff_asIdeal_of_not_dvd hv, hu1, one_mul], ?_⟩
    rw [χ.coeff_pow_asIdeal hv, mul_pow]

end HeckeCharacter

end

end GroundTheory.Global
