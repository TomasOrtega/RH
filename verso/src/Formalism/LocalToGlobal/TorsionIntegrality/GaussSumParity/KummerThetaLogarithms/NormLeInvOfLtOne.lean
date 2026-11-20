import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementC
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)

namespace TraceNormBounds

/- English proof (translation)
Establish `: Fact l.Prime` using `⟨hl⟩`. Establish `: NeZero l` using `⟨hl.ne_zero⟩`. Establish `hprod : ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) = (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l))`. Establish `hr` using `FiniteField.roots_X_pow_card_sub_X (ZMod l)`. Rewrite `hr` using `[ZMod.card]`.

Establish `hdeg` using `FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod l) hl.one_lt`. Establish `hmon : (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)).Monic`. Apply `Polynomial.monic_X_pow_sub` to reduce the goal to its premises. Rewrite using `[Polynomial.degree_X]`. Conclude with `hl.one_lt` after adjusting the coercions.

Establish `h` using `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hr, hdeg]; simp)`. Rewrite `h` using `[hr]`. Conclude with `h`. Establish `hrange : ∏ n ∈ Finset.range l, (Polynomial.X - ((n : ℕ) : Polynomial (ZMod l))) = ∏ a : ZMod l, (Polynomial.X - Polynomial.C a)`. Use `Finset.prod_bij (fun n _ => ((n : ℕ) : ZMod l)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => by rw [map_natCast])` and prove the remaining obligations.

Introduce `a ha b hb hab`. Use `congrArg ZMod.val hab` as an intermediate fact. Rewrite `this` using `[ZMod.val_natCast_of_lt (Finset.mem_range.1 ha), ZMod.val_natCast_of_lt (Finset.mem_range.1 hb)]`. Then use the resulting hypothesis. Introduce `b _`. Conclude with `⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), by simp⟩`.

Express the relevant statement in the definitionally equal form `Polynomial.C (l : ℤ) ∣ _`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `hmap : Polynomial.map (Int.castRingHom (ZMod l)) (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l, (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = 0`.

Rewrite using `[Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_natCast]`. Rewrite using `[hrange, hprod, sub_self]`. Establish `h` using `congrArg (fun P => Polynomial.coeff P i) hmap`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h`.

Conclude with `h`.
-/
theorem poly_id (l : ℕ) (hl : l.Prime) : ∃ Q : Polynomial ℤ,
    (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l,
      (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = Polynomial.C (l : ℤ) * Q := by
  have : Fact l.Prime := ⟨hl⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  have hprod : ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) =
      (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)) := by
    have hr := FiniteField.roots_X_pow_card_sub_X (ZMod l)
    rw [ZMod.card] at hr
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod l) hl.one_lt
    have hmon : (Polynomial.X ^ l - Polynomial.X : Polynomial (ZMod l)).Monic := by
      apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact_mod_cast hl.one_lt
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [hr, hdeg]; simp)
    rw [hr] at h
    exact h
  have hrange : ∏ n ∈ Finset.range l, (Polynomial.X - ((n : ℕ) : Polynomial (ZMod l))) =
      ∏ a : ZMod l, (Polynomial.X - Polynomial.C a) := by
    refine Finset.prod_bij (fun n _ => ((n : ℕ) : ZMod l)) (fun _ _ => Finset.mem_univ _) ?_ ?_
      (fun _ _ => by rw [map_natCast])
    · intro a ha b hb hab
      have := congrArg ZMod.val hab
      rwa [ZMod.val_natCast_of_lt (Finset.mem_range.1 ha),
        ZMod.val_natCast_of_lt (Finset.mem_range.1 hb)] at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), by simp⟩
  change Polynomial.C (l : ℤ) ∣ _
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hmap : Polynomial.map (Int.castRingHom (ZMod l))
      (Polynomial.X ^ l - Polynomial.X - ∏ n ∈ Finset.range l,
        (Polynomial.X - ((n : ℕ) : Polynomial ℤ)) : Polynomial ℤ) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_natCast]
    rw [hrange, hprod, sub_self]
  have h := congrArg (fun P => Polynomial.coeff P i) hmap
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h
  exact h

section Normed

variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))`.
-/
private lemma norm_finset_sum_le_one_of_norm_le_one {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Use `push_cast`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))`.
-/
private lemma norm_natCast_le_one_kummer_theta_logarithms (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

/- English proof (translation)
Break down `Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩` into its components or cases. Conclude with `norm_natCast_le_one_kummer_theta_logarithms n` after adjusting the coercions. Rewrite using `[Int.cast_neg, norm_neg]`. Conclude with `norm_natCast_le_one_kummer_theta_logarithms n` after adjusting the coercions.
-/
private lemma int_lemma_3 (z : ℤ) : ‖(z : K)‖ ≤ 1 := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast norm_natCast_le_one_kummer_theta_logarithms n
  · rw [Int.cast_neg, norm_neg]
    exact_mod_cast norm_natCast_le_one_kummer_theta_logarithms n

/- English proof (translation)
Rewrite using `[Polynomial.eval₂_eq_sum_range]`. Apply `norm_finset_sum_le_one_of_norm_le_one` to reduce the goal to its premises. Introduce `i _`. Establish `hc : ‖(Int.castRingHom K) (Q.coeff i)‖ ≤ 1`. Rewrite using `[eq_intCast]`.

Conclude with `int_lemma_3 _`. Establish `hp : ‖x ^ i‖ ≤ 1`. Rewrite using `[norm_pow]`. Use `first`. Consider the case `exact pow_le_one₀ (norm_nonneg _) hx`.

Consider the case `exact pow_le_one _ (norm_nonneg _) hx`. Rewrite using `[norm_mul]`. Use `first`. Consider the case `exact mul_le_one₀ hc (norm_nonneg _) hp`. Consider the case `exact mul_le_one' hc hp`.

Consider the case `nlinarith [norm_nonneg ((Int.castRingHom K) (Q.coeff i)), norm_nonneg (x ^ i)]`.
-/
theorem norm_eval_le (Q : Polynomial ℤ) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ 1 := by
  rw [Polynomial.eval₂_eq_sum_range]
  apply norm_finset_sum_le_one_of_norm_le_one
  intro i _
  have hc : ‖(Int.castRingHom K) (Q.coeff i)‖ ≤ 1 := by
    rw [eq_intCast]
    exact int_lemma_3 _
  have hp : ‖x ^ i‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | exact pow_le_one _ (norm_nonneg _) hx
  rw [norm_mul]
  first
  | exact mul_le_one₀ hc (norm_nonneg _) hp
  | exact mul_le_one' hc hp
  | nlinarith [norm_nonneg ((Int.castRingHom K) (Q.coeff i)), norm_nonneg (x ^ i)]

/- English proof (translation)
Break down `eq_or_ne y 0 with rfl | hy0` into its components or cases. Simplify using the standard rewrite rules. Take `⟨k, hk⟩` from `hval y hy0`. Rewrite `hy`, the goal using `[hk]`. Establish `hl' : (1 : ℝ) < l` using `by exact_mod_cast hl`.

Establish `hk' : k < 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : (1 : ℝ) ≤ (l : ℝ) ^ k` using `by first`. Consider the case `exact one_le_zpow₀ hl'.le hc`.

Consider the case `exact one_le_zpow_of_nonneg₀ hl'.le hc`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ)` using `by first`. Consider the case `exact zpow_le_zpow_right₀ hl'.le (by omega)`. Consider the case `exact zpow_le_of_le hl'.le (by omega)`.

Simplify using `using h2`.
-/
theorem norm_le_inv_of_lt_one {l : ℕ} (hl : 1 < l)
    (hval : ∀ a : K, a ≠ 0 → ∃ k : ℤ, ‖a‖ = (l : ℝ) ^ k) {y : K} (hy : ‖y‖ < 1) :
    ‖y‖ ≤ (l : ℝ)⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  obtain ⟨k, hk⟩ := hval y hy0
  rw [hk] at hy ⊢
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hk' : k < 0 := by
    by_contra hc
    push_neg at hc
    have h1 : (1 : ℝ) ≤ (l : ℝ) ^ k := by
      first
      | exact one_le_zpow₀ hl'.le hc
      | exact one_le_zpow_of_nonneg₀ hl'.le hc
    linarith
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := by
    first
    | exact zpow_le_zpow_right₀ hl'.le (by omega)
    | exact zpow_le_of_le hl'.le (by omega)
  simpa using h2

end Normed

end TraceNormBounds

open TraceNormBounds

/- English proof (translation)
Unfold `SigmaIsom`. Introduce `K _ _ _ l σ hU a`. Take `⟨hp, h2, hnp, hval, hfr⟩` from `hU`. Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Simplify using the standard rewrite rules.

Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (by omega : 1 < l)`. Establish `hl0 : (l : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `unit : ∀ u : K, ‖u‖ = 1 → ‖σ u‖ = 1`. Introduce `u hu`. Establish `h1` using `hfr u hu.le`.

Establish `h3 : ‖u ^ l‖ = 1` using `by rw [norm_pow, hu, one_pow]`. Establish `h4 : ‖σ u - u ^ l‖ < ‖u ^ l‖`. Rewrite using `[h3]`. Conclude with `lt_of_le_of_lt h1 (inv_lt_one_of_one_lt₀ hl)`. Establish `e : σ u = (σ u - u ^ l) + u ^ l` using `by ring`.

Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h4.ne, h3]`. Conclude with `max_eq_right (h4.trans_eq h3).le`. Take `⟨k, hk⟩` from `hval a ha`. Establish `hnu : ‖a * (l : K) ^ k‖ = 1`. Rewrite using `[norm_mul, norm_zpow, hnp, hk, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero k (by positivity))]`.

Establish `ha' : a = (a * (l : K) ^ k) * (l : K) ^ (-k)`. Rewrite using `[mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, mul_one]`. Rewrite using `[ha', map_mul, map_zpow₀, map_natCast, norm_mul, norm_mul, unit _ hnu, hnu]`.
-/
theorem sigma_isometry : SigmaIsom := by
  unfold SigmaIsom
  intro K _ _ _ l σ hU a
  obtain ⟨hp, h2, hnp, hval, hfr⟩ := hU
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hl : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have unit : ∀ u : K, ‖u‖ = 1 → ‖σ u‖ = 1 := by
    intro u hu
    have h1 := hfr u hu.le
    have h3 : ‖u ^ l‖ = 1 := by rw [norm_pow, hu, one_pow]
    have h4 : ‖σ u - u ^ l‖ < ‖u ^ l‖ := by
      rw [h3]
      exact lt_of_le_of_lt h1 (inv_lt_one_of_one_lt₀ hl)
    have e : σ u = (σ u - u ^ l) + u ^ l := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h4.ne, h3]
    exact max_eq_right (h4.trans_eq h3).le
  obtain ⟨k, hk⟩ := hval a ha
  have hnu : ‖a * (l : K) ^ k‖ = 1 := by
    rw [norm_mul, norm_zpow, hnp, hk, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero k (by positivity))]
  have ha' : a = (a * (l : K) ^ k) * (l : K) ^ (-k) := by
    rw [mul_assoc, ← zpow_add₀ hl0, add_neg_cancel, zpow_zero, mul_one]
  rw [ha', map_mul, map_zpow₀, map_natCast, norm_mul, norm_mul, unit _ hnu, hnu]

/- English proof (translation)
Introduce `K _ _ _ l σ hU`. Take `⟨hp, hp2, hpn, hval, hσ⟩` from `hU`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hp.one_lt`. Establish `hl0 : (l : ℝ) ≠ 0` using `by positivity`. Establish `hinv : ((l : ℝ))⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl1`.

Establish `hlK : (l : K) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`. Establish `step : ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∃ n : ℕ, ‖x - n‖ ≤ (l : ℝ)⁻¹`. Introduce `x hx hfix`. Take `⟨Q, hQ⟩` from `poly_id l hp`. Establish `hev` using `congrArg (Polynomial.eval₂ (Int.castRingHom K) x) hQ`.

Rewrite `hev` using `[Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetProd]`. Simplify using `only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_natCast, eq_intCast, Int.cast_natCast] at hev`. Establish `h1 : ‖x ^ l - x‖ ≤ (l : ℝ)⁻¹`. Use `hσ x hx` as an intermediate fact. Rewrite `this` using `[hfix, norm_sub_rev]`. Then use the resulting hypothesis.

Establish `h2 : ‖(l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ (l : ℝ)⁻¹`. Rewrite using `[norm_mul, hpn]`. Conclude with `mul_le_of_le_one_right (by positivity) (norm_eval_le Q hx)`. Establish `h3 : ‖∏ n ∈ Finset.range l, (x - (n : K))‖ ≤ (l : ℝ)⁻¹`. Establish `e : ∏ n ∈ Finset.range l, (x - (n : K)) = (x ^ l - x) - (l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q`.

Rewrite using `[← hev]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `h4 : ∀ n ∈ Finset.range l, (1 : ℝ) ≤ ‖x - (n : K)‖`. Introduce `n _`. Assume the negation of the conclusion as `hlt`. Conclude with `absurd (norm_le_inv_of_lt_one hp.one_lt hval (not_le.1 hlt)) (not_le.2 (hc n))`.

Establish `h5 : (1 : ℝ) ≤ ‖∏ n ∈ Finset.range l, (x - (n : K))‖`. Rewrite using `[norm_prod]`. Use `Finset.prod_le_prod (s := Finset.range l) (f := fun _ => (1 : ℝ)) (g := fun n : ℕ => ‖x - (n : K)‖) (fun _ _ => zero_le_one) h4` as an intermediate fact. Simplify using `using this`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `x hx hfix k`. Proceed by induction on `k generalizing x with`. Consider the case `zero => exact ⟨0, by simpa using hx⟩`. Consider the case `succ k ih`. Take `⟨n0, hn0⟩` from `step x hx hfix`.

Establish `hy : ‖(x - n0) / (l : K)‖ ≤ 1`. Rewrite using `[norm_div, hpn, div_inv_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hyf : σ ((x - n0) / (l : K)) = (x - n0) / (l : K)`. Rewrite using `[map_div₀, map_sub, map_natCast, map_natCast, hfix]`.

Take `⟨m, hm⟩` from `ih _ hy hyf`. Use `⟨n0 + l * m, ?_⟩` and prove the remaining obligations. Establish `e : x - ((n0 + l * m : ℕ) : K) = (l : K) * ((x - n0) / (l : K) - m)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, hpn, pow_succ, mul_inv, mul_comm]`. Use `gcongr`.
-/
theorem fixed_is_limit : FixedIsLimit := by
  intro K _ _ _ l σ hU
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (l : ℝ) ≠ 0 := by positivity
  have hinv : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have step : ∀ x : K, ‖x‖ ≤ 1 → σ x = x → ∃ n : ℕ, ‖x - n‖ ≤ (l : ℝ)⁻¹ := by
    intro x hx hfix
    obtain ⟨Q, hQ⟩ := poly_id l hp
    have hev := congrArg (Polynomial.eval₂ (Int.castRingHom K) x) hQ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_finsetProd] at hev
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_natCast, eq_intCast,
      Int.cast_natCast] at hev
    have h1 : ‖x ^ l - x‖ ≤ (l : ℝ)⁻¹ := by
      have := hσ x hx
      rwa [hfix, norm_sub_rev] at this
    have h2 : ‖(l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q‖ ≤ (l : ℝ)⁻¹ := by
      rw [norm_mul, hpn]
      exact mul_le_of_le_one_right (by positivity) (norm_eval_le Q hx)
    have h3 : ‖∏ n ∈ Finset.range l, (x - (n : K))‖ ≤ (l : ℝ)⁻¹ := by
      have e : ∏ n ∈ Finset.range l, (x - (n : K)) =
          (x ^ l - x) - (l : K) * Polynomial.eval₂ (Int.castRingHom K) x Q := by
        rw [← hev]; ring
      rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    by_contra hc
    push Not at hc
    have h4 : ∀ n ∈ Finset.range l, (1 : ℝ) ≤ ‖x - (n : K)‖ := by
      intro n _
      by_contra hlt
      exact absurd (norm_le_inv_of_lt_one hp.one_lt hval (not_le.1 hlt)) (not_le.2 (hc n))
    have h5 : (1 : ℝ) ≤ ‖∏ n ∈ Finset.range l, (x - (n : K))‖ := by
      rw [norm_prod]
      have := Finset.prod_le_prod (s := Finset.range l) (f := fun _ => (1 : ℝ))
        (g := fun n : ℕ => ‖x - (n : K)‖) (fun _ _ => zero_le_one) h4
      simpa using this
    linarith
  intro x hx hfix k
  induction k generalizing x with
  | zero => exact ⟨0, by simpa using hx⟩
  | succ k ih =>
    obtain ⟨n0, hn0⟩ := step x hx hfix
    have hy : ‖(x - n0) / (l : K)‖ ≤ 1 := by
      rw [norm_div, hpn, div_inv_eq_mul]
      calc ‖x - n0‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
        _ = 1 := inv_mul_cancel₀ hl0
    have hyf : σ ((x - n0) / (l : K)) = (x - n0) / (l : K) := by
      rw [map_div₀, map_sub, map_natCast, map_natCast, hfix]
    obtain ⟨m, hm⟩ := ih _ hy hyf
    refine ⟨n0 + l * m, ?_⟩
    have e : x - ((n0 + l * m : ℕ) : K) = (l : K) * ((x - n0) / (l : K) - m) := by
      push_cast
      field_simp
      ring
    rw [e, norm_mul, hpn, pow_succ, mul_inv, mul_comm]
    gcongr

/- English proof (translation)
Introduce `K _ _ _ l σ hU τ _ f c hc hfix hs`. Take `⟨hp, hp2, hpn, hval, hσ⟩` from `hU`. Take `⟨h0, hI⟩` from `hs`. Rewrite `h0`, `hI` using `[sub_zero]`. Establish `hp0 : l ≠ 0` using `hp.ne_zero`.

Establish `hD` using `Formalism.InvariantFactorPaths.G7.Top.dworkMv`. Establish `h0' : MvPowerSeries.constantCoeff (MvPowerSeries.C c * f) = 0` using `by simp [h0]`. Use `⟨by rwa [sub_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero, hD K τ l σ hp hpn hσ _ h0']`. Establish `hcf` using `(hD K τ l σ hp hpn hσ f h0).1 hI`.

Introduce `n`. Establish `he : frobVar l (MvPowerSeries.map σ (MvPowerSeries.C c * f)) - MvPowerSeries.C (l : K) * (MvPowerSeries.C c * f) = MvPowerSeries.C c * (frobVar l (MvPowerSeries.map σ f) - MvPowerSeries.C (l : K) * f)`. Rewrite using `[map_mul, MvPowerSeries.map_C, hfix, Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0, Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0, map_mul, MvPowerSeries.expand_C]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, MvPowerSeries.coeff_C_mul, norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hc).trans (hcf n)`.
-/
theorem simeq_fixed : SimeqFixed := by
  intro K _ _ _ l σ hU τ _ f c hc hfix hs
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  obtain ⟨h0, hI⟩ := hs
  rw [sub_zero] at h0 hI
  have hp0 : l ≠ 0 := hp.ne_zero
  have hD := Formalism.InvariantFactorPaths.G7.Top.dworkMv
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.C c * f) = 0 := by simp [h0]
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K τ l σ hp hpn hσ _ h0']
  have hcf := (hD K τ l σ hp hpn hσ f h0).1 hI
  intro n
  have he : frobVar l (MvPowerSeries.map σ (MvPowerSeries.C c * f)) -
      MvPowerSeries.C (l : K) * (MvPowerSeries.C c * f) =
      MvPowerSeries.C c * (frobVar l (MvPowerSeries.map σ f) - MvPowerSeries.C (l : K) * f) := by
    rw [map_mul, MvPowerSeries.map_C, hfix, Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0,
      Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hp0, map_mul, MvPowerSeries.expand_C]
    ring
  rw [he, MvPowerSeries.coeff_C_mul, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hcf n)

/- English proof (translation)
Introduce `K _ _ _ l σ hU τ _ f g hlim hf`. Apply the tactic sequence `have hiso := sigma_isometry K l σ hU`. Take `⟨hp, hp2, hpn, hval, hσ⟩` from `hU`. Establish `hp0 : l ≠ 0` using `hp.ne_zero`. Establish `hD` using `Formalism.InvariantFactorPaths.G7.Top.dworkMv`.

Establish `hcont : Continuous σ` using `(AddMonoidHomClass.isometry_of_norm σ hiso).continuous`. Establish `hf0 : ∀ k, MvPowerSeries.constantCoeff (f k) = 0` using `fun k => by`. Use `(hf k).1` as an intermediate fact. Rewrite `this` using `[sub_zero]`. Then use the resulting hypothesis. Establish `hg0 : MvPowerSeries.constantCoeff g = 0`.

Establish `h` using `hlim 0`. Simplify using `only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0] at h`. Conclude with `tendsto_nhds_unique h tendsto_const_nhds`. Use `⟨by rwa [sub_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero, hD K τ l σ hp hpn hσ _ hg0]`.

Introduce `n`. Establish `hk : ∀ k, ‖MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) - MvPowerSeries.C (l : K) * f k)‖ ≤ (l : ℝ)⁻¹` using `fun k => (hD K τ l σ hp hpn hσ _ (hf0 k)).1 (by have := (hf k).2; rwa [sub_zero] at this) n`. Establish `hT : Filter.Tendsto (fun k => MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) - MvPowerSeries.C (l : K) * f k)) Filter.atTop (nhds (MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ g) - MvPowerSeries.C (l : K) * g)))`. Simplify using `only [map_sub, MvPowerSeries.coeff_C_mul]`. Use `Filter.Tendsto.sub ?_ ((hlim n).const_mul _)` and prove the remaining obligations.

Distinguish the cases in `hd : ∀ i, l ∣ n i`. Choose the witnesses or unpack the hypotheses as in `⟨m, rfl⟩ : ∃ m : τ →₀ ℕ, n = l • m := by`. Use `⟨n.mapRange (· / l) (by simp), ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`.

Conclude with `(Nat.mul_div_cancel' (hd i)).symm`. Simplify using `only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hp0, MvPowerSeries.coeff_map]`. Conclude with `(hcont.tendsto _).comp (hlim m)`. Use `push Not at hd`. Take `⟨i, hi⟩` from `hd`.

Simplify using `only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hp0 _ hi]`. Conclude with `tendsto_const_nhds`. Conclude with `le_of_tendsto hT.norm (Filter.Eventually.of_forall hk)`.
-/
theorem simeq_closed : SimeqClosed := by
  intro K _ _ _ l σ hU τ _ f g hlim hf
  have hiso := sigma_isometry K l σ hU
  obtain ⟨hp, hp2, hpn, hval, hσ⟩ := hU
  have hp0 : l ≠ 0 := hp.ne_zero
  have hD := Formalism.InvariantFactorPaths.G7.Top.dworkMv
  have hcont : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hiso).continuous
  have hf0 : ∀ k, MvPowerSeries.constantCoeff (f k) = 0 := fun k => by
    have := (hf k).1
    rwa [sub_zero] at this
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := hlim 0
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨by rwa [sub_zero], ?_⟩
  rw [sub_zero, hD K τ l σ hp hpn hσ _ hg0]
  intro n
  have hk : ∀ k, ‖MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.C (l : K) * f k)‖ ≤ (l : ℝ)⁻¹ := fun k =>
    (hD K τ l σ hp hpn hσ _ (hf0 k)).1 (by have := (hf k).2; rwa [sub_zero] at this) n
  have hT : Filter.Tendsto (fun k => MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ (f k)) -
      MvPowerSeries.C (l : K) * f k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n (frobVar l (MvPowerSeries.map σ g) -
        MvPowerSeries.C (l : K) * g))) := by
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    refine Filter.Tendsto.sub ?_ ((hlim n).const_mul _)
    by_cases hd : ∀ i, l ∣ n i
    · obtain ⟨m, rfl⟩ : ∃ m : τ →₀ ℕ, n = l • m := by
        refine ⟨n.mapRange (· / l) (by simp), ?_⟩
        ext i
        simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
        exact (Nat.mul_div_cancel' (hd i)).symm
      simp only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hp0, MvPowerSeries.coeff_map]
      exact (hcont.tendsto _).comp (hlim m)
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      simp only [Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hp0 _ hi]
      exact tendsto_const_nhds
  exact le_of_tendsto hT.norm (Filter.Eventually.of_forall hk)

end Formalism.L2.Th1.D
