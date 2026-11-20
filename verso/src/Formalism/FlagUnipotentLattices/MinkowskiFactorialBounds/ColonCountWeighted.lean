import Formalism.FlagUnipotentLattices.IdealCountLeW
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
import Lemmata.GeneralBFactSecondMore.Imports

open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
Introduce `K U _ _ _ _ h O g L₀ L₀' ι' hg hsg hg0 hO hι hiso`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `l' hl' x hx hxl`. Take `⟨l, hl, hxl⟩` from `hxl`. Take `⟨t, ht, hiso'⟩` from `hiso l' hl' x hx.2`.

Establish `hx' : x = ι' x - g • l` using `by rw [← hxl]; abel`. Establish `h1 : h (ι' l') x = h (ι' l') (ι' x) - g * h (ι' l') l` using `by conv_lhs => rw [hx']`. Rewrite using `[map_sub, LinearMap.map_smulₛₗ, starRingEnd_apply, hsg, smul_eq_mul]`. Establish `key : h (l' - ι' l') x = g * (h (ι' l') l - t)`. Rewrite using `[map_sub, LinearMap.sub_apply, h1]`.

Take the linear combination `(-1 : K) * hiso'`. Rewrite using `[map_smul, LinearMap.smul_apply, key, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]`. Conclude with `O.sub_mem (hO _ (hι l' hl') _ hl) ht`. Introduce and unpack `l' hl' ⟨l, hl, e⟩`. Establish `h2 : l' - ι' l' = g • (-l)` using `by rw [smul_neg, ← e]; abel`.

Rewrite using `[h2, smul_smul, inv_mul_cancel₀ hg0, one_smul]`. Conclude with `L₀.neg_mem hl`.
-/
theorem embedding_dual_compatible : IotaDual := by
  intro K U _ _ _ _ h O g L₀ L₀' ι' hg hsg hg0 hO hι hiso
  refine ⟨?_, ?_⟩
  · intro l' hl' x hx hxl
    obtain ⟨l, hl, hxl⟩ := hxl
    obtain ⟨t, ht, hiso'⟩ := hiso l' hl' x hx.2
    have hx' : x = ι' x - g • l := by rw [← hxl]; abel
    have h1 : h (ι' l') x = h (ι' l') (ι' x) - g * h (ι' l') l := by
      conv_lhs => rw [hx']
      rw [map_sub, LinearMap.map_smulₛₗ, starRingEnd_apply, hsg, smul_eq_mul]
    have key : h (l' - ι' l') x = g * (h (ι' l') l - t) := by
      rw [map_sub, LinearMap.sub_apply, h1]
      linear_combination (-1 : K) * hiso'
    rw [map_smul, LinearMap.smul_apply, key, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
    exact O.sub_mem (hO _ (hι l' hl') _ hl) ht
  · rintro l' hl' ⟨l, hl, e⟩
    have h2 : l' - ι' l' = g • (-l) := by rw [smul_neg, ← e]; abel
    rw [h2, smul_smul, inv_mul_cancel₀ hg0, one_smul]
    exact L₀.neg_mem hl

/- English proof (translation)
Introduce `K U _ _ _ g L₀ ι₁ ι₂ l' hg0 hmem`. Use `⟨-(g⁻¹ • (l' - ι₁ l') - g⁻¹ • (l' - ι₂ l')), L₀.neg_mem hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hg0, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem embedding_determined_by_restriction : IotaDetermined := by
  intro K U _ _ _ g L₀ ι₁ ι₂ l' hg0 hmem
  refine ⟨-(g⁻¹ • (l' - ι₁ l') - g⁻¹ • (l' - ι₂ l')), L₀.neg_mem hmem, ?_⟩
  rw [← smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hg0, one_smul]
  abel

/- English proof (translation)
Introduce `E _ _ U _ _ Lam₁ y c aa aa' hc h1 h2`. Use extensionality with `x`. Rewrite using `[FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_coeIdeal]`. Rewrite using `[← h1 x]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y', hy', rfl⟩`. Rewrite `hy'` using `[FractionalIdeal.mem_coeIdeal, ← h2 y']`. Rewrite `hy'` using `[smul_smul, mul_comm]`. Then use the resulting hypothesis. Introduce `hx`. Use `⟨c⁻¹ * x, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[FractionalIdeal.mem_coeIdeal, ← h2, smul_smul, mul_assoc, mul_comm x c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`. Conclude with `hx`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul]`.
-/
theorem colon_ideal_scaling : ColonScale := by
  intro E _ _ U _ _ Lam₁ y c aa aa' hc h1 h2
  ext x
  rw [FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_coeIdeal]
  rw [← h1 x]
  constructor
  · rintro ⟨y', hy', rfl⟩
    rw [FractionalIdeal.mem_coeIdeal, ← h2 y'] at hy'
    rwa [smul_smul, mul_comm] at hy'
  · intro hx
    refine ⟨c⁻¹ * x, ?_, ?_⟩
    · rw [FractionalIdeal.mem_coeIdeal, ← h2, smul_smul, mul_assoc, mul_comm x c, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
      exact hx
    · rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/- English proof (translation)
Introduce `C C' r f b hb`. Establish `hb0 : 0 < b` using `by linarith`. Rewrite using `[← pow_mul]`. Establish `e : ∀ N : ℕ, b ^ N = Real.exp ((N : ℝ) * Real.log b)`. Introduce `N`.

Rewrite using `[Real.exp_nat_mul, Real.exp_log hb0]`. Rewrite using `[e, Real.exp_le_exp]`. Apply `mul_le_mul_of_nonneg_right _ (Real.log_nonneg hb)` to reduce the goal to its premises. Establish `hr : r ^ 4 ≤ (2 * r + 2) ^ 4` using `Nat.pow_le_pow_left (by omega) 4`. Establish `: C * (2 * r + 2) ^ 2 * f * (C' * r ^ 4) ≤ C * C' * (2 * r + 2) ^ 6 * f`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions.
-/
theorem loss_bound_holds : HLoss := by
  intro C C' r f b hb
  have hb0 : 0 < b := by linarith
  rw [← pow_mul]
  have e : ∀ N : ℕ, b ^ N = Real.exp ((N : ℝ) * Real.log b) := by
    intro N; rw [Real.exp_nat_mul, Real.exp_log hb0]
  rw [e, Real.exp_le_exp]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hb)
  have hr : r ^ 4 ≤ (2 * r + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have : C * (2 * r + 2) ^ 2 * f * (C' * r ^ 4) ≤ C * C' * (2 * r + 2) ^ 6 * f := by
    calc C * (2 * r + 2) ^ 2 * f * (C' * r ^ 4) ≤ C * (2 * r + 2) ^ 2 * f * (C' * (2 * r + 2) ^ 4) := by gcongr
      _ = C * C' * (2 * r + 2) ^ 6 * f := by ring
  exact_mod_cast this

/- English proof (translation)
Introduce `C C₂ r Db Del NT Ncc hr hDel hDD hNT hN0 hN`. Establish `hDb : 1 ≤ Db` using `le_trans hDel hDD`. Use `set X := Db * NT with hX`. Establish `hX1 : 1 ≤ X` using `by nlinarith`. Establish `hY : Db * Del * NT ≤ X ^ 2`.

Establish `: Db * Del * NT ≤ Db * Db * NT` using `by gcongr`. Use polynomial arithmetic with `[mul_nonneg (by positivity : 0 ≤ Db * Db * NT) (by linarith : 0 ≤ NT - 1)]`. Establish `hY0 : 0 ≤ Db * Del * NT` using `by positivity`. Establish `hN' : Ncc ≤ X ^ (2 * (C * r))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hG : Del * NT ≤ X` using `by rw [hX]; gcongr`. Establish `hG0 : 0 ≤ Del * NT` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ X ^ ((36 * C + 4 * C * C₂ + 6) * r ^ 3) := by`. Apply `pow_le_pow_right₀ hX1` to reduce the goal to its premises. Establish `h1 : (2 * r + 1) ^ 2 ≤ 9 * r ^ 2` using `by nlinarith`. Establish `h2 : 2 * (2 * r + 1) ≤ 6 * r ^ 3` using `by nlinarith [Nat.pow_le_pow_left hr 3, Nat.pow_le_pow_left hr 2, mul_le_mul hr hr]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem cost_bound : CostBound := by
  intro C C₂ r Db Del NT Ncc hr hDel hDD hNT hN0 hN
  have hDb : 1 ≤ Db := le_trans hDel hDD
  set X := Db * NT with hX
  have hX1 : 1 ≤ X := by nlinarith
  have hY : Db * Del * NT ≤ X ^ 2 := by
    have : Db * Del * NT ≤ Db * Db * NT := by gcongr
    nlinarith [mul_nonneg (by positivity : 0 ≤ Db * Db * NT) (by linarith : 0 ≤ NT - 1)]
  have hY0 : 0 ≤ Db * Del * NT := by positivity
  have hN' : Ncc ≤ X ^ (2 * (C * r)) := by
    calc Ncc ≤ (Db * Del * NT) ^ (C * r) := hN
      _ ≤ (X ^ 2) ^ (C * r) := by gcongr
      _ = X ^ (2 * (C * r)) := by rw [← pow_mul]
  have hG : Del * NT ≤ X := by rw [hX]; gcongr
  have hG0 : 0 ≤ Del * NT := by positivity
  calc Ncc ^ (2 * (2 * r + 1) ^ 2) * (Del * NT) ^ (2 * (2 * r + 1)) * (Ncc ^ 2) ^ (C₂ * r ^ 2)
      ≤ (X ^ (2 * (C * r))) ^ (2 * (2 * r + 1) ^ 2) * X ^ (2 * (2 * r + 1)) *
          ((X ^ (2 * (C * r))) ^ 2) ^ (C₂ * r ^ 2) := by gcongr
    _ = X ^ (2 * (C * r) * (2 * (2 * r + 1) ^ 2) + 2 * (2 * r + 1) + 2 * (C * r) * 2 * (C₂ * r ^ 2)) := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ X ^ ((36 * C + 4 * C * C₂ + 6) * r ^ 3) := by
        apply pow_le_pow_right₀ hX1
        have h1 : (2 * r + 1) ^ 2 ≤ 9 * r ^ 2 := by nlinarith
        have h2 : 2 * (2 * r + 1) ≤ 6 * r ^ 3 := by nlinarith [Nat.pow_le_pow_left hr 3, Nat.pow_le_pow_left hr 2, mul_le_mul hr hr]
        calc 2 * (C * r) * (2 * (2 * r + 1) ^ 2) + 2 * (2 * r + 1) + 2 * (C * r) * 2 * (C₂ * r ^ 2)
            ≤ 2 * (C * r) * (2 * (9 * r ^ 2)) + 6 * r ^ 3 + 2 * (C * r) * 2 * (C₂ * r ^ 2) := by gcongr
          _ = (36 * C + 4 * C * C₂ + 6) * r ^ 3 := by ring

/- English proof (translation)
Introduce `E _ _ L _ _ Lam₁ y`. Use `set aa : Ideal (𝓞 E) := Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) with haa`. Establish `hdvd : Ideal.absNorm aa ∣ Lam₁.toAddSubgroup.index`. Establish `e1 : Ideal.absNorm aa = (Submodule.toAddSubgroup aa).index`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Both sides reduce to the same expression. Establish `e2 : Submodule.toAddSubgroup aa = Lam₁.toAddSubgroup.comap (LinearMap.toSpanSingleton (𝓞 E) L y).toAddMonoidHom`. Use extensionality with `a`. Both sides reduce to the same expression. Rewrite using `[e1, e2, AddSubgroup.index_comap]`.

Conclude with `AddSubgroup.relIndex_dvd_index_of_normal _ _`. Use `⟨hdvd, fun h0 => ⟨?_, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd⟩⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (Ideal.absNorm aa) with h | h` into its components or cases. Rewrite `hdvd` using `[h]`. Conclude with `absurd (Nat.eq_zero_of_zero_dvd hdvd) h0`.

Conclude with `h`.
-/
theorem colon_ideal_norm : ColonNorm := by
  intro E _ _ L _ _ Lam₁ y
  set aa : Ideal (𝓞 E) := Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) with haa
  have hdvd : Ideal.absNorm aa ∣ Lam₁.toAddSubgroup.index := by
    have e1 : Ideal.absNorm aa = (Submodule.toAddSubgroup aa).index := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have e2 : Submodule.toAddSubgroup aa =
        Lam₁.toAddSubgroup.comap (LinearMap.toSpanSingleton (𝓞 E) L y).toAddMonoidHom := by
      ext a; rfl
    rw [e1, e2, AddSubgroup.index_comap]
    exact AddSubgroup.relIndex_dvd_index_of_normal _ _
  refine ⟨hdvd, fun h0 => ⟨?_, Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd⟩⟩
  rcases Nat.eq_zero_or_pos (Ideal.absNorm aa) with h | h
  · rw [h] at hdvd; exact absurd (Nat.eq_zero_of_zero_dvd hdvd) h0
  · exact h

/- English proof (translation)
Introduce `R Q _ _ _ N e₁ e₂ s t hs ht`. Use `choose t' ht' using fun i => Submodule.Quotient.mk_surjective N (t i)`. Use `⟨Fin.append s t', ?_⟩` and prove the remaining obligations. Establish `hsub1 : N ≤ Submodule.span R (Set.range (Fin.append s t'))`. Rewrite using `[← hs]`.

Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩; exact ⟨Fin.castAdd e₂ i, by simp⟩`. Establish `hsub2 : Submodule.span R (Set.range t') ≤ Submodule.span R (Set.range (Fin.append s t'))`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩; exact ⟨Fin.natAdd e₁ i, by simp⟩`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : (Submodule.Quotient.mk x : Q ⧸ N) ∈ Submodule.span R (Set.range t)` using `by rw [ht]; trivial`. Establish `hmap : Submodule.span R (Set.range t) = (Submodule.span R (Set.range t')).map N.mkQ`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`.

Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨i, ht' i⟩`.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨i, (ht' i).symm⟩`. Rewrite `hx` using `[hmap]`. Take `⟨w, hw, hwx⟩` from `hx`. Establish `: x - w ∈ N`.

Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `hwx.symm`. Establish `hx2 : x = (x - w) + w` using `by abel`. Rewrite using `[hx2]`. Conclude with `Submodule.add_mem _ (hsub1 this) (hsub2 hw)`.
-/
theorem extension_generator_count : ExtGen := by
  intro R Q _ _ _ N e₁ e₂ s t hs ht
  choose t' ht' using fun i => Submodule.Quotient.mk_surjective N (t i)
  refine ⟨Fin.append s t', ?_⟩
  have hsub1 : N ≤ Submodule.span R (Set.range (Fin.append s t')) := by
    rw [← hs]; apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩; exact ⟨Fin.castAdd e₂ i, by simp⟩
  have hsub2 : Submodule.span R (Set.range t') ≤ Submodule.span R (Set.range (Fin.append s t')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩; exact ⟨Fin.natAdd e₁ i, by simp⟩
  rw [eq_top_iff]
  intro x _
  have hx : (Submodule.Quotient.mk x : Q ⧸ N) ∈ Submodule.span R (Set.range t) := by rw [ht]; trivial
  have hmap : Submodule.span R (Set.range t) = (Submodule.span R (Set.range t')).map N.mkQ := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, ht' i⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, (ht' i).symm⟩
  rw [hmap] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  have : x - w ∈ N := by
    rw [← Submodule.Quotient.eq]; exact hwx.symm
  have hx2 : x = (x - w) + w := by abel
  rw [hx2]
  exact Submodule.add_mem _ (hsub1 this) (hsub2 hw)

/- English proof (translation)
Introduce `R Q _ _ _ _ _ e s hs N`. Conclude with `Formalism.SLP.P.exists_family_span_eq_of_le e s N (by rw [hs]; exact le_top)`.
-/
theorem submodule_generator_count : SubGen := by
  intro R Q _ _ _ _ _ e s hs N
  exact Formalism.SLP.P.exists_family_span_eq_of_le e s N (by rw [hs]; exact le_top)

namespace DualLatticeIndexBis

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p k hp hk`. Introduce `hodd`. Establish `hp3 : 3 ≤ p`.

Establish `h2 : p ≠ 2`. Introduce and unpack `rfl`. Establish `: Even (2 ^ k)` using `(Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)`. Conclude with `(Nat.not_odd_iff_even.mpr this) hodd`. Use `hp.two_le` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.totient_prime_pow hp hk]`. Take `⟨k, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Take `⟨q, rfl⟩ : ∃ q, p = q + 3` from `⟨p - 3, by omega⟩`.

Establish `h1 : 1 ≤ (q + 3) ^ k` using `Nat.one_le_pow _ _ (by omega)`. Establish `h2 : (q + 3) ^ k ≤ ((q + 3) ^ k) ^ 2` using `by nlinarith`. Establish `h3 : q + 3 ≤ (q + 3 - 1) ^ 2`. Establish `: q + 3 - 1 = q + 2` using `by omega`. Rewrite using `[this]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `one => intro _`.

Simplify using the standard rewrite rules. Consider the case `coprime a b ha hb hab iha ihb`. Introduce `hodd`. Rewrite `hodd` using `[Nat.odd_mul]`. Rewrite using `[Nat.totient_mul hab, mul_pow]`.

Conclude with `Nat.mul_le_mul (iha hodd.1) (ihb hodd.2)`.
-/
lemma totient_odd : ∀ n : ℕ, Odd n → n ≤ Nat.totient n ^ 2 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd
    have hp3 : 3 ≤ p := by
      have h2 : p ≠ 2 := by
        rintro rfl
        have : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩)
        exact (Nat.not_odd_iff_even.mpr this) hodd
      have := hp.two_le
      omega
    rw [Nat.totient_prime_pow hp hk]
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    have h1 : 1 ≤ (q + 3) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : (q + 3) ^ k ≤ ((q + 3) ^ k) ^ 2 := by nlinarith
    have h3 : q + 3 ≤ (q + 3 - 1) ^ 2 := by
      have : q + 3 - 1 = q + 2 := by omega
      rw [this]; nlinarith
    calc (q + 3) ^ (k + 1) = (q + 3) ^ k * (q + 3) := pow_succ _ _
      _ ≤ ((q + 3) ^ k) ^ 2 * (q + 3 - 1) ^ 2 := Nat.mul_le_mul h2 h3
      _ = ((q + 3) ^ k * (q + 3 - 1)) ^ 2 := by ring
  | zero => intro _; simp
  | one => intro _; simp
  | coprime a b ha hb hab iha ihb =>
    intro hodd
    rw [Nat.odd_mul] at hodd
    rw [Nat.totient_mul hab, mul_pow]
    exact Nat.mul_le_mul (iha hodd.1) (ihb hodd.2)

end DualLatticeIndexBis

/- English proof (translation)
Introduce `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Take `⟨k, m, hm, rfl⟩` from `Nat.exists_eq_two_pow_mul_odd hn.ne'`. Establish `hcop : Nat.Coprime (2 ^ k) m` using `Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)`.

Establish `h1` using `DualLatticeIndexBis.totient_odd m hm`. Rewrite using `[Nat.totient_mul hcop, mul_pow]`. Establish `h2 : 2 ^ k ≤ 2 * Nat.totient (2 ^ k) ^ 2`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Simplify using the standard rewrite rules.

Rewrite using `[Nat.totient_prime_pow Nat.prime_two hk]`. Take `⟨k, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `h1 : 1 ≤ 2 ^ k` using `Nat.one_le_pow _ _ (by omega)`. Rewrite using `[pow_succ]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem totient_bound_alt : TotientBound := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h1 := DualLatticeIndexBis.totient_odd m hm
  rw [Nat.totient_mul hcop, mul_pow]
  have h2 : 2 ^ k ≤ 2 * Nat.totient (2 ^ k) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ]
      nlinarith
  calc 2 ^ k * m ≤ (2 * Nat.totient (2 ^ k) ^ 2) * Nat.totient m ^ 2 := Nat.mul_le_mul h2 h1
    _ = 2 * (Nat.totient (2 ^ k) ^ 2 * Nat.totient m ^ 2) := by ring

/- English proof (translation)
Introduce `hT E _ _ f hf`. Take `⟨ζ, hζ⟩` from `IsCyclic.exists_generator (α := NumberField.Units.torsion E)`. Establish `hord : orderOf ζ = Nat.card (NumberField.Units.torsion E)` using `orderOf_eq_card_of_forall_mem_zpowers hζ`. Use `set w := Nat.card (NumberField.Units.torsion E) with hw`. Establish `hwpos : 0 < w` using `Nat.card_pos`.

Set `φ : NumberField.Units.torsion E →* E` to `((algebraMap (𝓞 E) E : 𝓞 E →* E).comp (Units.coeHom (𝓞 E))).comp (NumberField.Units.torsion E).subtype`. Establish `hφ : Function.Injective φ`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `RingOfIntegers.coe_injective hab`. Establish `hprim : IsPrimitiveRoot (φ ζ) w`. Rewrite using `[← hord, ← orderOf_injective φ hφ ζ]`. Conclude with `IsPrimitiveRoot.orderOf _`. Establish `h1 : Nat.totient w ≤ 2 * f`.

Rewrite using `[← hf, ← Polynomial.natDegree_cyclotomic w ℚ, Polynomial.cyclotomic_eq_minpoly_rat hprim hwpos]`. Conclude with `minpoly.natDegree_le _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem torsion_bound_of_totient : TorsionBoundAsm := by
  intro hT E _ _ f hf
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  have hord : orderOf ζ = Nat.card (NumberField.Units.torsion E) :=
    orderOf_eq_card_of_forall_mem_zpowers hζ
  set w := Nat.card (NumberField.Units.torsion E) with hw
  have hwpos : 0 < w := Nat.card_pos
  let φ : NumberField.Units.torsion E →* E :=
    ((algebraMap (𝓞 E) E : 𝓞 E →* E).comp (Units.coeHom (𝓞 E))).comp
      (NumberField.Units.torsion E).subtype
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective hab
  have hprim : IsPrimitiveRoot (φ ζ) w := by
    rw [← hord, ← orderOf_injective φ hφ ζ]
    exact IsPrimitiveRoot.orderOf _
  have h1 : Nat.totient w ≤ 2 * f := by
    rw [← hf, ← Polynomial.natDegree_cyclotomic w ℚ, Polynomial.cyclotomic_eq_minpoly_rat hprim hwpos]
    exact minpoly.natDegree_le _
  calc w ≤ 2 * Nat.totient w ^ 2 := hT w
    _ ≤ 2 * (2 * f) ^ 2 := by gcongr
    _ = 8 * f ^ 2 := by ring

/- English proof (translation)
The claim follows from `torsion_bound_of_totient totient_bound_alt`.
-/
theorem torsion_bound_alt : TorsionBound := torsion_bound_of_totient totient_bound_alt

namespace DualLatticeIndexBis

/- English proof (translation)
Rewrite using `[(Nat.perm_primeFactorsList_mul (by omega) (by omega)).length_eq, List.length_append]`. Establish `: 0 < (Nat.primeFactorsList q).length`. Rewrite using `[List.length_pos_iff, Nat.primeFactorsList_ne_nil]`. Conclude with `hq`. Use linear arithmetic over natural numbers and integers.
-/
lemma omega_mul_ge {q n' : ℕ} (hq : 1 < q) (hn' : 1 ≤ n') :
    1 + (Nat.primeFactorsList n').length ≤ (Nat.primeFactorsList (q * n')).length := by
  rw [(Nat.perm_primeFactorsList_mul (by omega) (by omega)).length_eq, List.length_append]
  have : 0 < (Nat.primeFactorsList q).length := by
    rw [List.length_pos_iff, Nat.primeFactorsList_ne_nil]
    exact hq
  omega

/- English proof (translation)
Establish `hcard : Ideal.absNorm I = Nat.card (𝓞 E ⧸ I)`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hfin : Finite (𝓞 E ⧸ I)` using `Nat.finite_of_card_ne_zero (hcard ▸ h0)`. Establish `: Fact p.Prime` using `⟨hp⟩`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p (hcard ▸ hI)`.

Establish `hne : I ⊔ Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊤`. Introduce `htop`. Establish `h1 : (1 : 𝓞 E) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 E)}` using `by rw [htop]; trivial`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hb`.

Establish `hpx : p • x = 0` using `hx ▸ addOrderOf_nsmul_eq_zero x`. Establish `h2 : (Ideal.Quotient.mk I (c * (p : 𝓞 E))) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk I), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]`. Establish `h3 : x = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← h2, map_mul, map_natCast, nsmul_eq_mul, mul_assoc]`. Use `_ = 0 := by rw [hpx, mul_zero]`. Rewrite `hx` using `[h3, addOrderOf_zero]`. Conclude with `hp.one_lt.ne hx`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Conclude with `⟨P, hP, le_sup_left.trans hle, hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))⟩`.
-/
lemma exists_max_above (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hI : p ∣ Ideal.absNorm I) (h0 : Ideal.absNorm I ≠ 0) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ I ≤ P ∧ ((p : ℕ) : 𝓞 E) ∈ P := by
  have hcard : Ideal.absNorm I = Nat.card (𝓞 E ⧸ I) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ h0)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p (hcard ▸ hI)
  have hne : I ⊔ Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 E) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 E)} := by rw [htop]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have hpx : p • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
    have h2 : (Ideal.Quotient.mk I (c * (p : 𝓞 E))) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have h3 : x = 0 := by
      calc x = 1 * x := (one_mul x).symm
        _ = Ideal.Quotient.mk I c * (p • x) := by
            rw [← h2, map_mul, map_natCast, nsmul_eq_mul, mul_assoc]
        _ = 0 := by rw [hpx, mul_zero]
    rw [h3, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨P, hP, le_sup_left.trans hle,
    hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))⟩

end DualLatticeIndexBis

/- English proof (translation)
Introduce `E _ _ n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn`. Use `set N := Module.finrank ℚ E with hN`.

Establish `hNpos : 0 < N` using `Module.finrank_pos`. Break down `Nat.eq_or_lt_of_le hn with h1 | h1` into its components or cases. Establish `: {I : Ideal (𝓞 E) | Ideal.absNorm I = 1} = {⊤}`. Use extensionality with `I`. Simplify using `[Ideal.absNorm_eq_one_iff]`.

Rewrite using `[← h1, this]`. Simplify using the standard rewrite rules. Use `set p := n.minFac with hpdef`. Establish `hp : p.Prime` using `Nat.minFac_prime (by omega)`. Establish `hpn : p ∣ n` using `Nat.minFac_dvd n`.

Take `⟨Ps, hPs, hPmem⟩` from `Formalism.SLP.P.CountO.primes_card E p hp`. Set `G` to `Ps.filter (fun P => P.IsMaximal ∧ ((p : ℕ) : 𝓞 E) ∈ P)`. Set `t : Ideal (𝓞 E) → Set (Ideal (𝓞 E))` to `fun P => (fun I' => P * I') '' {I' | Ideal.absNorm P * Ideal.absNorm I' = n}`. Establish `hsub : {I : Ideal (𝓞 E) | Ideal.absNorm I = n} ⊆ ⋃ P ∈ G, t P`. Introduce `I hI`.

Establish `hI' : Ideal.absNorm I = n` using `hI`. Take `⟨P, hP, hle, hpP⟩` from `DualLatticeIndexBis.exists_max_above E I p hp (hI' ▸ hpn) (by omega)`. Take `⟨I', rfl⟩` from `Ideal.dvd_iff_le.mpr hle`. Simplify using `only [Set.mem_iUnion]`. Use `⟨P, Finset.mem_filter.mpr ⟨hPmem P hP hpP, hP, hpP⟩, I', ?_, rfl⟩` and prove the remaining obligations.

Rewrite `hI'` using `[map_mul]`. Conclude with `hI'`. Establish `hOm : 1 ≤ (Nat.primeFactorsList n).length`. Use `DualLatticeIndexBis.omega_mul_ge (q := n) (n' := 1) h1 le_rfl` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Use linear arithmetic over natural numbers and integers. Establish `ht : ∀ P ∈ G, (t P).Finite ∧ (t P).ncard ≤ N ^ ((Nat.primeFactorsList n).length - 1)`. Introduce `P hP`. Take `⟨_, hPm, hpP⟩` from `Finset.mem_filter.mp hP`. Use `set q := Ideal.absNorm P with hq`.

Establish `hq0 : q ≠ 0`. Introduce `h`. Rewrite `h` using `[hq, Ideal.absNorm_eq_zero_iff]`. Rewrite `hpP` using `[h, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hpP)`.

Establish `hq1 : q ≠ 1`. Introduce `h`. Rewrite `h` using `[hq, Ideal.absNorm_eq_one_iff]`. Conclude with `hPm.ne_top h`. Distinguish the cases in `hqn : q ∣ n`.

Take `⟨n', hn'⟩` from `hqn`. Establish `hn'1 : 1 ≤ n'`. Break down `Nat.eq_zero_or_pos n' with h | h` into its components or cases. Rewrite `hn'` using `[h, mul_zero]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hlt : n' < n`. Establish `hq2 : 2 ≤ q` using `by omega`. Rewrite using `[hn']`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hset : {I' : Ideal (𝓞 E) | q * Ideal.absNorm I' = n} = {I' : Ideal (𝓞 E) | Ideal.absNorm I' = n'}`. Use extensionality with `I'`. Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[hn']`. Conclude with `Nat.mul_right_inj hq0`.

Take `⟨hf, hc⟩` from `ih n' hlt hn'1`. Establish `hge` using `DualLatticeIndexBis.omega_mul_ge (q := q) (n' := n') (by omega) hn'1`. Rewrite `hge` using `[← hn']`. Simplify using `only [t]`. Rewrite using `[hset]`.

Use `⟨hf.image _, (Set.ncard_image_le hf).trans (hc.trans ?_)⟩` and prove the remaining obligations. Conclude with `Nat.pow_le_pow_right hNpos (by omega)`. Establish `hset : {I' : Ideal (𝓞 E) | q * Ideal.absNorm I' = n} = ∅`. Use extensionality with `I'`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`.

Introduce `h`. Conclude with `hqn ⟨_, h.symm⟩`. Simplify using `only [t]`. Rewrite using `[hset]`. Simplify using the standard rewrite rules.

Take `⟨hfin, hcard⟩` from `Formalism.SLP.P.CountO.ncard_biUnion_le G t (fun P hP => (ht P hP).1)`. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_succ']`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ideal_count_eq : IdealCountEq := by
  intro E _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  classical
  set N := Module.finrank ℚ E with hN
  have hNpos : 0 < N := Module.finrank_pos
  rcases Nat.eq_or_lt_of_le hn with h1 | h1
  · have : {I : Ideal (𝓞 E) | Ideal.absNorm I = 1} = {⊤} := by
      ext I; simp [Ideal.absNorm_eq_one_iff]
    rw [← h1, this]; simp
  · set p := n.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    obtain ⟨Ps, hPs, hPmem⟩ := Formalism.SLP.P.CountO.primes_card E p hp
    let G := Ps.filter (fun P => P.IsMaximal ∧ ((p : ℕ) : 𝓞 E) ∈ P)
    let t : Ideal (𝓞 E) → Set (Ideal (𝓞 E)) := fun P =>
      (fun I' => P * I') '' {I' | Ideal.absNorm P * Ideal.absNorm I' = n}
    have hsub : {I : Ideal (𝓞 E) | Ideal.absNorm I = n} ⊆ ⋃ P ∈ G, t P := by
      intro I hI
      have hI' : Ideal.absNorm I = n := hI
      obtain ⟨P, hP, hle, hpP⟩ := DualLatticeIndexBis.exists_max_above E I p hp (hI' ▸ hpn) (by omega)
      obtain ⟨I', rfl⟩ := Ideal.dvd_iff_le.mpr hle
      simp only [Set.mem_iUnion]
      refine ⟨P, Finset.mem_filter.mpr ⟨hPmem P hP hpP, hP, hpP⟩, I', ?_, rfl⟩
      rw [map_mul] at hI'
      exact hI'
    have hOm : 1 ≤ (Nat.primeFactorsList n).length := by
      have := DualLatticeIndexBis.omega_mul_ge (q := n) (n' := 1) h1 le_rfl
      rw [mul_one] at this
      omega
    have ht : ∀ P ∈ G, (t P).Finite ∧ (t P).ncard ≤ N ^ ((Nat.primeFactorsList n).length - 1) := by
      intro P hP
      obtain ⟨_, hPm, hpP⟩ := Finset.mem_filter.mp hP
      set q := Ideal.absNorm P with hq
      have hq0 : q ≠ 0 := by
        intro h
        rw [hq, Ideal.absNorm_eq_zero_iff] at h
        rw [h, Ideal.mem_bot] at hpP
        exact hp.ne_zero (by exact_mod_cast hpP)
      have hq1 : q ≠ 1 := by
        intro h
        rw [hq, Ideal.absNorm_eq_one_iff] at h
        exact hPm.ne_top h
      by_cases hqn : q ∣ n
      · obtain ⟨n', hn'⟩ := hqn
        have hn'1 : 1 ≤ n' := by
          rcases Nat.eq_zero_or_pos n' with h | h
          · rw [h, mul_zero] at hn'; omega
          · exact h
        have hlt : n' < n := by
          have hq2 : 2 ≤ q := by omega
          rw [hn']; nlinarith
        have hset : {I' : Ideal (𝓞 E) | q * Ideal.absNorm I' = n} =
            {I' : Ideal (𝓞 E) | Ideal.absNorm I' = n'} := by
          ext I'
          simp only [Set.mem_ofPred_eq]
          rw [hn']
          exact Nat.mul_right_inj hq0
        obtain ⟨hf, hc⟩ := ih n' hlt hn'1
        have hge := DualLatticeIndexBis.omega_mul_ge (q := q) (n' := n') (by omega) hn'1
        rw [← hn'] at hge
        simp only [t]
        rw [hset]
        refine ⟨hf.image _, (Set.ncard_image_le hf).trans (hc.trans ?_)⟩
        exact Nat.pow_le_pow_right hNpos (by omega)
      · have hset : {I' : Ideal (𝓞 E) | q * Ideal.absNorm I' = n} = ∅ := by
          ext I'
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          exact hqn ⟨_, h.symm⟩
        simp only [t]
        rw [hset]
        simp
    obtain ⟨hfin, hcard⟩ := Formalism.SLP.P.CountO.ncard_biUnion_le G t (fun P hP => (ht P hP).1)
    refine ⟨hfin.subset hsub, ?_⟩
    calc {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤ (⋃ P ∈ G, t P).ncard :=
          Set.ncard_le_ncard hsub hfin
      _ ≤ ∑ P ∈ G, (t P).ncard := hcard
      _ ≤ ∑ _P ∈ G, N ^ ((Nat.primeFactorsList n).length - 1) :=
          Finset.sum_le_sum (fun P hP => (ht P hP).2)
      _ = G.card * N ^ ((Nat.primeFactorsList n).length - 1) := by simp
      _ ≤ N * N ^ ((Nat.primeFactorsList n).length - 1) :=
          Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hPs)
      _ = N ^ (Nat.primeFactorsList n).length := by
          rw [← pow_succ']; congr 1; omega

namespace DualLatticeIndexBis

/- English proof (translation)
Establish `hset : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y} = ⋃ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n}`. Use extensionality with `I`. Simplify using the standard rewrite rules. Take `⟨hfin, hcard⟩` from `Formalism.SLP.P.CountO.ncard_biUnion_le (Finset.Icc 1 y) (fun n => {I : Ideal (𝓞 E) | Ideal.absNorm I = n}) (fun n hn => (h n (Finset.mem_Icc.mp hn).1).1)`. Rewrite using `[hset]`.

Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hlog : 0 ≤ Real.logb 2 N` using `Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)`. Break down `Nat.eq_zero_or_pos y with rfl | hy` into its components or cases. Simplify using `only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one]`. Simplify using `only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.ncard_empty, Nat.cast_zero]`.

Conclude with `Real.rpow_nonneg le_rfl _`. Establish `hy' : (0 : ℝ) < y` using `by exact_mod_cast hy`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hcard` after adjusting the coercions. Use `_ = ∑ n ∈ Finset.Icc 1 y, (({I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) := by push_cast; rfl`.

Use `_ ≤ ∑ _n ∈ Finset.Icc 1 y, (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `n hn`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.mp hn`. Establish `h3` using `(h n h1).2`.

Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hny : (n : ℝ) ≤ y` using `by exact_mod_cast h2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hy', Real.rpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = (y : ℝ) * (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by simp`. Use `_ = (y : ℝ) ^ (1 + ((k : ℝ) + Real.logb 2 N)) := by`. Rewrite using `[Real.rpow_add hy' 1, Real.rpow_one]`.
-/
lemma count_le (E : Type) [Field E] [NumberField E] (N k y : ℕ) (hN : 1 ≤ N)
    (hOm : Formalism.SLP.OmegaPow)
    (h : ∀ n, 1 ≤ n → {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.Finite ∧
      {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤ N ^ (Nat.primeFactorsList n).length * n ^ k) :
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + ((k : ℝ) + Real.logb 2 N)) := by
  classical
  have hset : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y} =
      ⋃ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
    ext I; simp
  obtain ⟨hfin, hcard⟩ := Formalism.SLP.P.CountO.ncard_biUnion_le (Finset.Icc 1 y)
    (fun n => {I : Ideal (𝓞 E) | Ideal.absNorm I = n})
    (fun n hn => (h n (Finset.mem_Icc.mp hn).1).1)
  rw [hset]
  refine ⟨hfin, ?_⟩
  have hlog : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one]
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.ncard_empty, Nat.cast_zero]
    exact Real.rpow_nonneg le_rfl _
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  calc (((⋃ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n}).ncard : ℕ) : ℝ)
      ≤ ((∑ n ∈ Finset.Icc 1 y, {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ∑ n ∈ Finset.Icc 1 y, (({I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ _n ∈ Finset.Icc 1 y, (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
        have h3 := (h n h1).2
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hny : (n : ℝ) ≤ y := by exact_mod_cast h2
        calc (({I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ)
            ≤ ((N ^ (Nat.primeFactorsList n).length * n ^ k : ℕ) : ℝ) := by exact_mod_cast h3
          _ = (N : ℝ) ^ (Nat.primeFactorsList n).length * (n : ℝ) ^ k := by push_cast; ring
          _ ≤ (n : ℝ) ^ Real.logb 2 N * (n : ℝ) ^ k := by
              gcongr; exact hOm N n hN h1
          _ ≤ (y : ℝ) ^ Real.logb 2 N * (y : ℝ) ^ k := by
              gcongr
          _ = (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by
              rw [Real.rpow_add hy', Real.rpow_natCast]; ring
    _ = (y : ℝ) * (y : ℝ) ^ ((k : ℝ) + Real.logb 2 N) := by simp
    _ = (y : ℝ) ^ (1 + ((k : ℝ) + Real.logb 2 N)) := by
        rw [Real.rpow_add hy' 1, Real.rpow_one]

end DualLatticeIndexBis

/- English proof (translation)
Introduce `E _ _ f y hf`. Establish `h` using `DualLatticeIndexBis.count_le E (Module.finrank ℚ E) 0 y Module.finrank_pos Formalism.SLP.Final.omegaPow (fun n hn => by simpa using ideal_count_eq E n hn)`. Rewrite `h` using `[hf]`. Use `⟨h.1, h.2.trans (le_of_eq ?_)⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[zero_add]`.
-/
theorem quotient_card : IdealCountLe := by
  intro E _ _ f y hf
  have h := DualLatticeIndexBis.count_le E (Module.finrank ℚ E) 0 y Module.finrank_pos Formalism.SLP.Final.omegaPow
    (fun n hn => by simpa using ideal_count_eq E n hn)
  rw [hf] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  push_cast
  rw [zero_add]

/- English proof (translation)
Introduce `hS hOm E _ _ f y hf`. Establish `h` using `DualLatticeIndexBis.count_le E (Module.finrank ℚ E) 1 y Module.finrank_pos hOm (fun n hn => by`. Establish `h1` using `hS E (𝓞 E) n hn`. Establish `hset : {N : Submodule (𝓞 E) (𝓞 E) | N.toAddSubgroup.index = n} = {I : Ideal (𝓞 E) | Ideal.absNorm I = n}`. Use extensionality with `I`.

Establish `e1 : Ideal.absNorm I = (Submodule.toAddSubgroup I).index`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Simplify using `only [Set.mem_ofPred_eq, e1]`. Rewrite `h1` using `[hset, Module.finrank_self]`.

Conclude with `h1)`. Rewrite `h` using `[hf]`. Use `⟨h.1, h.2.trans (le_of_eq ?_)⟩` and prove the remaining obligations. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem ideal_count_le_weighted_of_hyp : IdealCountLeW' := by
  intro hS hOm E _ _ f y hf
  have h := DualLatticeIndexBis.count_le E (Module.finrank ℚ E) 1 y Module.finrank_pos hOm
    (fun n hn => by
      have h1 := hS E (𝓞 E) n hn
      have hset : {N : Submodule (𝓞 E) (𝓞 E) | N.toAddSubgroup.index = n} =
          {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
        ext I
        have e1 : Ideal.absNorm I = (Submodule.toAddSubgroup I).index := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
        simp only [Set.mem_ofPred_eq, e1]
      rw [hset, Module.finrank_self] at h1
      exact h1)
  rw [hf] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  push_cast
  rfl

/- English proof (translation)
The claim follows from `ideal_count_le_weighted_of_hyp Formalism.SLP.Final.submoduleIndexCountO Formalism.SLP.Final.omegaPow`.
-/
theorem ideal_count_le_weighted : IdealCountLeW :=
  ideal_count_le_weighted_of_hyp Formalism.SLP.Final.submoduleIndexCountO Formalism.SLP.Final.omegaPow

namespace DualLatticeIndexBis

/- English proof (translation)
Use `set S := {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D} with hSdef`. Establish `hSf : Finite S` using `hS.to_subtype`. Establish `hpair : ∀ c : cSet E D, ∃ p : S × S, FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E) * ((p.2 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = ((p.1 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Introduce and unpack `⟨c, hc, aa, aa', h1, h2, h3, h4, h5⟩`. Conclude with `⟨(⟨aa, h1, h2⟩, ⟨aa', h3, h4⟩), h5⟩`.

Use `choose pr hpr using hpair`. Establish `hrep : ∀ p : S × S, ∃ c0 : E, ∀ c : cSet E D, pr c = p → ∃ u : NumberField.Units.torsion E, (c : E) = (((u : (𝓞 E)ˣ) : 𝓞 E) : E) * c0`. Introduce `p`. Distinguish the cases in `h : ∃ c : cSet E D, pr c = p`. Take `⟨c0, hc0⟩` from `h`.

Use `⟨c0, fun c hc => ?_⟩` and prove the remaining obligations. Establish `e1` using `hpr c`. Establish `e0` using `hpr c0`. Rewrite `e1` using `[hc]`. Rewrite `e0` using `[hc0]`.

Establish `hne : ((p.2 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0`. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero]`. Introduce `hb`. Use `p.2.2.1` as an intermediate fact. Rewrite `this` using `[hb, Ideal.absNorm_bot]`.

Use linear arithmetic over natural numbers and integers. Establish `e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c0 : E) = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)` using `mul_right_cancel₀ hne (e0.trans e1.symm)`. Take `⟨z, hz⟩` from `FractionalIdeal.spanSingleton_eq_spanSingleton.mp e2`. Establish `hz' : (c : E) = ((z : 𝓞 E) : E) * c0`. Rewrite using `[← hz, Units.smul_def, Algebra.smul_def]`.

Use `⟨⟨z, ?_⟩, hz'⟩` and prove the remaining obligations. Rewrite using `[NumberField.Units.mem_torsion]`. Introduce `w`. Establish `h1` using `c.2.1 w`. Establish `h0` using `c0.2.1 w`.

Rewrite `h1` using `[hz', map_mul, h0, mul_one]`. Conclude with `h1`. Conclude with `⟨1, fun c hc => absurd ⟨c, hc⟩ h⟩`. Use `choose rep hrep using hrep`. Use `choose u hu using fun c : cSet E D => hrep (pr c) c rfl`.

Establish `hinj : Function.Injective (fun c : cSet E D => (pr c, u c))`. Introduce `c c' h`. Simplify using `only [Prod.mk.injEq] at h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hu c, hu c', h.1, h.2]`.

Establish `hfin : Finite (cSet E D)` using `Finite.of_injective _ hinj`. Use `⟨Set.toFinite _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma cSet_count (E : Type) [Field E] [NumberField E] (D : ℕ)
    (hS : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.Finite) :
    (cSet E D).Finite ∧ (cSet E D).ncard ≤ Nat.card (NumberField.Units.torsion E) *
      {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard ^ 2 := by
  classical
  set S := {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D} with hSdef
  have hSf : Finite S := hS.to_subtype
  have hpair : ∀ c : cSet E D, ∃ p : S × S,
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E) *
        ((p.2 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      ((p.1 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rintro ⟨c, hc, aa, aa', h1, h2, h3, h4, h5⟩
    exact ⟨(⟨aa, h1, h2⟩, ⟨aa', h3, h4⟩), h5⟩
  choose pr hpr using hpair
  have hrep : ∀ p : S × S, ∃ c0 : E, ∀ c : cSet E D, pr c = p →
      ∃ u : NumberField.Units.torsion E, (c : E) = (((u : (𝓞 E)ˣ) : 𝓞 E) : E) * c0 := by
    intro p
    by_cases h : ∃ c : cSet E D, pr c = p
    · obtain ⟨c0, hc0⟩ := h
      refine ⟨c0, fun c hc => ?_⟩
      have e1 := hpr c
      have e0 := hpr c0
      rw [hc] at e1
      rw [hc0] at e0
      have hne : ((p.2 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
        rw [FractionalIdeal.coeIdeal_ne_zero]
        intro hb
        have := p.2.2.1
        rw [hb, Ideal.absNorm_bot] at this
        omega
      have e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c0 : E) =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E) :=
        mul_right_cancel₀ hne (e0.trans e1.symm)
      obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp e2
      have hz' : (c : E) = ((z : 𝓞 E) : E) * c0 := by
        rw [← hz, Units.smul_def, Algebra.smul_def]
      refine ⟨⟨z, ?_⟩, hz'⟩
      rw [NumberField.Units.mem_torsion]
      intro w
      have h1 := c.2.1 w
      have h0 := c0.2.1 w
      rw [hz', map_mul, h0, mul_one] at h1
      exact h1
    · exact ⟨1, fun c hc => absurd ⟨c, hc⟩ h⟩
  choose rep hrep using hrep
  choose u hu using fun c : cSet E D => hrep (pr c) c rfl
  have hinj : Function.Injective (fun c : cSet E D => (pr c, u c)) := by
    intro c c' h
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext
    rw [hu c, hu c', h.1, h.2]
  have hfin : Finite (cSet E D) := Finite.of_injective _ hinj
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  calc Nat.card (cSet E D) ≤ Nat.card ((S × S) × NumberField.Units.torsion E) :=
        Nat.card_le_card_of_injective _ hinj
    _ = _ := by rw [Nat.card_prod, Nat.card_prod]; ring

/- English proof (translation)
Take `⟨h1, h2⟩` from `cSet_count E D hS.1`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hT' : ((Nat.card (NumberField.Units.torsion E) : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2`. Conclude with `hT` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.

Conclude with `h2` after adjusting the coercions. Use `_ = ((Nat.card (NumberField.Units.torsion E) : ℕ) : ℝ) * (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard : ℕ) : ℝ) ^ 2 := by push_cast; ring`. Use `_ ≤ 8 * (f : ℝ) ^ 2 * ((D : ℝ) ^ e) ^ 2 := by gcongr`. Conclude with `hS.2`. Use `_ = 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * e) := by`.

Rewrite using `[← Real.rpow_natCast ((D : ℝ) ^ e) 2, ← Real.rpow_mul (Nat.cast_nonneg D), mul_comm e]`. Evaluate the numerical expressions.
-/
lemma cCount_of (E : Type) [Field E] [NumberField E] (f D : ℕ) (e : ℝ)
    (hT : Nat.card (NumberField.Units.torsion E) ≤ 8 * f ^ 2)
    (hS : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard : ℕ) : ℝ) ≤ (D : ℝ) ^ e) :
    (cSet E D).Finite ∧ (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * e) := by
  obtain ⟨h1, h2⟩ := cSet_count E D hS.1
  refine ⟨h1, ?_⟩
  have hT' : ((Nat.card (NumberField.Units.torsion E) : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 := by
    exact_mod_cast hT
  calc (((cSet E D).ncard : ℕ) : ℝ)
      ≤ ((Nat.card (NumberField.Units.torsion E) *
          {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h2
    _ = ((Nat.card (NumberField.Units.torsion E) : ℕ) : ℝ) *
          (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard : ℕ) : ℝ) ^ 2 := by
        push_cast; ring
    _ ≤ 8 * (f : ℝ) ^ 2 * ((D : ℝ) ^ e) ^ 2 := by
        gcongr
        exact hS.2
    _ = 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * e) := by
        rw [← Real.rpow_natCast ((D : ℝ) ^ e) 2, ← Real.rpow_mul (Nat.cast_nonneg D), mul_comm e]
        norm_num

end DualLatticeIndexBis

/- English proof (translation)
Introduce `hI hT E _ _ f D hf`. Conclude with `DualLatticeIndexBis.cCount_of E f D _ (hT E f hf) (hI E f D hf)`.
-/
theorem colon_count_of_hyp : CCountAsm := by
  intro hI hT E _ _ f D hf
  exact DualLatticeIndexBis.cCount_of E f D _ (hT E f hf) (hI E f D hf)

/- English proof (translation)
Introduce `hI hT E _ _ f D hf`. Establish `h` using `DualLatticeIndexBis.cCount_of E f D _ (hT E f hf) (hI E f D hf)`. Establish `e : 2 * (1 + (1 + Real.logb 2 (2 * (f : ℝ)))) = 2 + 2 * (1 + Real.logb 2 (2 * (f : ℝ)))` using `by ring`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem colon_count_weighted_of_hyp : CCountWAsm := by
  intro hI hT E _ _ f D hf
  have h := DualLatticeIndexBis.cCount_of E f D _ (hT E f hf) (hI E f D hf)
  have e : 2 * (1 + (1 + Real.logb 2 (2 * (f : ℝ)))) = 2 + 2 * (1 + Real.logb 2 (2 * (f : ℝ))) := by ring
  rw [e] at h
  exact h

/- English proof (translation)
The claim follows from `colon_count_of_hyp quotient_card torsion_bound_alt`.
-/
theorem colon_count_bound : CCount := colon_count_of_hyp quotient_card torsion_bound_alt

/- English proof (translation)
The claim follows from `colon_count_weighted_of_hyp ideal_count_le_weighted torsion_bound_alt`.
-/
theorem colon_count_weighted : CCountW := colon_count_weighted_of_hyp ideal_count_le_weighted torsion_bound_alt

namespace DualLatticeIndexBis

/- English proof (translation)
Distinguish the cases in `hMN : M ≤ N`. Establish `: N = M` using `le_antisymm hNM hMN`. Rewrite using `[this, AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (I := A * J) (J := J) Ideal.mul_le_right (mul_ne_zero hA hJ)`. Establish `haJ : Ideal.span {a} ≤ J` using `ha ▸ le_sup_right`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Apply `hMN` to reduce the goal to its premises. Establish `h1 : A * J = 1 * J`. Rewrite using `[one_mul]`.

Simplify using `using ha`. Establish `h2 : A = 1` using `mul_right_cancel₀ hJ h1`. Rewrite `hAM` using `[h2, Ideal.one_eq_top, Submodule.top_smul]`. Conclude with `hAM`. Take `⟨J', hJ'⟩` from `Ideal.dvd_iff_le.mpr haJ`.

Establish `hcop : A ⊔ J' = ⊤`. Establish `h1 : J * (A ⊔ J') = J * 1`. Rewrite using `[Ideal.mul_sup, ← hJ', mul_comm J A, ha, mul_one]`. Rewrite using `[← Ideal.one_eq_top]`. Conclude with `mul_left_cancel₀ hJ h1`.

Set `φ : U →ₗ[R] U` to `LinearMap.lsmul R U a`. Establish `hφ : Function.Injective φ`. Introduce `x y hxy`. Establish `h1 : a • (x - y) = 0`. Rewrite using `[smul_sub]`.

Conclude with `sub_eq_zero.mpr hxy`. Conclude with `sub_eq_zero.mp (htf a ha0 _ h1)`. Establish `hmap : ∀ L : Submodule R U, L.map φ = Ideal.span {a} • L`. Introduce `L`. Rewrite using `[Submodule.ideal_span_singleton_smul]`.

Use extensionality with `x`. Simplify using `[φ, Submodule.mem_smul_pointwise_iff_exists]`. Establish `h1 : J • M = M.map φ ⊔ J • N`. Apply `le_antisymm` to reduce the goal to its premises. Use `conv_lhs => rw [← ha]`.

Rewrite using `[Submodule.sup_smul, hmap M]`. Use `sup_le ?_ le_sup_left` and prove the remaining obligations. Rewrite using `[mul_comm, Submodule.mul_smul]`. Conclude with `(Submodule.smul_mono le_rfl hAM).trans le_sup_right`. Rewrite using `[hmap M]`.

Conclude with `sup_le (Submodule.smul_mono_left haJ) (Submodule.smul_mono le_rfl hNM)`. Establish `h2 : J • N ⊓ M.map φ = N.map φ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨hx1, y, hy, rfl⟩`. Use `⟨y, ?_, rfl⟩` and prove the remaining obligations.

Establish `h1 : (1 : R) ∈ A ⊔ J'` using `by rw [hcop]; trivial`. Take `⟨s, hs, t, ht, hst⟩` from `Submodule.mem_sup.mp h1`. Establish `hsy : s • y ∈ N` using `hAM (Submodule.smul_mem_smul hs hy)`. Establish `hty : t • y ∈ N`. Establish `h3 : t • φ y ∈ J' • (J • N)` using `Submodule.smul_mem_smul ht hx1`.

Rewrite `h3` using `[← Submodule.mul_smul, mul_comm J' J, ← hJ', ← hmap N]`. Take `⟨n, hn, hn'⟩` from `h3`. Establish `h4 : φ n = φ (t • y)` using `by rw [hn', map_smul]`. Rewrite using `[← hφ h4]`. Conclude with `hn`.

Establish `: y = s • y + t • y` using `by rw [← add_smul, hst, one_smul]`. Rewrite using `[this]`. Conclude with `N.add_mem hsy hty`. Use `le_inf ?_ (Submodule.map_mono hNM)` and prove the remaining obligations. Rewrite using `[hmap N]`.

Conclude with `Submodule.smul_mono_left haJ`. Establish `h2' : (J • N).toAddSubgroup ⊓ (M.map φ).toAddSubgroup = (N.map φ).toAddSubgroup`. Rewrite using `[← h2]`. Both sides reduce to the same expression. Rewrite using `[h1, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right, h2', Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]`.

Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hφ`.
-/
lemma relIndex_ideal_smul {R U : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup U] [Module R U]
    (htf : ∀ a : R, a ≠ 0 → ∀ x : U, a • x = 0 → x = 0) (M N : Submodule R U) (hNM : N ≤ M)
    (A J : Ideal R) (hA : A ≠ ⊥) (hJ : J ≠ ⊥) (hAM : A • M ≤ N) :
    (J • N).toAddSubgroup.relIndex (J • M).toAddSubgroup =
      N.toAddSubgroup.relIndex M.toAddSubgroup := by
  by_cases hMN : M ≤ N
  · have : N = M := le_antisymm hNM hMN
    rw [this, AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := A * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hA hJ)
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hMN
    have h1 : A * J = 1 * J := by
      rw [one_mul]
      simpa using ha
    have h2 : A = 1 := mul_right_cancel₀ hJ h1
    rw [h2, Ideal.one_eq_top, Submodule.top_smul] at hAM
    exact hAM
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr haJ
  have hcop : A ⊔ J' = ⊤ := by
    have h1 : J * (A ⊔ J') = J * 1 := by
      rw [Ideal.mul_sup, ← hJ', mul_comm J A, ha, mul_one]
    rw [← Ideal.one_eq_top]
    exact mul_left_cancel₀ hJ h1
  let φ : U →ₗ[R] U := LinearMap.lsmul R U a
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : a • (x - y) = 0 := by
      rw [smul_sub]; exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (htf a ha0 _ h1)
  have hmap : ∀ L : Submodule R U, L.map φ = Ideal.span {a} • L := by
    intro L
    rw [Submodule.ideal_span_singleton_smul]
    ext x
    simp [φ, Submodule.mem_smul_pointwise_iff_exists]
  have h1 : J • M = M.map φ ⊔ J • N := by
    apply le_antisymm
    · conv_lhs => rw [← ha]
      rw [Submodule.sup_smul, hmap M]
      refine sup_le ?_ le_sup_left
      rw [mul_comm, Submodule.mul_smul]
      exact (Submodule.smul_mono le_rfl hAM).trans le_sup_right
    · rw [hmap M]
      exact sup_le (Submodule.smul_mono_left haJ) (Submodule.smul_mono le_rfl hNM)
  have h2 : J • N ⊓ M.map φ = N.map φ := by
    apply le_antisymm
    · rintro x ⟨hx1, y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      have h1 : (1 : R) ∈ A ⊔ J' := by rw [hcop]; trivial
      obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp h1
      have hsy : s • y ∈ N := hAM (Submodule.smul_mem_smul hs hy)
      have hty : t • y ∈ N := by
        have h3 : t • φ y ∈ J' • (J • N) := Submodule.smul_mem_smul ht hx1
        rw [← Submodule.mul_smul, mul_comm J' J, ← hJ', ← hmap N] at h3
        obtain ⟨n, hn, hn'⟩ := h3
        have h4 : φ n = φ (t • y) := by rw [hn', map_smul]
        rw [← hφ h4]
        exact hn
      have : y = s • y + t • y := by rw [← add_smul, hst, one_smul]
      rw [this]
      exact N.add_mem hsy hty
    · refine le_inf ?_ (Submodule.map_mono hNM)
      rw [hmap N]
      exact Submodule.smul_mono_left haJ
  have h2' : (J • N).toAddSubgroup ⊓ (M.map φ).toAddSubgroup = (N.map φ).toAddSubgroup := by
    rw [← h2]; rfl
  rw [h1, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right,
    h2', Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hφ

open TensorProduct in
/- English proof (translation)
Set `_` to `Ideal.Quotient.field P`. Establish `e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M))` using `TensorProduct.quotTensorEquivQuotSMul M P`. Rewrite using `[← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]`. Use `congr 1`. Set `q : PrimeSpectrum (R ⧸ P)` to `⟨⊥, Ideal.isPrime_bot⟩`.

Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q`. Rewrite `h1` using `[Module.rankAtStalk_eq_finrank_of_free]`. Establish `h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M`. Rewrite using `[Module.rankAtStalk_eq]`. Conclude with `Ideal.finrank_fiber_eq_finrank _`.

Rewrite using `[← h2, ← h1]`. Both sides reduce to the same expression.
-/
lemma card_quot_prime {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [hP : P.IsMaximal] :
    Nat.card (M ⧸ (P • (⊤ : Submodule R M))) = Nat.card (R ⧸ P) ^ Module.finrank R M := by
  let _ := Ideal.Quotient.field P
  have e : ((R ⧸ P) ⊗[R] M) ≃ₗ[R] M ⧸ (P • (⊤ : Submodule R M)) :=
    TensorProduct.quotTensorEquivQuotSMul M P
  rw [← Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := R ⧸ P)]
  congr 1
  let q : PrimeSpectrum (R ⧸ P) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ P) q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1
  have h2 : Module.rankAtStalk M (q.comap (algebraMap R (R ⧸ P))) = Module.finrank R M := by
    rw [Module.rankAtStalk_eq]
    exact Ideal.finrank_fiber_eq_finrank _
  rw [← h2, ← h1]
  rfl

end DualLatticeIndexBis

/- English proof (translation)
Introduce `E _ _ M _ _ _ _ I`. Establish `htf : ∀ a : 𝓞 E, a ≠ 0 → ∀ x : M, a • x = 0 → x = 0` using `fun a ha x hx => by`. Establish `h` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M) (mem_nonZeroDivisors_of_ne_zero ha)`. Conclude with `h (hx.trans (smul_zero a).symm)`. Establish `hidx : ∀ S : Submodule (𝓞 E) M, Nat.card (M ⧸ S) = S.toAddSubgroup.index` using `fun S => rfl`.

Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁`. Establish `hb : ((0 : Ideal (𝓞 E)) • (⊤ : Submodule (𝓞 E) M)) = ⊥`. Rewrite using `[Ideal.zero_eq_bot, Submodule.bot_smul]`. Rewrite using `[hb, Nat.card_congr (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv, Ideal.zero_eq_bot, Ideal.absNorm_bot]`.

Break down `Nat.eq_zero_or_pos (Module.finrank (𝓞 E) M) with h0 | h0` into its components or cases. Rewrite using `[h0, pow_zero]`. Establish `htor` using `Module.finrank_eq_zero_iff_isTorsion.mp h0`. Establish `: Subsingleton M`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations.

Establish `hz : ∀ z : M, z = 0`. Introduce `z`. Take `⟨a, ha⟩` from `@htor z`. Conclude with `htf a (nonZeroDivisors.ne_zero a.2) z ha`. Rewrite using `[hz x, hz y]`.

Conclude with `Nat.card_unique`. Rewrite using `[zero_pow h0.ne']`. Establish `hnt : Nontrivial M`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`.

Rewrite `h0` using `[Module.finrank_zero_of_subsingleton]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx⟩` from `exists_ne (0 : M)`. Establish `hinj : Function.Injective (fun a : 𝓞 E => a • x)`. Introduce `a b hab`.

Assume the negation of the conclusion as `hne`. Establish `h1 : (a - b) • x = 0` using `by rw [sub_smul]; exact sub_eq_zero.mpr hab`. Conclude with `hx (htf _ (sub_ne_zero.mpr hne) x h1)`. Establish `: Infinite M` using `Infinite.of_injective _ hinj`. Conclude with `Nat.card_eq_zero_of_infinite`.

Consider the case `h₂ I hI`. Rewrite `hI` using `[Ideal.isUnit_iff]`. Substitute `hI` using the available equality. Simplify using the standard rewrite rules. Consider the case `h₃ I P hI hP ih`.

Establish `hP0 : P ≠ ⊥` using `hP.ne_zero`. Establish `hPm : P.IsMaximal` using `(Ideal.prime_iff_isPrime hP0).mp hP |>.isMaximal hP0`. Rewrite `ih`, the goal using `[hidx]`. Establish `hle : ((P * I) • (⊤ : Submodule (𝓞 E) M)) ≤ I • ⊤` using `Submodule.smul_mono_left Ideal.mul_le_right`. Rewrite using `[← AddSubgroup.relIndex_mul_index (H := ((P * I) • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup) (K := (I • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup) hle, ih, mul_comm P I, Submodule.mul_smul, DualLatticeIndexBis.relIndex_ideal_smul htf ⊤ (P • ⊤) le_top P I hP0 hI le_rfl]`.

Establish `h3 : (P • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup.relIndex (⊤ : Submodule (𝓞 E) M).toAddSubgroup = Ideal.absNorm P ^ Module.finrank (𝓞 E) M`. Rewrite using `[Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, ← hidx, DualLatticeIndexBis.card_quot_prime P, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite using `[h3, map_mul, mul_pow, mul_comm]`.
-/
theorem height_loss_bound : QuotCard := by
  intro E _ _ M _ _ _ _ I
  have htf : ∀ a : 𝓞 E, a ≠ 0 → ∀ x : M, a • x = 0 → x = 0 := fun a ha x hx => by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M)
      (mem_nonZeroDivisors_of_ne_zero ha)
    exact h (hx.trans (smul_zero a).symm)
  have hidx : ∀ S : Submodule (𝓞 E) M, Nat.card (M ⧸ S) = S.toAddSubgroup.index := fun S => rfl
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    have hb : ((0 : Ideal (𝓞 E)) • (⊤ : Submodule (𝓞 E) M)) = ⊥ := by
      rw [Ideal.zero_eq_bot, Submodule.bot_smul]
    rw [hb, Nat.card_congr (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv, Ideal.zero_eq_bot, Ideal.absNorm_bot]
    rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 E) M) with h0 | h0
    · rw [h0, pow_zero]
      have htor := Module.finrank_eq_zero_iff_isTorsion.mp h0
      have : Subsingleton M := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : M, z = 0 := by
          intro z
          obtain ⟨a, ha⟩ := @htor z
          exact htf a (nonZeroDivisors.ne_zero a.2) z ha
        rw [hz x, hz y]
      exact Nat.card_unique
    · rw [zero_pow h0.ne']
      have hnt : Nontrivial M := by
        by_contra hn
        rw [not_nontrivial_iff_subsingleton] at hn
        rw [Module.finrank_zero_of_subsingleton] at h0
        omega
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      have hinj : Function.Injective (fun a : 𝓞 E => a • x) := by
        intro a b hab
        by_contra hne
        have h1 : (a - b) • x = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr hab
        exact hx (htf _ (sub_ne_zero.mpr hne) x h1)
      have : Infinite M := Infinite.of_injective _ hinj
      exact Nat.card_eq_zero_of_infinite
  | h₂ I hI =>
    rw [Ideal.isUnit_iff] at hI
    subst hI
    simp
  | h₃ I P hI hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPm : P.IsMaximal := (Ideal.prime_iff_isPrime hP0).mp hP |>.isMaximal hP0
    rw [hidx] at ih ⊢
    have hle : ((P * I) • (⊤ : Submodule (𝓞 E) M)) ≤ I • ⊤ := Submodule.smul_mono_left Ideal.mul_le_right
    rw [← AddSubgroup.relIndex_mul_index (H := ((P * I) • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup)
      (K := (I • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup) hle, ih, mul_comm P I, Submodule.mul_smul,
      DualLatticeIndexBis.relIndex_ideal_smul htf ⊤ (P • ⊤) le_top P I hP0 hI le_rfl]
    have h3 : (P • (⊤ : Submodule (𝓞 E) M)).toAddSubgroup.relIndex
        (⊤ : Submodule (𝓞 E) M).toAddSubgroup = Ideal.absNorm P ^ Module.finrank (𝓞 E) M := by
      rw [Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right, ← hidx, DualLatticeIndexBis.card_quot_prime P,
        Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h3, map_mul, mul_pow, mul_comm]

namespace DualLatticeIndexBis

/- English proof (translation)
Establish `hLv : L = Submodule.span ℤ (Set.range (fun i => (c i : V)))`. Establish `: Set.range (fun i => (c i : V)) = L.subtype '' Set.range c`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]`.

Establish `hli : LinearIndependent ℚ (fun i => (c i : V))` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp (c.linearIndependent.map' L.subtype (Submodule.ker_subtype L))`. Establish `hsp : ⊤ ≤ Submodule.span ℚ (Set.range (fun i => (c i : V)))`. Introduce `x _`. Take `⟨n, hn, hnx⟩` from `hL x`. Rewrite `hnx` using `[hLv]`.

Establish `h1 : n • x ∈ Submodule.span ℚ (Set.range (fun i => (c i : V)))` using `Submodule.span_subset_span ℤ ℚ _ hnx`. Establish `h2 : x = (n : ℚ)⁻¹ • (n • x)`. Rewrite using `[← Int.cast_smul_eq_zsmul ℚ n x, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ h1`.

Use `⟨Module.Basis.mk hli hsp, fun i => by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.coe_mk]`. Conclude with `hLv`.
-/
lemma exists_rat_basis {V ι : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V] (L : Submodule ℤ V)
    (c : Module.Basis ι ℤ L) (hL : ∀ x : V, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L) :
    ∃ cb : Module.Basis ι ℚ V, (∀ i, cb i = (c i : V)) ∧ L = Submodule.span ℤ (Set.range cb) := by
  have hLv : L = Submodule.span ℤ (Set.range (fun i => (c i : V))) := by
    have : Set.range (fun i => (c i : V)) = L.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent ℚ (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (c.linearIndependent.map' L.subtype (Submodule.ker_subtype L))
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range (fun i => (c i : V))) := by
    intro x _
    obtain ⟨n, hn, hnx⟩ := hL x
    rw [hLv] at hnx
    have h1 : n • x ∈ Submodule.span ℚ (Set.range (fun i => (c i : V))) :=
      Submodule.span_subset_span ℤ ℚ _ hnx
    have h2 : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ n x, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  refine ⟨Module.Basis.mk hli hsp, fun i => by simp, ?_⟩
  rw [Module.Basis.coe_mk]
  exact hLv

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `h _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `h y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem x hx => obtain ⟨i, rfl⟩ := hx`. Conclude with `h i`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`.

Take `⟨m, hm⟩` from `hy`. Conclude with `⟨n + m, by rw [map_add, hn, hm]; push_cast; rfl⟩`. Consider the case `smul a x _ hx`. Take `⟨n, hn⟩` from `hx`. Conclude with `⟨a * n, by rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, hn]; push_cast; rfl⟩`.
-/
lemma int_on_span {V ι : Type*} [AddCommGroup V] [Module ℚ V] (φ : V →ₗ[ℚ] ℚ) (v : ι → V) :
    (∀ y ∈ Submodule.span ℤ (Set.range v), ∃ n : ℤ, φ y = n) ↔ ∀ i, ∃ n : ℤ, φ (v i) = n := by
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      exact ⟨n + m, by rw [map_add, hn, hm]; push_cast; rfl⟩
    | smul a x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨a * n, by rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, hn]; push_cast; rfl⟩

/- English proof (translation)
Establish `: Module.Finite ℤ B` using `Module.Finite.iff_fg.mpr hB`. Establish `: Module.IsTorsionFree ℤ V` using `Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V`. Take `⟨ι, _, ⟨b⟩⟩ : ∃ (ι : Type _) (_ : Fintype ι), Nonempty (Module.Basis ι ℤ B)` from `⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ B⟩⟩`. Set `A₀ : Submodule ℤ B` to `A.comap B.subtype`. Establish `hrank : Module.finrank ℤ A₀ = Module.finrank ℤ B`.

Establish `h1` using `Submodule.finrank_quotient_add_finrank A₀`. Establish `h2 : Module.finrank ℤ (B ⧸ A₀) = 0`. Rewrite using `[Module.finrank_eq_zero_iff_isTorsion]`. Introduce `x`. Take `⟨y, rfl⟩` from `A₀.mkQ_surjective x`.

Take `⟨n, hn, hny⟩` from `hA (y : V)`. Use `⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `n • A₀.mkQ y = 0`. Rewrite using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hny`.

Use linear arithmetic over natural numbers and integers. Take `⟨b', a, ab', hab⟩` from `Submodule.exists_smith_normal_form_of_rank_eq b hrank`. Take `⟨vb, hvb, hBv⟩` from `exists_rat_basis B b' (fun x => by`. Take `⟨n, hn, hnx⟩` from `hA x`. Conclude with `⟨n, hn, hAB hnx⟩)`.

Take `⟨va, hva, hAv⟩` from `exists_rat_basis A (ab'.map (Submodule.comapSubtypeEquivOfLe hAB)) hA`. Establish `hvab : ∀ i, va i = (a i : ℚ) • vb i`. Introduce `i`. Rewrite using `[hva, hvb, Module.Basis.map_apply, Submodule.comapSubtypeEquivOfLe_apply_coe, hab, Int.cast_smul_eq_zsmul]`. Both sides reduce to the same expression.

Set `S : V →ₗ[ℚ] V` to `∑ i, LinearMap.smulRight (t.flip (va i)) (vb i)`. Establish `hS1 : ∀ x, S x = ∑ i, t x (va i) • vb i`. Introduce `x`. Simplify using `[S, LinearMap.sum_apply]`. Establish `hS2 : ∀ x, S x = ∑ i, t x (vb i) • va i`.

Introduce `x`. Rewrite using `[hS1]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hvab, map_smul, smul_smul, smul_eq_mul, mul_comm]`. Establish `hr1 : ∀ x i, vb.repr (S x) i = t x (va i)`.

Introduce `x i`. Rewrite using `[hS1, Module.Basis.repr_sum_self]`. Establish `hr2 : ∀ x i, va.repr (S x) i = t x (vb i)`. Introduce `x i`. Rewrite using `[hS2, Module.Basis.repr_sum_self]`.

Establish `hinj : Function.Injective S`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Apply `hnd` to reduce the goal to its premises. Establish `h0 : t x = 0`.

Apply `va.ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← hr1, hx]`. Simplify using the standard rewrite rules. Introduce `y`.

Rewrite using `[h0]`. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective S` using `LinearMap.injective_iff_surjective.mp hinj`. Establish `hmem : ∀ (cb : Module.Basis ι ℚ V) (y : V), y ∈ Submodule.span ℤ (Set.range cb) ↔ ∀ i, ∃ n : ℤ, cb.repr y i = n`. Introduce `cb y`.

Rewrite using `[Module.Basis.mem_span_iff_repr_mem]`. Use `forall_congr' (fun i => ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Conclude with `⟨n, hn.symm⟩`.

Introduce and unpack `⟨n, hn⟩`. Conclude with `⟨n, hn.symm⟩`. Establish `eA : A' = B.toAddSubgroup.comap S.toAddMonoidHom`. Use extensionality with `x`. Rewrite using `[hA', hAv, int_on_span (t x) va, AddSubgroup.mem_comap]`.

Express the relevant statement in the definitionally equal form `_ ↔ S x ∈ B`. Rewrite using `[hBv, hmem]`. Simplify using `only [hr1]`. Establish `eB : B' = A.toAddSubgroup.comap S.toAddMonoidHom`. Use extensionality with `x`.

Rewrite using `[hB', hBv, int_on_span (t x) vb, AddSubgroup.mem_comap]`. Express the relevant statement in the definitionally equal form `_ ↔ S x ∈ A`. Rewrite using `[hAv, hmem]`. Simplify using `only [hr2]`. Rewrite using `[eA, eB, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]`.
-/
lemma zdual_relIndex {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (t : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hnd : ∀ x, (∀ y, t x y = 0) → x = 0)
    (A B : Submodule ℤ V) (hAB : A ≤ B) (hB : B.FG) (hA : ∀ x : V, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ A)
    (A' B' : AddSubgroup V)
    (hA' : ∀ x, x ∈ A' ↔ ∀ y ∈ A, ∃ n : ℤ, t x y = n)
    (hB' : ∀ x, x ∈ B' ↔ ∀ y ∈ B, ∃ n : ℤ, t x y = n) :
    B'.relIndex A' = A.toAddSubgroup.relIndex B.toAddSubgroup := by
  classical
  have : Module.Finite ℤ B := Module.Finite.iff_fg.mpr hB
  have : Module.IsTorsionFree ℤ V := Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  obtain ⟨ι, _, ⟨b⟩⟩ : ∃ (ι : Type _) (_ : Fintype ι), Nonempty (Module.Basis ι ℤ B) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ B⟩⟩
  let A₀ : Submodule ℤ B := A.comap B.subtype
  have hrank : Module.finrank ℤ A₀ = Module.finrank ℤ B := by
    have h1 := Submodule.finrank_quotient_add_finrank A₀
    have h2 : Module.finrank ℤ (B ⧸ A₀) = 0 := by
      rw [Module.finrank_eq_zero_iff_isTorsion]
      intro x
      obtain ⟨y, rfl⟩ := A₀.mkQ_surjective x
      obtain ⟨n, hn, hny⟩ := hA (y : V)
      refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
      change n • A₀.mkQ y = 0
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hny
    omega
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b hrank
  obtain ⟨vb, hvb, hBv⟩ := exists_rat_basis B b' (fun x => by
    obtain ⟨n, hn, hnx⟩ := hA x
    exact ⟨n, hn, hAB hnx⟩)
  obtain ⟨va, hva, hAv⟩ := exists_rat_basis A (ab'.map (Submodule.comapSubtypeEquivOfLe hAB)) hA
  have hvab : ∀ i, va i = (a i : ℚ) • vb i := by
    intro i
    rw [hva, hvb, Module.Basis.map_apply, Submodule.comapSubtypeEquivOfLe_apply_coe, hab,
      Int.cast_smul_eq_zsmul]
    rfl
  let S : V →ₗ[ℚ] V := ∑ i, LinearMap.smulRight (t.flip (va i)) (vb i)
  have hS1 : ∀ x, S x = ∑ i, t x (va i) • vb i := by
    intro x; simp [S, LinearMap.sum_apply]
  have hS2 : ∀ x, S x = ∑ i, t x (vb i) • va i := by
    intro x
    rw [hS1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hvab, map_smul, smul_smul, smul_eq_mul, mul_comm]
  have hr1 : ∀ x i, vb.repr (S x) i = t x (va i) := by
    intro x i
    rw [hS1, Module.Basis.repr_sum_self]
  have hr2 : ∀ x i, va.repr (S x) i = t x (vb i) := by
    intro x i
    rw [hS2, Module.Basis.repr_sum_self]
  have hinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hnd
    have h0 : t x = 0 := by
      apply va.ext
      intro i
      rw [← hr1, hx]; simp
    intro y
    rw [h0]; rfl
  have hsurj : Function.Surjective S := LinearMap.injective_iff_surjective.mp hinj
  have hmem : ∀ (cb : Module.Basis ι ℚ V) (y : V), y ∈ Submodule.span ℤ (Set.range cb) ↔
      ∀ i, ∃ n : ℤ, cb.repr y i = n := by
    intro cb y
    rw [Module.Basis.mem_span_iff_repr_mem]
    refine forall_congr' (fun i => ?_)
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
  have eA : A' = B.toAddSubgroup.comap S.toAddMonoidHom := by
    ext x
    rw [hA', hAv, int_on_span (t x) va, AddSubgroup.mem_comap]
    change _ ↔ S x ∈ B
    rw [hBv, hmem]
    simp only [hr1]
  have eB : B' = A.toAddSubgroup.comap S.toAddMonoidHom := by
    ext x
    rw [hB', hBv, int_on_span (t x) vb, AddSubgroup.mem_comap]
    change _ ↔ S x ∈ A
    rw [hAv, hmem]
    simp only [hr2]
  rw [eA, eB, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]

end DualLatticeIndexBis

namespace DualLatticeIndexBis

open scoped Pointwise in

/- English proof (translation)
Set `σ : 𝓞 E →+* 𝓞 E` to `RingOfIntegers.mapRingHom (starRingEnd E)`. Establish `hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = star (a : E)` using `fun a => rfl`. Establish `hσσ : ∀ a : 𝓞 E, σ (σ a) = a`. Introduce `a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hσ, hσ, star_star]`. Set `Dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E` to `FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Establish `hDd0 : Dd ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`. Set `δ : 𝓞 E` to `(Dd.den : 𝓞 E)`. Establish `hδ : δ ≠ 0` using `nonZeroDivisors.ne_zero Dd.den.2`.

Establish `hδE : (δ : E) ≠ 0`. Introduce `h0`. Conclude with `hδ (RingOfIntegers.ext (by simpa using h0))`. Establish `F1 : ∀ a₀ ∈ Dd.num, ∃ w ∈ Dd, (a₀ : E) = (δ : E) * w`. Introduce `a₀ ha₀`.

Establish `h1 : (a₀ : E) ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) Dd.num` using `⟨a₀, ha₀, rfl⟩`. Rewrite `h1` using `[← FractionalIdeal.den_mul_self_eq_num]`. Take `⟨w, hw, hw'⟩` from `h1`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw']`.

Conclude with `Algebra.smul_def δ w`. Establish `F2 : ∀ w ∈ Dd, ∃ a₀ ∈ Dd.num, (a₀ : E) = (δ : E) * w`. Introduce `w hw`. Establish `h1 : Dd.den • w ∈ Dd.den • (Dd : Submodule (𝓞 E) E)` using `Submodule.smul_mem_pointwise_smul _ _ _ hw`. Rewrite `h1` using `[FractionalIdeal.den_mul_self_eq_num]`.

Take `⟨a₀, ha₀, ha₀'⟩` from `h1`. Use `⟨a₀, ha₀, ?_⟩` and prove the remaining obligations. Establish `h2 : (a₀ : E) = Dd.den • w` using `ha₀'`. Rewrite using `[h2]`. Conclude with `Algebra.smul_def δ w`.

Establish `hone : (1 : E) ∈ Dd` using `FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)`. Use `⟨δ, Ideal.comap σ Dd.num, hδ, ?_, ?_⟩` and prove the remaining obligations. Introduce `hbot`. Take `⟨a₀, ha₀, ha₀'⟩` from `F2 1 hone`. Establish `h1 : σ a₀ ∈ Ideal.comap σ Dd.num`.

Rewrite using `[Ideal.mem_comap, hσσ]`. Conclude with `ha₀`. Rewrite `h1` using `[hbot, Ideal.mem_bot]`. Establish `h2 : a₀ = 0` using `by rw [← hσσ a₀, h1, map_zero]`. Rewrite `ha₀'` using `[h2, mul_one]`.

Conclude with `hδE (by simpa using ha₀'.symm)`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩ a ha`. Take `⟨w, hw, hw'⟩` from `F1 (σ a) ha`.

Establish `h1` using `(FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0)).mp hw (o : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨o, rfl⟩)`. Take `⟨n, hn⟩` from `h1`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hσ, hw', mul_comm (δ : E) w, mul_assoc, ← ho]`. Rewrite `hn` using `[Algebra.traceForm_apply]`.

Conclude with `hn.symm`. Introduce `H`. Establish `h1 : (δ : E) * z ∈ FractionalIdeal.dual ℤ ℚ Dd`. Rewrite using `[FractionalIdeal.mem_dual hDd0]`. Introduce `w hw`.

Take `⟨a₀, ha₀, ha₀'⟩` from `F2 w hw`. Take `⟨n, hn⟩` from `H (σ a₀) (by rw [Ideal.mem_comap, hσσ]; exact ha₀)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.traceForm_apply]`. Rewrite `hn` using `[← hσ, hσσ, ha₀']`.

Rewrite using `[show (δ : E) * z * w = (δ : E) * w * z by ring, hn]`. Both sides reduce to the same expression. Rewrite `h1` using `[FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff]`. Conclude with `h1`.
-/
lemma exists_codiff (E : Type) [Field E] [NumberField E] [StarRing E] :
    ∃ (δ : 𝓞 E) (K : Ideal (𝓞 E)), δ ≠ 0 ∧ K ≠ ⊥ ∧ ∀ z : E,
      (∃ o : 𝓞 E, (o : E) = (δ : E) * z) ↔
        ∀ a ∈ K, ∃ n : ℤ, Algebra.trace ℚ E (star (a : E) * z) = n := by
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = star (a : E) := fun a => rfl
  have hσσ : ∀ a : 𝓞 E, σ (σ a) = a := by
    intro a
    apply RingOfIntegers.ext
    rw [hσ, hσ, star_star]
  let Dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  have hDd0 : Dd ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  let δ : 𝓞 E := (Dd.den : 𝓞 E)
  have hδ : δ ≠ 0 := nonZeroDivisors.ne_zero Dd.den.2
  have hδE : (δ : E) ≠ 0 := by
    intro h0
    exact hδ (RingOfIntegers.ext (by simpa using h0))
  have F1 : ∀ a₀ ∈ Dd.num, ∃ w ∈ Dd, (a₀ : E) = (δ : E) * w := by
    intro a₀ ha₀
    have h1 : (a₀ : E) ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) Dd.num := ⟨a₀, ha₀, rfl⟩
    rw [← FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨w, hw, hw'⟩ := h1
    refine ⟨w, hw, ?_⟩
    rw [← hw']
    exact Algebra.smul_def δ w
  have F2 : ∀ w ∈ Dd, ∃ a₀ ∈ Dd.num, (a₀ : E) = (δ : E) * w := by
    intro w hw
    have h1 : Dd.den • w ∈ Dd.den • (Dd : Submodule (𝓞 E) E) :=
      Submodule.smul_mem_pointwise_smul _ _ _ hw
    rw [FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨a₀, ha₀, ha₀'⟩ := h1
    refine ⟨a₀, ha₀, ?_⟩
    have h2 : (a₀ : E) = Dd.den • w := ha₀'
    rw [h2]
    exact Algebra.smul_def δ w
  have hone : (1 : E) ∈ Dd := FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)
  refine ⟨δ, Ideal.comap σ Dd.num, hδ, ?_, ?_⟩
  · intro hbot
    obtain ⟨a₀, ha₀, ha₀'⟩ := F2 1 hone
    have h1 : σ a₀ ∈ Ideal.comap σ Dd.num := by
      rw [Ideal.mem_comap, hσσ]; exact ha₀
    rw [hbot, Ideal.mem_bot] at h1
    have h2 : a₀ = 0 := by rw [← hσσ a₀, h1, map_zero]
    rw [h2, mul_one] at ha₀'
    exact hδE (by simpa using ha₀'.symm)
  · intro z
    constructor
    · rintro ⟨o, ho⟩ a ha
      obtain ⟨w, hw, hw'⟩ := F1 (σ a) ha
      have h1 := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ)
        (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0)).mp hw (o : E)
        ((FractionalIdeal.mem_one_iff _).mpr ⟨o, rfl⟩)
      obtain ⟨n, hn⟩ := h1
      refine ⟨n, ?_⟩
      rw [← hσ, hw', mul_comm (δ : E) w, mul_assoc, ← ho]
      rw [Algebra.traceForm_apply] at hn
      exact hn.symm
    · intro H
      have h1 : (δ : E) * z ∈ FractionalIdeal.dual ℤ ℚ Dd := by
        rw [FractionalIdeal.mem_dual hDd0]
        intro w hw
        obtain ⟨a₀, ha₀, ha₀'⟩ := F2 w hw
        obtain ⟨n, hn⟩ := H (σ a₀) (by rw [Ideal.mem_comap, hσσ]; exact ha₀)
        refine ⟨n, ?_⟩
        rw [Algebra.traceForm_apply]
        rw [← hσ, hσσ, ha₀'] at hn
        rw [show (δ : E) * z * w = (δ : E) * w * z by ring, hn]
        rfl
      rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h1
      exact h1

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second'.goal1 .. | (apply Bl.general_b_fact_second'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second'.goal1 <;> assumption)`.
-/
lemma exists_smul_mem_of_span {E U : Type} [Field E] [NumberField E] [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (N : Submodule (𝓞 E) U)
    (hN : Submodule.span E (N : Set U) = ⊤) (x : U) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ N := by
  first | exact Bl.general_b_fact_second'.goal1 .. | (apply Bl.general_b_fact_second'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second'.goal1 <;> assumption)

/- English proof (translation)
Establish `h1` using `Ideal.absNorm_mem (Ideal.span {d})`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp h1`. Use `⟨(Ideal.absNorm (Ideal.span {d}) : ℕ), ?_, ?_⟩` and prove the remaining obligations. Establish `: Ideal.absNorm (Ideal.span {d}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`.

Conclude with `hd`. Conclude with `this` after adjusting the coercions. Rewrite using `[natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul]`. Conclude with `L.smul_mem c hx`.
-/
lemma exists_int_smul_mem {E U : Type} [Field E] [NumberField E] [AddCommGroup U]
    [Module (𝓞 E) U] (L : Submodule (𝓞 E) U) (x : U) (d : 𝓞 E) (hd : d ≠ 0) (hx : d • x ∈ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  have h1 := Ideal.absNorm_mem (Ideal.span {d})
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
  refine ⟨(Ideal.absNorm (Ideal.span {d}) : ℕ), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    exact_mod_cast this
  · rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul]
    exact L.smul_mem c hx

/- English proof (translation)
Proceed by induction on `M, hM using Submodule.fg_induction with`. Consider the case `singleton x`. Take `⟨d, hd, hdx⟩` from `exists_smul_mem_of_span N hN x`. Use `⟨d, hd, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hy`.

Rewrite using `[smul_comm]`. Conclude with `N.smul_mem r hdx`. Consider the case `sup M₁ M₂ _ _ h₁ h₂`. Take `⟨d, hd, hdx⟩` from `h₁`. Take `⟨e, he, hey⟩` from `h₂`.

Use `⟨d * e, mul_ne_zero hd he, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.mp hz`. Rewrite using `[smul_add]`. Use `N.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `N.smul_mem e (hdx x hx)`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem d (hey y hy)`.
-/
lemma exists_smul_le {E U : Type} [Field E] [NumberField E] [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] (N M : Submodule (𝓞 E) U)
    (hN : Submodule.span E (N : Set U) = ⊤) (hM : M.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ x ∈ M, d • x ∈ N := by
  induction M, hM using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_span N hN x
    refine ⟨d, hd, fun y hy => ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_comm]
    exact N.smul_mem r hdx
  | sup M₁ M₂ _ _ h₁ h₂ =>
    obtain ⟨d, hd, hdx⟩ := h₁
    obtain ⟨e, he, hey⟩ := h₂
    refine ⟨d * e, mul_ne_zero hd he, fun z hz => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem e (hdx x hx)
    · rw [mul_smul]; exact N.smul_mem d (hey y hy)

end DualLatticeIndexBis

namespace DualLatticeIndexBis

section Dual

variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]

noncomputable def trForm (h : U →ₗ[E] U →ₗ⋆[E] E) : U →ₗ[ℚ] U →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (h x y))
    (fun x x' y => by simp only [map_add, LinearMap.add_apply])
    (fun q x y => by
      rw [← algebraMap_smul E q x, map_smul, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [map_add])
    (fun q x y => by
      rw [← algebraMap_smul E q y, LinearMap.map_smulₛₗ, RingHom.map_rat_algebraMap, smul_eq_mul,
        ← Algebra.smul_def, map_smul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma trForm_apply (h : U →ₗ[E] U →ₗ⋆[E] E) (x y : U) :
    trForm h x y = Algebra.trace ℚ E (h x y) := rfl

/- English proof (translation)
Introduce `x hx`. Apply `hnd` to reduce the goal to its premises. Introduce `y`. Apply `(traceForm_nondegenerate ℚ E).1` to reduce the goal to its premises. Introduce `e`.

Rewrite using `[Algebra.traceForm_apply]`. Establish `h1` using `hx (star e • y)`. Rewrite `h1` using `[trForm_apply, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]`. Conclude with `h1`.
-/
lemma trForm_nondeg (h : U →ₗ[E] U →ₗ⋆[E] E) (hnd : ∀ x : U, (∀ y : U, h x y = 0) → x = 0) :
    ∀ x, (∀ y, trForm h x y = 0) → x = 0 := by
  intro x hx
  apply hnd
  intro y
  apply (traceForm_nondegenerate ℚ E).1
  intro e
  rw [Algebra.traceForm_apply]
  have h1 := hx (star e • y)
  rw [trForm_apply, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm] at h1
  exact h1

/- English proof (translation)
Establish `hsm : ∀ (a : 𝓞 E) (x : U), a • x = (a : E) • x` using `fun a x => (algebraMap_smul E a x).symm`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Use `Submodule.smul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `a ha y hy`.

Take `⟨o, ho⟩` from `H y hy`. Establish `h1 : (o : E) = (δ : E) * h x y`. Rewrite `ho` using `[map_smul, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `ho`. Take `⟨n, hn⟩` from `(hcod (h x y)).mp ⟨o, h1⟩ a ha`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[trForm_apply, hsm, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]`. Conclude with `hn`. Introduce and unpack `y y' ⟨n, hn⟩ ⟨m, hm⟩`. Conclude with `⟨n + m, by rw [map_add, hn, hm]; push_cast; rfl⟩`.

Introduce `H y hy`. Establish `h1 : ∃ o : 𝓞 E, (o : E) = (δ : E) * h x y`. Rewrite using `[hcod]`. Introduce `a ha`. Take `⟨n, hn⟩` from `H (a • y) (Submodule.smul_mem_smul ha hy)`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[trForm_apply, hsm, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]`. Conclude with `hn`. Take `⟨o, ho⟩` from `h1`. Use `⟨o, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `ho`.
-/
lemma dual_key (h : U →ₗ[E] U →ₗ⋆[E] E) (δ : 𝓞 E) (K : Ideal (𝓞 E))
    (hcod : ∀ z : E, (∃ o : 𝓞 E, (o : E) = (δ : E) * z) ↔
        ∀ a ∈ K, ∃ n : ℤ, Algebra.trace ℚ E (star (a : E) * z) = n)
    (L : Submodule (𝓞 E) U) (x : U) :
    ((δ : E) • x ∈ hdual h (algebraMap (𝓞 E) E).range L.toAddSubgroup) ↔
        ∀ y ∈ K • L, ∃ n : ℤ, trForm h x y = n := by
  have hsm : ∀ (a : 𝓞 E) (x : U), a • x = (a : E) • x := fun a x => (algebraMap_smul E a x).symm
  constructor
  · intro H y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha y hy
      obtain ⟨o, ho⟩ := H y hy
      have h1 : (o : E) = (δ : E) * h x y := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at ho
        exact ho
      obtain ⟨n, hn⟩ := (hcod (h x y)).mp ⟨o, h1⟩ a ha
      refine ⟨n, ?_⟩
      rw [trForm_apply, hsm, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
      exact hn
    · rintro y y' ⟨n, hn⟩ ⟨m, hm⟩
      exact ⟨n + m, by rw [map_add, hn, hm]; push_cast; rfl⟩
  · intro H y hy
    have h1 : ∃ o : 𝓞 E, (o : E) = (δ : E) * h x y := by
      rw [hcod]
      intro a ha
      obtain ⟨n, hn⟩ := H (a • y) (Submodule.smul_mem_smul ha hy)
      refine ⟨n, ?_⟩
      rw [trForm_apply, hsm, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul] at hn
      exact hn
    obtain ⟨o, ho⟩ := h1
    refine ⟨o, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact ho

/- English proof (translation)
Establish `h1 : Module.Finite (𝓞 E) ↥L` using `Module.Finite.iff_fg.mpr hL`. Establish `h2 : Module.Finite ℤ ↥L` using `Module.Finite.trans (𝓞 E) _`. Conclude with `Module.Finite.iff_fg.mp h2`.
-/
lemma fg_int (L : Submodule (𝓞 E) U) (hL : L.FG) : (L.restrictScalars ℤ).FG := by
  have h1 : Module.Finite (𝓞 E) ↥L := Module.Finite.iff_fg.mpr hL
  have h2 : Module.Finite ℤ ↥L := Module.Finite.trans (𝓞 E) _
  exact Module.Finite.iff_fg.mp h2

/- English proof (translation)
Take `⟨δ, K, hδ, hK, hcod⟩` from `exists_codiff E`. Establish `hδE : (δ : E) ≠ 0`. Introduce `h0`. Conclude with `hδ (RingOfIntegers.ext (by simpa using h0))`. Establish `hsm : ∀ (a : 𝓞 E) (x : U), a • x = (a : E) • x` using `fun a x => (algebraMap_smul E a x).symm`.

Establish `htf : ∀ a : 𝓞 E, a ≠ 0 → ∀ x : U, a • x = 0 → x = 0`. Introduce `a ha x hx`. Rewrite `hx` using `[hsm]`. Break down `smul_eq_zero.mp hx with h0 | h0` into its components or cases. Conclude with `absurd (RingOfIntegers.ext (by simpa using h0)) ha`.

Conclude with `h0`. Take `⟨d, hd, hdM⟩` from `exists_smul_le N M hN hM`. Take `⟨k, hkK, hk0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hK`. Set `mδ : U →+ U` to `(LinearMap.lsmul E U (δ : E)).toAddMonoidHom`. Establish `hmδ : Function.Surjective mδ`.

Introduce `x`. Use `⟨(δ : E)⁻¹ • x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(δ : E) • ((δ : E)⁻¹ • x) = x`. Rewrite using `[smul_smul, mul_inv_cancel₀ hδE, one_smul]`. Establish `hfgZ : ((K • M).restrictScalars ℤ).FG` using `fg_int _ (Submodule.FG.of_le hM Submodule.smul_le_right)`.

Establish `hle : (K • N).restrictScalars ℤ ≤ (K • M).restrictScalars ℤ`. Introduce `x hx`. Conclude with `Submodule.smul_mono (le_refl K) hNM hx`. Establish `hfull : ∀ x : U, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ (K • N).restrictScalars ℤ`. Introduce `x`.

Take `⟨e, he, hex⟩` from `exists_smul_mem_of_span N hN x`. Use `exists_int_smul_mem (K • N) x (k * e) (mul_ne_zero hk0 he) ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mem_smul hkK hex`. Establish `hZ` using `zdual_relIndex (trForm h) (trForm_nondeg h hnd) ((K • N).restrictScalars ℤ) ((K • M).restrictScalars ℤ) hle hfgZ hfull ((hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup).comap mδ) ((hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).comap mδ) (fun x => dual_key h δ K hcod N x …`.

Rewrite `hZ` using `[AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hmδ]`. Rewrite using `[hZ]`. Use `relIndex_ideal_smul htf M N hNM (Ideal.span {d}) K ?_ hK ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hd`.

Rewrite using `[Submodule.smul_le]`. Introduce `r hr x hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem c (hdM x hx)`.
-/
lemma relIndex_hermitian_dual_eq [FiniteDimensional ℚ U] (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U)
    (hnd : ∀ x : U, (∀ y : U, h x y = 0) → x = 0) (hNM : N ≤ M) (hM : M.FG)
    (hN : Submodule.span E (N : Set U) = ⊤) :
    (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup := by
  obtain ⟨δ, K, hδ, hK, hcod⟩ := exists_codiff E
  have hδE : (δ : E) ≠ 0 := by
    intro h0
    exact hδ (RingOfIntegers.ext (by simpa using h0))
  have hsm : ∀ (a : 𝓞 E) (x : U), a • x = (a : E) • x := fun a x => (algebraMap_smul E a x).symm
  have htf : ∀ a : 𝓞 E, a ≠ 0 → ∀ x : U, a • x = 0 → x = 0 := by
    intro a ha x hx
    rw [hsm] at hx
    rcases smul_eq_zero.mp hx with h0 | h0
    · exact absurd (RingOfIntegers.ext (by simpa using h0)) ha
    · exact h0
  obtain ⟨d, hd, hdM⟩ := exists_smul_le N M hN hM
  obtain ⟨k, hkK, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  let mδ : U →+ U := (LinearMap.lsmul E U (δ : E)).toAddMonoidHom
  have hmδ : Function.Surjective mδ := by
    intro x
    refine ⟨(δ : E)⁻¹ • x, ?_⟩
    change (δ : E) • ((δ : E)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hδE, one_smul]
  have hfgZ : ((K • M).restrictScalars ℤ).FG :=
    fg_int _ (Submodule.FG.of_le hM Submodule.smul_le_right)
  have hle : (K • N).restrictScalars ℤ ≤ (K • M).restrictScalars ℤ := by
    intro x hx
    exact Submodule.smul_mono (le_refl K) hNM hx
  have hfull : ∀ x : U, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ (K • N).restrictScalars ℤ := by
    intro x
    obtain ⟨e, he, hex⟩ := exists_smul_mem_of_span N hN x
    refine exists_int_smul_mem (K • N) x (k * e) (mul_ne_zero hk0 he) ?_
    rw [mul_smul]
    exact Submodule.smul_mem_smul hkK hex
  have hZ := zdual_relIndex (trForm h) (trForm_nondeg h hnd) ((K • N).restrictScalars ℤ)
    ((K • M).restrictScalars ℤ) hle hfgZ hfull
    ((hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup).comap mδ)
    ((hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).comap mδ)
    (fun x => dual_key h δ K hcod N x) (fun x => dual_key h δ K hcod M x)
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hmδ] at hZ
  rw [hZ]
  refine relIndex_ideal_smul htf M N hNM (Ideal.span {d}) K ?_ hK ?_
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hd
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [mul_smul]
    exact N.smul_mem c (hdM x hx)

end Dual

end DualLatticeIndexBis

/- English proof (translation)
Introduce `E _ _ _ U _ _ _ _ _ h M N hnd hNM hM hN`. Set `_ : Module ℚ U` to `Module.compHom U (algebraMap ℚ E)`. Establish `hq : ∀ (q : ℚ) (x : U), q • x = (algebraMap ℚ E q) • x` using `fun _ _ => rfl`. Establish `: IsScalarTower ℚ E U` using `⟨fun q e x => by rw [hq, Algebra.smul_def, mul_smul]⟩`. Establish `: FiniteDimensional ℚ U` using `Module.Finite.trans E U`.

Conclude with `DualLatticeIndexBis.relIndex_hermitian_dual_eq h M N hnd hNM hM hN`.
-/
theorem dual_lattice_index : DualIndex := by
  intro E _ _ _ U _ _ _ _ _ h M N hnd hNM hM hN
  let _ : Module ℚ U := Module.compHom U (algebraMap ℚ E)
  have hq : ∀ (q : ℚ) (x : U), q • x = (algebraMap ℚ E q) • x := fun _ _ => rfl
  have : IsScalarTower ℚ E U := ⟨fun q e x => by rw [hq, Algebra.smul_def, mul_smul]⟩
  have : FiniteDimensional ℚ U := Module.Finite.trans E U
  exact DualLatticeIndexBis.relIndex_hermitian_dual_eq h M N hnd hNM hM hN

end Formalism.HermitianLatticeCounting.P
