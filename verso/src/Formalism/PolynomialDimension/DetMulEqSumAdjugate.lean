import Formalism.PolynomialDimension.MultinomialDepth.ExistsNonzeroExchangedMinorHolds
import Formalism.PolynomialDimension.MultinomialDepth.FrobeniusDetVanishingHolds
import Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds

namespace Formalism.CountingSumsFrames.Top

/- English proof (translation)
Introduce `p J n' z hz hJ`. Establish `key : ∀ m, m ≤ J → (∑ j ∈ Finset.range m, (z (j + 1) - z j)) + z 0 = z m`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _`.

Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `hm`. Rewrite using `[Finset.sum_range_succ]`. Establish `h1` using `ih (by omega)`.

Establish `h2` using `hz m (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `hterm : ∀ j ∈ Finset.range J, (p : ℤ) ^ z j * ((p : ℤ) ^ (z (j + 1) - z j) - 1) = (p : ℤ) ^ z (j + 1) - (p : ℤ) ^ z j`. Introduce `j hj`. Establish `h` using `hz j (Finset.mem_range.mp hj)`.

Rewrite using `[mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j => (p : ℤ) ^ z j), hJ, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.prod_pow_eq_pow_sum]`.

Use `congr 1`. Use `key J le_rfl` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem locTelescope : Formalism.CountingSumsFrames.LocTelescope := by
  intro p J n' z hz hJ
  have key : ∀ m, m ≤ J → (∑ j ∈ Finset.range m, (z (j + 1) - z j)) + z 0 = z m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hz m (by omega)
      omega
  have hterm : ∀ j ∈ Finset.range J, (p : ℤ) ^ z j * ((p : ℤ) ^ (z (j + 1) - z j) - 1) =
      (p : ℤ) ^ z (j + 1) - (p : ℤ) ^ z j := by
    intro j hj
    have h := hz j (Finset.mem_range.mp hj)
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j => (p : ℤ) ^ z j), hJ, pow_add]
    ring
  · rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    have := key J le_rfl
    omega
/- English proof (translation)
Introduce `F _ r k h H hA hex`. Take `⟨i0, c, hc, hne⟩` from `hex`. Establish `hv : (fun m => H m c) ≠ 0` using `fun h0 => hne (congrFun h0 i0)`. Establish `hw : Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c) ≠ 0`. Introduce `h0`.

Apply `hv` to reduce the goal to its premises. Establish `h1 : Matrix.mulVec (H.submatrix id (Fin.castLE h)) (Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c)) = (H.submatrix id (Fin.castLE h)).det • (fun m => H m c)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_adjugate]`. Use `first`. Consider the case `rw [Matrix.smul_mulVec, Matrix.one_mulVec]`.

Consider the case `rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]`. Consider the case `(ext x; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])`. Rewrite `h1` using `[h0, Matrix.mulVec_zero]`. Conclude with `(smul_eq_zero.mp h1.symm).resolve_left hA`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c) i ≠ 0 := by`.

Assume the negation of the conclusion as `hh`. Use `push_neg at hh`. Conclude with `hw (funext hh)`. Use `⟨i, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[submatrix_swapCol, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]`.

Conclude with `hi`.
-/
theorem graphMinor : Formalism.CountingSumsFrames.GraphMinor := by
  intro F _ r k h H hA hex
  obtain ⟨i0, c, hc, hne⟩ := hex
  have hv : (fun m => H m c) ≠ 0 := fun h0 => hne (congrFun h0 i0)
  have hw : Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c) ≠ 0 := by
    intro h0
    apply hv
    have h1 : Matrix.mulVec (H.submatrix id (Fin.castLE h))
        (Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c)) =
        (H.submatrix id (Fin.castLE h)).det • (fun m => H m c) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate]
      first
        | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
        | (ext x; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
    rw [h0, Matrix.mulVec_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left hA
  obtain ⟨i, hi⟩ : ∃ i, Matrix.mulVec (H.submatrix id (Fin.castLE h)).adjugate (fun m => H m c) i ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hw (funext hh)
  refine ⟨i, c, hc, ?_⟩
  rw [submatrix_swapCol, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  exact hi
/- English proof (translation)
Introduce `p _ F _ _ _ n' r k J h hcard z hz hzJ pos hpos H hH A _ _ t`. Break down `subsingleton_or_nontrivial A with hA | hA` into its components or cases. Conclude with `Subsingleton.elim _ _`. Establish `hp1 : ∀ m, 1 ≤ p ^ m` using `fun m => Nat.one_le_pow _ _ (Fact.out : p.Prime).pos`. Establish `hJ : 0 < J`.

Assume the negation of the conclusion as `hJ0`. Establish `hJ' : J = 0` using `by omega`. Substitute `hJ'` using the available equality. Establish `hn : n' = 0` using `by omega`. Rewrite `hcard` using `[hn, pow_zero]`.

Establish `h1` using `Fintype.one_lt_card (α := F)`. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ j ∈ Finset.range J, p ^ z j * (p ^ (z (j + 1) - z j) - 1) = p ^ z 0 * (p ^ n' - 1)`. Establish `h1` using `(locTelescope p J n' z hz hzJ).1`. Establish `h2 : ((∑ j ∈ Finset.range J, p ^ z j * (p ^ (z (j + 1) - z j) - 1) : ℕ) : ℤ) = ((p ^ z 0 * (p ^ n' - 1) : ℕ) : ℤ)`.

Rewrite using `[Nat.cast_sum, Finset.sum_congr rfl fun j _ => by`. Rewrite using `[Nat.cast_mul, Nat.cast_sub (hp1 _), Nat.cast_pow, Nat.cast_pow, Nat.cast_one]]`. Rewrite using `[Nat.cast_mul, Nat.cast_sub (hp1 _), Nat.cast_pow, Nat.cast_pow, Nat.cast_one]`. Conclude with `h1`. Conclude with `h2` after adjusting the coercions.

Establish `hexp : ∀ x : F, x ≠ 0 → ∏ j ∈ Finset.range J, (x ^ p ^ z j) ^ (p ^ (z (j + 1) - z j) - 1) = 1`. Introduce `x hx`. Simplify using `only [← pow_mul]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hsum, pow_mul, ← hcard]`. Conclude with `FiniteField.pow_card_sub_one_eq_one _ (pow_ne_zero _ hx)`.

Establish `hfac : ∀ cols : Fin r → Fin k, ∏ j ∈ Finset.range J, piMinor p r k (H.map (algebraMap F A)) (pos j) (t j) (z j) cols ^ (p ^ (z (j + 1) - z j) - 1) = (∏ j ∈ Finset.range J, (Matrix.of fun l m => t j l m ^ p ^ (z j - pos j l)).det ^ (p ^ (z (j + 1) - z j) - 1)) * algebraMap F A (∏ …`. Introduce `cols`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[piMinor_map H (pos j) (t j) (z j) cols (hpos j (Finset.mem_range.mp hj)), mul_pow]`.

Simplify using `only [map_pow]`. Unfold `localizer`. Rewrite using `[piMinor_map H (pos 0) (t 0) (z 0) _ (hpos 0 hJ)]`. Distinguish the cases in `h0 : (H.submatrix id (Fin.castLE h)).det = 0`. Rewrite using `[h0, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), map_zero, mul_zero, zero_mul]`.

Take `⟨i, c, hc, hI⟩` from `graphMinor F r k h H h0 hH`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Apply `Finset.prod_eq_zero (Finset.mem_univ ((i, ⟨c, hc⟩) : IIdx r k))` to reduce the goal to its premises. Rewrite using `[hfac, hfac, ← mul_sub, ← map_sub, hexp _ h0, hexp _ hI, sub_self, map_zero, mul_zero]`.
-/
theorem localizerVanishes : Formalism.CountingSumsFrames.LocalizerVanishes := by
  intro p _ F _ _ _ n' r k J h hcard z hz hzJ pos hpos H hH A _ _ t
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  have hp1 : ∀ m, 1 ≤ p ^ m := fun m => Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hJ : 0 < J := by
    by_contra hJ0
    have hJ' : J = 0 := by omega
    subst hJ'
    have hn : n' = 0 := by omega
    rw [hn, pow_zero] at hcard
    have h1 := Fintype.one_lt_card (α := F)
    omega
  have hsum : ∑ j ∈ Finset.range J, p ^ z j * (p ^ (z (j + 1) - z j) - 1) = p ^ z 0 * (p ^ n' - 1) := by
    have h1 := (locTelescope p J n' z hz hzJ).1
    have h2 : ((∑ j ∈ Finset.range J, p ^ z j * (p ^ (z (j + 1) - z j) - 1) : ℕ) : ℤ) =
        ((p ^ z 0 * (p ^ n' - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Finset.sum_congr rfl fun j _ => by
        rw [Nat.cast_mul, Nat.cast_sub (hp1 _), Nat.cast_pow, Nat.cast_pow, Nat.cast_one]]
      rw [Nat.cast_mul, Nat.cast_sub (hp1 _), Nat.cast_pow, Nat.cast_pow, Nat.cast_one]
      exact h1
    exact_mod_cast h2
  have hexp : ∀ x : F, x ≠ 0 →
      ∏ j ∈ Finset.range J, (x ^ p ^ z j) ^ (p ^ (z (j + 1) - z j) - 1) = 1 := by
    intro x hx
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, hsum, pow_mul, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one _ (pow_ne_zero _ hx)
  have hfac : ∀ cols : Fin r → Fin k,
      ∏ j ∈ Finset.range J, piMinor p r k (H.map (algebraMap F A)) (pos j) (t j) (z j) cols ^
        (p ^ (z (j + 1) - z j) - 1) =
      (∏ j ∈ Finset.range J, (Matrix.of fun l m => t j l m ^ p ^ (z j - pos j l)).det ^
        (p ^ (z (j + 1) - z j) - 1)) *
      algebraMap F A (∏ j ∈ Finset.range J, ((H.submatrix id cols).det ^ p ^ z j) ^
        (p ^ (z (j + 1) - z j) - 1)) := by
    intro cols
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [piMinor_map H (pos j) (t j) (z j) cols (hpos j (Finset.mem_range.mp hj)), mul_pow]
    simp only [map_pow]
  unfold localizer
  rw [piMinor_map H (pos 0) (t 0) (z 0) _ (hpos 0 hJ)]
  by_cases h0 : (H.submatrix id (Fin.castLE h)).det = 0
  · rw [h0, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), map_zero, mul_zero, zero_mul]
  · obtain ⟨i, c, hc, hI⟩ := graphMinor F r k h H h0 hH
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ ((i, ⟨c, hc⟩) : IIdx r k))
    rw [hfac, hfac, ← mul_sub, ← map_sub, hexp _ h0, hexp _ hI, sub_self, map_zero, mul_zero]
/- English proof (translation)
Introduce `R _ ι _ _ J Del piI Q hJ`. Establish `h0J : 0 ∈ Finset.range J` using `Finset.mem_range.mpr (by omega)`. Establish `hexp : ∀ S : Finset ι, ∏ j ∈ Finset.range J, Del j ^ ((if j = 0 then 1 else 0) + Fintype.card ι * (Q j - 1) - S.card * (Q j - 1)) = Del 0 * (∏ j ∈ Finset.range J, Del j ^ (Q j - 1)) ^ (Fintype.card ι - S.card)`. Introduce `S`. Establish `hS : S.card ≤ Fintype.card ι` using `Finset.card_le_univ S`.

Establish `he : ∀ j, (if j = 0 then 1 else 0) + Fintype.card ι * (Q j - 1) - S.card * (Q j - 1) = (if j = 0 then 1 else 0) + (Q j - 1) * (Fintype.card ι - S.card)`. Introduce `j`. Establish `h1 : S.card * (Q j - 1) ≤ Fintype.card ι * (Q j - 1)` using `Nat.mul_le_mul_right _ hS`. Rewrite using `[Nat.add_sub_assoc h1, ← Nat.sub_mul, mul_comm]`. Simplify using `only [he, pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_pow]`.

Use `congr 1`. Rewrite using `[Finset.prod_eq_single_of_mem 0 h0J (fun j _ hj => by simp [hj])]`. Simplify using the standard rewrite rules. Establish `hprod : ∏ I, (∏ j ∈ Finset.range J, Del j ^ (Q j - 1) - ∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)) = ∑ S ∈ (Finset.univ : Finset ι).powerset, (∏ I ∈ S, -(∏ j ∈ Finset.range J, piI I j ^ (Q j - 1))) * ∏ I ∈ Finset.univ \ S, ∏ j ∈ Finset.range J, Del j ^ (Q j - 1)`. Rewrite using `[← Finset.prod_add]`.

Conclude with `Finset.prod_congr rfl fun I _ => by ring`. Rewrite using `[hprod, Finset.mul_sum, Finset.powerset_univ]`. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Establish `hneg : ∏ I ∈ S, -(∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)) = (-1) ^ S.card * ∏ I ∈ S, ∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)`. Rewrite using `[← Finset.prod_const, ← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl fun _ _ => by ring`. Rewrite using `[hexp S, hneg, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locExpand : Formalism.CountingSumsFrames.LocExpand := by
  intro R _ ι _ _ J Del piI Q hJ
  classical
  have h0J : 0 ∈ Finset.range J := Finset.mem_range.mpr (by omega)
  have hexp : ∀ S : Finset ι, ∏ j ∈ Finset.range J, Del j ^ ((if j = 0 then 1 else 0) +
      Fintype.card ι * (Q j - 1) - S.card * (Q j - 1)) =
      Del 0 * (∏ j ∈ Finset.range J, Del j ^ (Q j - 1)) ^ (Fintype.card ι - S.card) := by
    intro S
    have hS : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    have he : ∀ j, (if j = 0 then 1 else 0) + Fintype.card ι * (Q j - 1) - S.card * (Q j - 1) =
        (if j = 0 then 1 else 0) + (Q j - 1) * (Fintype.card ι - S.card) := by
      intro j
      have h1 : S.card * (Q j - 1) ≤ Fintype.card ι * (Q j - 1) := Nat.mul_le_mul_right _ hS
      rw [Nat.add_sub_assoc h1, ← Nat.sub_mul, mul_comm]
    simp only [he, pow_add, pow_mul, Finset.prod_mul_distrib, Finset.prod_pow]
    congr 1
    rw [Finset.prod_eq_single_of_mem 0 h0J (fun j _ hj => by simp [hj])]
    simp
  have hprod : ∏ I, (∏ j ∈ Finset.range J, Del j ^ (Q j - 1) -
      ∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset, (∏ I ∈ S, -(∏ j ∈ Finset.range J, piI I j ^ (Q j - 1))) *
        ∏ I ∈ Finset.univ \ S, ∏ j ∈ Finset.range J, Del j ^ (Q j - 1) := by
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun I _ => by ring
  rw [hprod, Finset.mul_sum, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hneg : ∏ I ∈ S, -(∏ j ∈ Finset.range J, piI I j ^ (Q j - 1)) =
      (-1) ^ S.card * ∏ I ∈ S, ∏ j ∈ Finset.range J, piI I j ^ (Q j - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun _ _ => by ring
  rw [hexp S, hneg, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  ring
/- English proof (translation)
Introduce `R _ r ts T`. Establish `hsub : ∀ (u : R) (b : Fin r → R) (i : Fin (r + 1)), (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove = (borderedMatrix r ts 0 T 0).submatrix i.succAbove (Fin.last r).succAbove`. Introduce `u b i`. Use extensionality with `x y`. Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last, borderedMatrix, Matrix.of_apply]`.

Apply the tactic sequence `rcases Fin.eq_zero_or_eq_succ (i.succAbove x) with h | ⟨j, h⟩ <;> rw [h] <;> simp`. Establish `h0 : ∀ (u : R) (b : Fin r → R), (borderedMatrix r ts u T b).submatrix (0 : Fin (r + 1)).succAbove (Fin.last r).succAbove = T`. Introduce `u b`. Use extensionality with `x y`. Simplify using `[borderedMatrix, Fin.succAbove_last]`.

Use `⟨fun l => (-1) ^ ((l.succ : ℕ) + (Fin.last r : ℕ)) * ((borderedMatrix r ts 0 T 0).submatrix l.succ.succAbove (Fin.last r).succAbove).det, fun u b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ, h0]`. Simplify using `only [hsub u b]`. Simplify using `only [borderedMatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.snoc_last, Fin.val_zero, Fin.val_last, zero_add]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem borderedDetLinear : Formalism.CountingSumsFrames.BorderedDetLinear := by
  intro R _ r ts T
  have hsub : ∀ (u : R) (b : Fin r → R) (i : Fin (r + 1)),
      (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove =
        (borderedMatrix r ts 0 T 0).submatrix i.succAbove (Fin.last r).succAbove := by
    intro u b i
    ext x y
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, borderedMatrix, Matrix.of_apply]
    rcases Fin.eq_zero_or_eq_succ (i.succAbove x) with h | ⟨j, h⟩ <;> rw [h] <;> simp
  have h0 : ∀ (u : R) (b : Fin r → R),
      (borderedMatrix r ts u T b).submatrix (0 : Fin (r + 1)).succAbove (Fin.last r).succAbove = T := by
    intro u b
    ext x y
    simp [borderedMatrix, Fin.succAbove_last]
  refine ⟨fun l => (-1) ^ ((l.succ : ℕ) + (Fin.last r : ℕ)) *
    ((borderedMatrix r ts 0 T 0).submatrix l.succ.succAbove (Fin.last r).succAbove).det, fun u b => ?_⟩
  rw [Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ, h0]
  simp only [hsub u b]
  simp only [borderedMatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.snoc_last, Fin.val_zero,
    Fin.val_last, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring
/- English proof (translation)
Introduce `R _ r T s a`. Combine the equalities or inequalities in the displayed calculation. Consider the case `(rw [Matrix.smul_mulVec, Matrix.one_mulVec]; rfl)`. Consider the case `(rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)`. Consider the case `simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.smul_apply]`.

Use `_ = Matrix.mulVec (T.adjugate * T) s a := by rw [Matrix.adjugate_mul]`. Use `_ = Matrix.mulVec T.adjugate (Matrix.mulVec T s) a := by rw [Matrix.mulVec_mulVec]`. Use `_ = ∑ l, Matrix.mulVec T s l * T.adjugate a l := by`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`.
-/
theorem detMulEqSumAdjugate : Formalism.CountingSumsFrames.DetMulEqSumAdjugate := by
  intro R _ r T s a
  calc T.det * s a = Matrix.mulVec (T.det • (1 : Matrix (Fin r) (Fin r) R)) s a := by
        first
          | (rw [Matrix.smul_mulVec, Matrix.one_mulVec]; rfl)
          | (rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)
          | simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.smul_apply]
    _ = Matrix.mulVec (T.adjugate * T) s a := by rw [Matrix.adjugate_mul]
    _ = Matrix.mulVec T.adjugate (Matrix.mulVec T s) a := by rw [Matrix.mulVec_mulVec]
    _ = ∑ l, Matrix.mulVec T s l * T.adjugate a l := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
/- English proof (translation)
Introduce `p _ F _ _ r k h hdet s`. Use `haveI : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)`. Establish `hpne : ∀ n, p ^ n ≠ 0` using `fun n => pow_ne_zero _ (Fact.out : p.Prime).ne_zero`. Establish `hHmap : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h`. Use extensionality with `i j`.

Simplify using `[iterateFrobenius_def]`. Establish `hHdet : IsUnit (h.map (fun x => x ^ p ^ s)).det`. Rewrite using `[hHmap, ← RingHom.map_det]`. Conclude with `hdet.map _`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `A t cols hA ht`. Set `T' : Matrix (Fin (r + 1)) (Fin k) F` to `Matrix.of fun l i => t l i ^ p ^ (s - A l)`. Set `P : Matrix (Fin k) (Fin k) F` to `Matrix.diagonal fun i => if i.val < r then 1 else 0`. Set `G : Matrix (Fin k) (Fin (r + 1)) F` to `Matrix.of fun i c => (h.map (fun x => x ^ p ^ s)) i (cols c)`. Establish `hz : (T' * P * G).det = 0`.

Assume the negation of the conclusion as `hne`. Establish `hrank` using `Matrix.rank_of_isUnit (T' * P * G) ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))`. Establish `h1 : (T' * P * G).rank ≤ P.rank` using `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)`. Establish `h2 : P.rank ≤ r`. Rewrite using `[Matrix.rank_diagonal]`.

Use `(Fintype.card_le_of_injective (fun i => (⟨i.1.val, by` and prove the remaining obligations. Establish `hi` using `i.2`. Assume the negation of the conclusion as `hc`. Simplify using `[hc] at hi⟩ : Fin r)) ?_).trans (Fintype.card_fin r).le`. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `using congrArg Fin.val hxy`. Rewrite `h1` using `[hrank, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.

Use `hz using 2` and compare the differences between its conclusion and the goal. Use extensionality with `l c`. Rewrite using `[Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c)]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.vecMul, dotProduct, T', P, G, Matrix.of_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < r`. Simplify using `[hi, Matrix.diagonal_apply]`. Establish `h0 : t l i = 0` using `ht l i (by omega)`. Simplify using `[hi, h0, zero_pow (hpne _)]`.

Introduce `a t v ha ht hv`. Establish `hrow : ∀ c, ((Matrix.vecMul t (h.map fun x => x ^ p ^ a)) c) ^ p ^ (s - a) = Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s) c` using `fun c => frob_row h a s ha t c`. Repeatedly rewrite using `[hrow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hHdet, Matrix.vecMul_one]`.

Use `_ = 0 := by`. Simplify using `only [dotProduct]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < r`. Simplify using `[hv i hi]`.

Simplify using `[ht i (by omega), zero_pow (hpne _)]`.
-/
theorem keyVanish : Formalism.CountingSumsFrames.KeyVanish := by
  intro p _ F _ _ r k h hdet s
  classical
  haveI : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)
  have hpne : ∀ n, p ^ n ≠ 0 := fun n => pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hHmap : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h := by
    ext i j
    simp [iterateFrobenius_def]
  have hHdet : IsUnit (h.map (fun x => x ^ p ^ s)).det := by
    rw [hHmap, ← RingHom.map_det]
    exact hdet.map _
  refine ⟨?_, ?_⟩
  · intro A t cols hA ht
    let T' : Matrix (Fin (r + 1)) (Fin k) F := Matrix.of fun l i => t l i ^ p ^ (s - A l)
    let P : Matrix (Fin k) (Fin k) F := Matrix.diagonal fun i => if i.val < r then 1 else 0
    let G : Matrix (Fin k) (Fin (r + 1)) F := Matrix.of fun i c => (h.map (fun x => x ^ p ^ s)) i (cols c)
    have hz : (T' * P * G).det = 0 := by
      by_contra hne
      have hrank := Matrix.rank_of_isUnit (T' * P * G)
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
      have h1 : (T' * P * G).rank ≤ P.rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      have h2 : P.rank ≤ r := by
        rw [Matrix.rank_diagonal]
        refine (Fintype.card_le_of_injective
          (fun i => (⟨i.1.val, by
            have hi := i.2
            by_contra hc
            simp [hc] at hi⟩ : Fin r)) ?_).trans (Fintype.card_fin r).le
        intro x y hxy
        apply Subtype.ext
        apply Fin.ext
        simpa using congrArg Fin.val hxy
      rw [hrank, Fintype.card_fin] at h1
      omega
    convert hz using 2
    ext l c
    rw [Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c)]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.vecMul, dotProduct, T', P, G, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < r
    · simp [hi, Matrix.diagonal_apply]
    · have h0 : t l i = 0 := ht l i (by omega)
      simp [hi, h0, zero_pow (hpne _)]
  · intro a t v ha ht hv
    have hrow : ∀ c, ((Matrix.vecMul t (h.map fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
        Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s) c :=
      fun c => frob_row h a s ha t c
    simp_rw [hrow]
    calc ∑ c, Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s) c *
          Matrix.vecMul v (Matrix.transpose (h.map fun x => x ^ p ^ s)⁻¹) c
        = dotProduct (Matrix.vecMul (fun i => t i ^ p ^ (s - a)) (h.map fun x => x ^ p ^ s))
            (Matrix.vecMul v (Matrix.transpose (h.map fun x => x ^ p ^ s)⁻¹)) := rfl
      _ = dotProduct (fun i => t i ^ p ^ (s - a)) v := by
          rw [Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
            Matrix.mul_nonsing_inv _ hHdet, Matrix.vecMul_one]
      _ = 0 := by
          simp only [dotProduct]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i.val < r
          · simp [hv i hi]
          · simp [ht i (by omega), zero_pow (hpne _)]
/- English proof (translation)
Introduce `M _ Deg FF FF' hFF hFF' τ level spare sym raw o c' Q hdeg hsym hraw hstep S hS`. Establish `key : ∀ n : ℕ, ∀ x : τ, o + c' - level x ≤ n → o ≤ level x → (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - level x) ≤ (spare x).1 → ((o : ℤ) + c' - 1 - level x) ≤ (spare x).2 → ∃ g ∈ Deg, g - sym x ∈ FF (o + c') ∧ g ∈ FF' (o + c')`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `x hn ho h1 h2`. Distinguish the cases in `hl : level x < o + c'`. Take `⟨ch, ρ, hρ, hρd, heq, hch⟩` from `hstep x hl h1 h2`. Establish `hy : ∀ y ∈ ch, ∃ g ∈ Deg, g - sym y ∈ FF (o + c') ∧ g ∈ FF' (o + c')`. Introduce `y hy`.

Take `⟨hxy, hyo, hsp⟩` from `hch y hy`. Use `ih (o + c' - level y) (by omega) y le_rfl (by omega) ?_ ?_` and prove the remaining obligations. Simplify using `only [hsp]`. Move the coercions through the operations in `at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [hsp]`. Move the coercions through the operations in `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose! gy hgyD hgyF hgyF' using hy`. Use `⟨raw x - ∑ y ∈ ch, gy y, Deg.sub_mem (hdeg x).2 (sum_mem fun y hy => hgyD y hy), ?_, ?_⟩` and prove the remaining obligations.

Establish `hrw : raw x - ∑ y ∈ ch, gy y - sym x = ρ - ∑ y ∈ ch, (gy y - sym y)`. Rewrite using `[Finset.sum_sub_distrib]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hrw]`. Conclude with `(FF (o + c')).sub_mem hρ (sum_mem fun y hy => hgyF y hy)`.

Conclude with `(FF' (o + c')).sub_mem (hFF' (by omega : o + c' ≤ level x + c') (hraw x)) (sum_mem fun y hy => hgyF' y hy)`. Use `⟨0, Deg.zero_mem, ?_, (FF' (o + c')).zero_mem⟩` and prove the remaining obligations. Rewrite using `[zero_sub]`. Conclude with `(FF (o + c')).neg_mem (hFF (by omega : o + c' ≤ level x) (hsym x))`. Establish `hinit : ∀ x ∈ S, ∃ g ∈ Deg, g - sym x ∈ FF (o + c') ∧ g ∈ FF' (o + c')`.

Introduce `x hx`. Take `⟨ho, hsp⟩` from `hS x hx`. Establish `hoz : (o : ℤ) ≤ level x` using `by exact_mod_cast ho`. Use `key _ x le_rfl ho ?_ ?_` and prove the remaining obligations. Simplify using `only [hsp]`.

Use `push_cast`. Use polynomial arithmetic with `[mul_nonneg (show (0 : ℤ) ≤ 2 * Q + 1 by positivity) (show (0 : ℤ) ≤ level x - o by linarith), (show (0 : ℤ) ≤ Q by positivity), (show (0 : ℤ) ≤ c' by positivity)]`. Simplify using `only [hsp]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `choose! g hgD hgF hgF' using hinit`. Use `⟨∑ x ∈ S, g x, sum_mem fun x hx => hgD x hx, ?_, sum_mem fun x hx => hgF' x hx⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `sum_mem fun x hx => hgF x hx`.
-/
theorem cleanInduction : Formalism.CountingSumsFrames.CleanInduction := by
  intro M _ Deg FF FF' hFF hFF' τ level spare sym raw o c' Q hdeg hsym hraw hstep S hS
  classical
  have key : ∀ n : ℕ, ∀ x : τ, o + c' - level x ≤ n → o ≤ level x →
      (2 * (Q : ℤ) + 1) * ((o : ℤ) + c' - 1 - level x) ≤ (spare x).1 →
      ((o : ℤ) + c' - 1 - level x) ≤ (spare x).2 →
      ∃ g ∈ Deg, g - sym x ∈ FF (o + c') ∧ g ∈ FF' (o + c') := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hn ho h1 h2
      by_cases hl : level x < o + c'
      · obtain ⟨ch, ρ, hρ, hρd, heq, hch⟩ := hstep x hl h1 h2
        have hy : ∀ y ∈ ch, ∃ g ∈ Deg, g - sym y ∈ FF (o + c') ∧ g ∈ FF' (o + c') := by
          intro y hy
          obtain ⟨hxy, hyo, hsp⟩ := hch y hy
          refine ih (o + c' - level y) (by omega) y le_rfl (by omega) ?_ ?_
          · simp only [hsp]
            push_cast at h1 ⊢
            linarith
          · simp only [hsp]
            push_cast at h2 ⊢
            linarith
        choose! gy hgyD hgyF hgyF' using hy
        refine ⟨raw x - ∑ y ∈ ch, gy y, Deg.sub_mem (hdeg x).2 (sum_mem fun y hy => hgyD y hy), ?_, ?_⟩
        · have hrw : raw x - ∑ y ∈ ch, gy y - sym x = ρ - ∑ y ∈ ch, (gy y - sym y) := by
            rw [Finset.sum_sub_distrib]
            calc raw x - ∑ y ∈ ch, gy y - sym x = (raw x - sym x) - ∑ y ∈ ch, gy y := by abel
              _ = (∑ y ∈ ch, sym y + ρ) - ∑ y ∈ ch, gy y := by rw [heq]
              _ = ρ - (∑ y ∈ ch, gy y - ∑ y ∈ ch, sym y) := by abel
          rw [hrw]
          exact (FF (o + c')).sub_mem hρ (sum_mem fun y hy => hgyF y hy)
        · exact (FF' (o + c')).sub_mem (hFF' (by omega : o + c' ≤ level x + c') (hraw x))
            (sum_mem fun y hy => hgyF' y hy)
      · refine ⟨0, Deg.zero_mem, ?_, (FF' (o + c')).zero_mem⟩
        rw [zero_sub]
        exact (FF (o + c')).neg_mem (hFF (by omega : o + c' ≤ level x) (hsym x))
  have hinit : ∀ x ∈ S, ∃ g ∈ Deg, g - sym x ∈ FF (o + c') ∧ g ∈ FF' (o + c') := by
    intro x hx
    obtain ⟨ho, hsp⟩ := hS x hx
    have hoz : (o : ℤ) ≤ level x := by exact_mod_cast ho
    refine key _ x le_rfl ho ?_ ?_
    · simp only [hsp]
      push_cast
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * Q + 1 by positivity) (show (0 : ℤ) ≤ level x - o by linarith),
        (show (0 : ℤ) ≤ Q by positivity), (show (0 : ℤ) ≤ c' by positivity)]
    · simp only [hsp]
      push_cast
      linarith
  choose! g hgD hgF hgF' using hinit
  refine ⟨∑ x ∈ S, g x, sum_mem fun x hx => hgD x hx, ?_, sum_mem fun x hx => hgF' x hx⟩
  rw [← Finset.sum_sub_distrib]
  exact sum_mem fun x hx => hgF x hx
/- English proof (translation)
Use `⟨fun j v o e' Q h1 h2 h3 => by nlinarith, fun e c' Q h => ⟨by nlinarith, by omega⟩⟩` and prove the remaining obligations.
-/
theorem cleanArith : Formalism.CountingSumsFrames.CleanArith := by
  refine ⟨fun j v o e' Q h1 h2 h3 => by nlinarith, fun e c' Q h => ⟨by nlinarith, by omega⟩⟩
/- English proof (translation)
Introduce `R _ D h π P n c hP`. Rewrite using `[add_pow]`. Use `Ideal.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Distinguish the cases in `hc : c ≤ n - j`. Apply `Ideal.mem_sup_right` to reduce the goal to its premises.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Rewrite using `[mul_pow]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Conclude with `Ideal.mem_span_singleton.mpr (pow_dvd_pow π hc)`.

Apply `Ideal.mem_sup_left` to reduce the goal to its premises. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton, ← pow_mul]`. Establish `hjP : j ≤ P * j` using `Nat.le_mul_of_pos_left j hP`.

Conclude with `pow_dvd_pow D (by omega)`.
-/
theorem powerSplit : Formalism.CountingSumsFrames.PowerSplit := by
  intro R _ D h π P n c hP
  rw [add_pow]
  refine Ideal.sum_mem _ fun j hj => ?_
  by_cases hc : c ≤ n - j
  · apply Ideal.mem_sup_right
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_left
    rw [mul_pow]
    apply Ideal.mul_mem_right
    exact Ideal.mem_span_singleton.mpr (pow_dvd_pow π hc)
  · apply Ideal.mem_sup_left
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_right
    rw [Ideal.mem_span_singleton, ← pow_mul]
    have hjP : j ≤ P * j := Nat.le_mul_of_pos_left j hP
    exact pow_dvd_pow D (by omega)
/- English proof (translation)
Introduce `p a B D0 S d hp ha hB hS`. Establish `hp0 : 0 < p` using `by linarith`. Establish `hp2 : 168 ≤ p ^ 2 - 1` using `by nlinarith`. Establish `hB0 : 0 ≤ B` using `le_trans (by positivity) hB`. Establish `hx0 : 0 ≤ 1 / p ^ 2` using `by positivity`.

Establish `hx1 : 1 / p ^ 2 < 1` using `by rw [div_lt_one (by positivity)]; nlinarith`. Establish `hterm : ∀ m ∈ S, d m ≤ 2.02 * B * (1 / p ^ 2) ^ m`. Introduce `m hm`. Take `⟨_, _, hdm⟩` from `hS m hm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_add, pow_mul, one_div_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 2.02 * B * (1 / p ^ 2) ^ m := by gcongr`. Establish `h0S : 0 ∉ S` using `fun h => by have := (hS 0 h).1; omega`. Establish `hgeom : ∑ m ∈ S, (1 / p ^ 2) ^ m ≤ 1 / (p ^ 2 - 1)`.

Establish `hsum` using `summable_geometric_of_lt_one hx0 hx1`. Establish `h1 : ∑ m ∈ insert 0 S, (1 / p ^ 2) ^ m ≤ ∑' m : ℕ, (1 / p ^ 2) ^ m` using `by first`. Consider the case `exact hsum.sum_le_tsum _ (fun m _ => pow_nonneg hx0 m)`. Consider the case `exact sum_le_tsum _ (fun m _ => pow_nonneg hx0 m) hsum`. Rewrite `h1` using `[Finset.sum_insert h0S, pow_zero, tsum_geometric_of_lt_one hx0 hx1]`.

Establish `h2 : (1 - 1 / p ^ 2)⁻¹ - 1 = 1 / (p ^ 2 - 1)`. Establish `hp2' : p ^ 2 - 1 ≠ 0` using `by linarith`. Establish `hp2'' : p ^ 2 ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_div_iff₀ (by linarith) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lemma4Geom : Formalism.CountingSumsFrames.Lemma4Geom := by
  intro p a B D0 S d hp ha hB hS
  have hp0 : 0 < p := by linarith
  have hp2 : 168 ≤ p ^ 2 - 1 := by nlinarith
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have hx0 : 0 ≤ 1 / p ^ 2 := by positivity
  have hx1 : 1 / p ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have hterm : ∀ m ∈ S, d m ≤ 2.02 * B * (1 / p ^ 2) ^ m := by
    intro m hm
    obtain ⟨_, _, hdm⟩ := hS m hm
    calc d m ≤ 2.02 * a / p ^ (D0 + 2 * m) := hdm
      _ = 2.02 * (a / p ^ D0) * (1 / p ^ 2) ^ m := by
          rw [pow_add, pow_mul, one_div_pow]
          ring
      _ ≤ 2.02 * B * (1 / p ^ 2) ^ m := by gcongr
  have h0S : 0 ∉ S := fun h => by have := (hS 0 h).1; omega
  have hgeom : ∑ m ∈ S, (1 / p ^ 2) ^ m ≤ 1 / (p ^ 2 - 1) := by
    have hsum := summable_geometric_of_lt_one hx0 hx1
    have h1 : ∑ m ∈ insert 0 S, (1 / p ^ 2) ^ m ≤ ∑' m : ℕ, (1 / p ^ 2) ^ m := by
      first
        | exact hsum.sum_le_tsum _ (fun m _ => pow_nonneg hx0 m)
        | exact sum_le_tsum _ (fun m _ => pow_nonneg hx0 m) hsum
    rw [Finset.sum_insert h0S, pow_zero, tsum_geometric_of_lt_one hx0 hx1] at h1
    have h2 : (1 - 1 / p ^ 2)⁻¹ - 1 = 1 / (p ^ 2 - 1) := by
      have hp2' : p ^ 2 - 1 ≠ 0 := by linarith
      have hp2'' : p ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    linarith
  refine ⟨?_, ?_⟩
  · calc ∑ m ∈ S, d m ≤ ∑ m ∈ S, 2.02 * B * (1 / p ^ 2) ^ m := Finset.sum_le_sum hterm
      _ = 2.02 * B * ∑ m ∈ S, (1 / p ^ 2) ^ m := by rw [Finset.mul_sum]
      _ ≤ 2.02 * B * (1 / (p ^ 2 - 1)) := by gcongr
      _ = 2.02 * B / (p ^ 2 - 1) := by ring
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
/- English proof (translation)
Introduce `B B' sl mstar val h0 h1 h2 h3 h4`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem lemma4Arith : Formalism.CountingSumsFrames.Lemma4Arith := by
  intro B B' sl mstar val h0 h1 h2 h3 h4
  constructor <;> linarith
/- English proof (translation)
Introduce `N1 ntops m kQ c' al h`. Establish `h1` using `Nat.mul_le_mul_right (m + kQ + c') h`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lemma4Count : Formalism.CountingSumsFrames.Lemma4Count := by
  intro N1 ntops m kQ c' al h
  have h1 := Nat.mul_le_mul_right (m + kQ + c') h
  calc ntops * (m + kQ + c') + (c' * al + 2 * c') ≤ N1 * (m + kQ + c') + (c' * al + 2 * c') :=
        Nat.add_le_add_right h1 _
    _ ≤ N1 * (m + kQ + c') + (c' * al + 2 * c') + (N1 * (c' * al + 2 * c') + (m + kQ + c')) :=
        Nat.le_add_right _ _
    _ = (N1 + 1) * (m + kQ + c' * al + 3 * c') := by ring
/- English proof (translation)
Introduce `p _ σ Z _ _ _ _ letter d N k a ha hcard hd F hF`. Establish `hc` using `fun α (hα : α ∈ F.support) => fock_core p letter d N k a ha hcard hd α (hF α hα)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `vBB`. Apply `Finset.le_inf` to reduce the goal to its premises.

Introduce `α hα`. Establish `h2` using `(hc α hα).2`. Establish `hle : vG p F ≤ (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ)`. Unfold `vG`. Conclude with `Finset.inf_le hα`.

Use `le_trans (add_le_add hle le_rfl) ?_` and prove the remaining obligations. Rewrite using `[← WithTop.coe_add, WithTop.coe_le_coe]`. Move the coercions through the operations in `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `vBB`.

Break down `F.support.eq_empty_or_nonempty with hs | hs` into its components or cases. Simplify using `[vG, hs]`. Take `⟨α, hα, heq⟩` from `Finset.exists_mem_eq_inf F.support hs (fun α => (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ))`. Establish `hvg : vG p F = (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ)` using `heq`. Rewrite using `[hvg, ← WithTop.coe_add]`.

Use `le_trans (Finset.inf_le hα) ?_` and prove the remaining obligations. Rewrite using `[WithTop.coe_le_coe]`. Establish `h1` using `(hc α hα).1`. Establish `h3 : (padicValNat p (factProd α) : ℝ) ≤ padicValNat p (∏ z, (d z).factorial)`. Conclude with `h1` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fockGauss : Formalism.CountingSumsFrames.FockGauss := by
  intro p _ σ Z _ _ _ _ letter d N k a ha hcard hd F hF
  have hc := fun α (hα : α ∈ F.support) => fock_core p letter d N k a ha hcard hd α (hF α hα)
  refine ⟨?_, ?_⟩
  · unfold vBB
    apply Finset.le_inf
    intro α hα
    have h2 := (hc α hα).2
    have hle : vG p F ≤ (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ) := by
      unfold vG
      exact Finset.inf_le hα
    refine le_trans (add_le_add hle le_rfl) ?_
    rw [← WithTop.coe_add, WithTop.coe_le_coe]
    push_cast at h2 ⊢
    linarith
  · unfold vBB
    rcases F.support.eq_empty_or_nonempty with hs | hs
    · simp [vG, hs]
    · obtain ⟨α, hα, heq⟩ := Finset.exists_mem_eq_inf F.support hs
        (fun α => (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ))
      have hvg : vG p F = (((padicValRat p (F.coeff α) : ℤ) : ℝ) : WithTop ℝ) := heq
      rw [hvg, ← WithTop.coe_add]
      refine le_trans (Finset.inf_le hα) ?_
      rw [WithTop.coe_le_coe]
      have h1 := (hc α hα).1
      have h3 : (padicValNat p (factProd α) : ℝ) ≤ padicValNat p (∏ z, (d z).factorial) := by
        exact_mod_cast h1
      linarith

end Formalism.CountingSumsFrames.Top
