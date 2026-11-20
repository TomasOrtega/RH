import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.NonPrimeVonMangoldt

noncomputable def F₀ (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ (3 / 4 : ℝ)

noncomputable def F₁ (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 1))

noncomputable def F₂ : Nat.Primes × ℕ → ℝ := F₁ ∘ (Prod.map _root_.id (· + 1))

/- English proof (translation)
Simplify using `only [F₂, Function.comp_apply, F₁, F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left, zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop, vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm, Nat.cast_pow]`.
-/
lemma F₂_eq (p : Nat.Primes) (k : ℕ) :
    F₂ (p, k) = Real.log p / ((p : ℝ) ^ (k + 2)) ^ (3 / 4 : ℝ) := by
  simp only [F₂, Function.comp_apply, F₁, F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm, Nat.cast_pow]

/- English proof (translation)
Rewrite using `[F₂_eq]`. Establish `hp : (0 : ℝ) < ((p : ℕ) : ℝ)` using `Nat.cast_pos.mpr p.prop.pos`. Establish `h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ)` using `Nat.ofNat_le_cast.mpr p.prop.two_le`. Use `set x : ℝ := ((p : ℕ) : ℝ) with hx`. Establish `h1 : Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4)` using `Real.log_le_rpow_div hp.le (by norm_num)`.

Establish `h3 : x ^ (-(3 / 4) : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4) : ℝ)` using `Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by norm_num)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le, ← Real.rpow_add hp, div_div, mul_comm (1 / 4 : ℝ), ← div_div, ← Real.rpow_sub hp]`. Establish `: (1 / 4 : ℝ) - ((k + 2 : ℕ) : ℝ) * (3 / 4) = -(5 / 4) + -(3 / 4) * (k : ℝ)` using `by push_cast; ring`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by gcongr`.
-/
lemma F₂_le (p : Nat.Primes) (k : ℕ) :
    F₂ (p, k) ≤ 4 * (((p : ℕ) : ℝ) ^ (-(5 / 4) : ℝ) * ((2 : ℝ) ^ (-(3 / 4) : ℝ)) ^ k) := by
  rw [F₂_eq]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := Nat.cast_pos.mpr p.prop.pos
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.ofNat_le_cast.mpr p.prop.two_le
  set x : ℝ := ((p : ℕ) : ℝ) with hx
  have h1 : Real.log x ≤ x ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hp.le (by norm_num)
  have h3 : x ^ (-(3 / 4) : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by norm_num)
  calc Real.log x / (x ^ (k + 2)) ^ (3 / 4 : ℝ)
      ≤ (x ^ (1 / 4 : ℝ) / (1 / 4)) / (x ^ (k + 2)) ^ (3 / 4 : ℝ) := by gcongr
    _ = 4 * (x ^ (-(5 / 4) : ℝ) * (x ^ (-(3 / 4) : ℝ)) ^ k) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp.le,
          ← Real.rpow_mul hp.le, ← Real.rpow_add hp, div_div, mul_comm (1 / 4 : ℝ), ← div_div,
          ← Real.rpow_sub hp]
        have : (1 / 4 : ℝ) - ((k + 2 : ℕ) : ℝ) * (3 / 4) = -(5 / 4) + -(3 / 4) * (k : ℝ) := by
          push_cast; ring
        rw [this]; ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4) : ℝ)` using `by positivity`. Establish `hr1 : (2 : ℝ) ^ (-(3 / 4) : ℝ) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)`. Establish `hA : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(5 / 4) : ℝ)` using `Nat.Primes.summable_rpow.mpr (by norm_num)`. Establish `hB` using `summable_geometric_of_lt_one hr0 hr1`. Establish `hAB` using `Summable.mul_of_nonneg hA hB (fun p => by positivity) (fun k => by positivity)`.

Use `(hAB.mul_left 4).of_nonneg_of_le (fun pk => ?_) (fun pk => F₂_le pk.1 pk.2)` and prove the remaining obligations. Take `⟨p, k⟩` from `pk`. Rewrite using `[F₂_eq]`. Use `Real.log_natCast_nonneg (p : ℕ)` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma summable_F₂ : Summable F₂ := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4) : ℝ) := by positivity
  have hr1 : (2 : ℝ) ^ (-(3 / 4) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hA : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(5 / 4) : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hB := summable_geometric_of_lt_one hr0 hr1
  have hAB := Summable.mul_of_nonneg hA hB (fun p => by positivity) (fun k => by positivity)
  refine (hAB.mul_left 4).of_nonneg_of_le (fun pk => ?_) (fun pk => F₂_le pk.1 pk.2)
  obtain ⟨p, k⟩ := pk
  rw [F₂_eq]
  have := Real.log_natCast_nonneg (p : ℕ)
  positivity

open Nat.Primes in
/- English proof (translation)
Establish `hF₀ (p : Nat.Primes) : F₀ p.val = 0`. Simplify using `only [p.prop, ↓reduceIte, zero_div, F₀]`. Use `(summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_` and prove the remaining obligations. Use `swap`. Simplify using `+contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn, not_false_eq_true, implies_true, true_or, F₀]`.

Establish `hFF' : F₀ ∘ Subtype.val (p` using `fun n ↦ n ∈ {n | IsPrimePow n}) = F₁ ∘ ⇑prodNatEquiv.symm := by`. Use `(Equiv.eq_comp_symm prodNatEquiv (F₀ ∘ Subtype.val) F₁).mpr ?_` and prove the remaining obligations. Use `ext1 n`. Simplify using `only [Function.comp_apply, F₁]`. Reduce the equality to equality of the corresponding arguments.

Rewrite using `[hFF']`. Use `(Nat.Primes.prodNatEquiv.symm.summable_iff (f := F₁)).mpr ?_` and prove the remaining obligations. Establish `hF'₀ (p : Nat.Primes) : F₁ (p, 0) = 0` using `by simp only [zero_add, pow_one, hF₀, F₁]`. Use `(Function.Injective.summable_iff (g := Prod.map _root_.id (· + 1)) ?_ fun u hu ↦ ?_).mp summable_F₂` and prove the remaining obligations. Conclude with `Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1`.

Simplify using `only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range, Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu`. Rewrite using `[← hF'₀ u.1, ← hu]`.
-/
lemma summable_F₀ : Summable F₀ := by
  have hF₀ (p : Nat.Primes) : F₀ p.val = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F₀]
  refine (summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr
      fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_
  swap
  · simp +contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn,
      not_false_eq_true, implies_true, true_or, F₀]
  have hFF' :
      F₀ ∘ Subtype.val (p := fun n ↦ n ∈ {n | IsPrimePow n}) = F₁ ∘ ⇑prodNatEquiv.symm := by
    refine (Equiv.eq_comp_symm prodNatEquiv (F₀ ∘ Subtype.val) F₁).mpr ?_
    ext1 n
    simp only [Function.comp_apply, F₁]
    congr
  rw [hFF']
  refine (Nat.Primes.prodNatEquiv.symm.summable_iff (f := F₁)).mpr ?_
  have hF'₀ (p : Nat.Primes) : F₁ (p, 0) = 0 := by simp only [zero_add, pow_one, hF₀, F₁]
  refine (Function.Injective.summable_iff (g := Prod.map _root_.id (· + 1)) ?_ fun u hu ↦ ?_).mp
    summable_F₂
  · exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1
  · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
      Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hF'₀ u.1, ← hu]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
/- English proof (translation)
Establish `hP0 : 0 < P` using `by linarith`. Establish `hA : 0 < P ^ (3 / 2 : ℝ)` using `Real.rpow_pos_of_pos hP0 _`. Establish `hC : 0 < ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k` using `by positivity`. Establish `hCB : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k ≤ (P ^ (3 / 4 : ℝ)) ^ k` using `pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hP (by norm_num)) k`. Establish `hsplit : (P ^ (k + 2)) ^ (3 / 4 : ℝ) = P ^ (3 / 2 : ℝ) * (P ^ (3 / 4 : ℝ)) ^ k`.

Rewrite using `[← Real.rpow_pow_comm hP0.le, pow_add, mul_comm, ← Real.rpow_natCast (P ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hP0.le]`. Evaluate the numerical expressions. Establish `hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ)`. Use `Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 4 by norm_num)` as an intermediate fact. Combine the linear relations using `[show P ^ (1 / 4 : ℝ) / (1 / 4) = 4 * P ^ (1 / 4 : ℝ) by ring]`.

Establish `hrhs : 4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k = 4 * P ^ (1 / 4 : ℝ) / (P ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k)`. Rewrite using `[show (-(5 / 4 : ℝ)) = 1 / 4 - 3 / 2 by norm_num, Real.rpow_sub hP0, Real.rpow_neg (by norm_num), inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsplit, hrhs]`. Conclude with `div_le_div₀ (by positivity) hlog (mul_pos hA hC) (mul_le_mul_of_nonneg_left hCB hA.le)`.
-/
private lemma log_div_pow_add_two_rpow_three_quarters_le (P : ℝ) (hP : 2 ≤ P) (k : ℕ) :
    Real.log P / (P ^ (k + 2)) ^ (3 / 4 : ℝ) ≤
      4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  have hP0 : 0 < P := by linarith
  have hA : 0 < P ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hP0 _
  have hC : 0 < ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k := by positivity
  have hCB : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k ≤ (P ^ (3 / 4 : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hP (by norm_num)) k
  have hsplit : (P ^ (k + 2)) ^ (3 / 4 : ℝ) = P ^ (3 / 2 : ℝ) * (P ^ (3 / 4 : ℝ)) ^ k := by
    rw [← Real.rpow_pow_comm hP0.le, pow_add, mul_comm, ← Real.rpow_natCast (P ^ (3 / 4 : ℝ)) 2,
      ← Real.rpow_mul hP0.le]
    norm_num
  have hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hP0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show P ^ (1 / 4 : ℝ) / (1 / 4) = 4 * P ^ (1 / 4 : ℝ) by ring]
  have hrhs : 4 * P ^ (-(5 / 4 : ℝ)) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k
      = 4 * P ^ (1 / 4 : ℝ) / (P ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ k) := by
    rw [show (-(5 / 4 : ℝ)) = 1 / 4 - 3 / 2 by norm_num, Real.rpow_sub hP0,
      Real.rpow_neg (by norm_num), inv_pow]
    field_simp
  rw [hsplit, hrhs]
  exact div_le_div₀ (by positivity) hlog (mul_pos hA hC) (mul_le_mul_of_nonneg_left hCB hA.le)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in

/- English proof (translation)
Use `set F := (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) with hF`. Use `set g : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 2) with hg_def`. Establish `hg : Function.Injective g`. Introduce and unpack `⟨p, k⟩ ⟨q, m⟩ h`. Take `⟨h1, h2⟩` from `Nat.Prime.pow_inj p.2 q.2 (h : (p : ℕ) ^ ((k + 1) + 1) = (q : ℕ) ^ ((m + 1) + 1))`.

Conclude with `Prod.ext (Subtype.ext h1) (by simpa using h2)`. Establish `hrange : ∀ n ∉ Set.range g, F n = 0`. Introduce `n hn`. Distinguish the cases in `hp : n.Prime`. Simplify using `[hF, hp]`.

Distinguish the cases in `hΛ : Λ n = 0`. Simplify using `[hF, hΛ]`. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Take `⟨p, k, hp', hk, rfl⟩` from `(isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)`.

Establish `hk2 : 2 ≤ k`. Assume the negation of the conclusion as `hlt`. Establish `: k = 1` using `by omega`. Substitute `this` using the available equality. Conclude with `hp (by simpa using hp')`.

Conclude with `⟨(⟨p, hp'⟩, k - 2), by simp only [hg_def]; congr 1; omega⟩`. Rewrite using `[← hg.summable_iff hrange]`. Establish `hmaj : Summable (fun pk : Nat.Primes × ℕ => (4 * ((pk.1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ pk.2)`. Use `Summable.mul_of_nonneg (f := fun p : Nat.Primes => 4 * ((p : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) (g := fun k : ℕ => ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 4`.

Conclude with `summable_geometric_of_lt_one (by positivity) (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))`. Introduce `p`. Simplify using `only [Pi.zero_apply]`. Check the signs of the components of the expression. Introduce `k`.

Simplify using `only [Pi.zero_apply]`. Check the signs of the components of the expression. Use `Summable.of_nonneg_of_le (fun pk => ?_) (fun pk => ?_) hmaj` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hF]`. Use `div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)` and prove the remaining obligations.

Use `split_ifs`. Conclude with `le_rfl`. Conclude with `vonMangoldt_nonneg`. Take `⟨⟨p, hp⟩, k⟩` from `pk`. Establish `hnp : ¬ (p ^ (k + 2)).Prime` using `Nat.Prime.not_prime_pow (by omega)`.

Simplify using `only [Function.comp_apply, hF, hg_def, if_neg hnp]`. Rewrite using `[vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Nat.cast_pow]`. Conclude with `log_div_pow_add_two_rpow_three_quarters_le _ (by exact_mod_cast hp.two_le) k`.
-/
theorem _root_.GlobalTheory.Lin.NonPrimeVonMangoldt.summable_nonPrime_vonMangoldt_div_rpow :
    Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  set F := (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) with hF
  set g : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 2) with hg_def
  have hg : Function.Injective g := by
    rintro ⟨p, k⟩ ⟨q, m⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 (h : (p : ℕ) ^ ((k + 1) + 1) = (q : ℕ) ^ ((m + 1) + 1))
    exact Prod.ext (Subtype.ext h1) (by simpa using h2)
  have hrange : ∀ n ∉ Set.range g, F n = 0 := by
    intro n hn
    by_cases hp : n.Prime
    · simp [hF, hp]
    by_cases hΛ : Λ n = 0
    · simp [hF, hΛ]
    exfalso
    apply hn
    obtain ⟨p, k, hp', hk, rfl⟩ := (isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k = 1 := by omega
      subst this
      exact hp (by simpa using hp')
    exact ⟨(⟨p, hp'⟩, k - 2), by simp only [hg_def]; congr 1; omega⟩
  rw [← hg.summable_iff hrange]
  have hmaj : Summable (fun pk : Nat.Primes × ℕ =>
      (4 * ((pk.1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) * ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ pk.2) := by
    refine Summable.mul_of_nonneg (f := fun p : Nat.Primes => 4 * ((p : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)))
      (g := fun k : ℕ => ((2 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k) ?_ ?_ ?_ ?_
    · exact (Nat.Primes.summable_rpow.2 (by norm_num)).mul_left 4
    · exact summable_geometric_of_lt_one (by positivity)
        (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    · intro p; simp only [Pi.zero_apply]; positivity
    · intro k; simp only [Pi.zero_apply]; positivity
  refine Summable.of_nonneg_of_le (fun pk => ?_) (fun pk => ?_) hmaj
  · simp only [Function.comp_apply, hF]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    split_ifs
    · exact le_rfl
    · exact vonMangoldt_nonneg
  · obtain ⟨⟨p, hp⟩, k⟩ := pk
    have hnp : ¬ (p ^ (k + 2)).Prime := Nat.Prime.not_prime_pow (by omega)
    simp only [Function.comp_apply, hF, hg_def, if_neg hnp]
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Nat.cast_pow]
    exact log_div_pow_add_two_rpow_three_quarters_le _ (by exact_mod_cast hp.two_le) k

end GlobalTheory.Lin.NonPrimeVonMangoldt
