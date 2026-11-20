import Formalism.TranslateCocycles.StatementNet
import Formalism.TranslateCocycles.TranslateCocycleProofs.TranslateScale

noncomputable section
namespace Formalism.CG
open Finset

/- English proof (translation)
The claim follows from `Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd`.
-/
theorem net_even_pred (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

/- English proof (translation)
The claim follows from `Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd`.
-/
theorem net_even_succ (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

/- English proof (translation)
Use `⟨fun k c => ⟨by ring, by ring, by ring⟩, fun k c p => by ring, fun k m => ⟨by ring, by ring, by ring⟩, fun k c hc => ?_, fun k => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩ : ∃ d, c = d + 1` from `⟨c - 1, by omega⟩`. Establish `h1` using `net_even_pred (c + 1)`. Establish `h2` using `net_even_pred k`. Establish `h3` using `net_even_succ (k + (c + 1))`.

Break down `k with _ | k` into its components or cases. Simplify using `only [Nat.add_sub_cancel, zero_add, Nat.zero_mul, Nat.zero_div, add_zero, mul_zero] at *`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [Nat.add_sub_cancel] at *`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2` using `net_even_pred k`. Establish `h3` using `net_even_succ k`. Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel] at *`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem netExponent : NetExponent := by
  refine ⟨fun k c => ⟨by ring, by ring, by ring⟩, fun k c p => by ring,
    fun k m => ⟨by ring, by ring, by ring⟩, fun k c hc => ?_, fun k => ?_⟩
  · obtain ⟨c, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    have h1 := net_even_pred (c + 1)
    have h2 := net_even_pred k
    have h3 := net_even_succ (k + (c + 1))
    rcases k with _ | k
    · simp only [Nat.add_sub_cancel, zero_add, Nat.zero_mul, Nat.zero_div, add_zero, mul_zero] at *
      nlinarith
    · simp only [Nat.add_sub_cancel] at *
      nlinarith
  · have h2 := net_even_pred k
    have h3 := net_even_succ k
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel] at *
      nlinarith

/- English proof (translation)
Introduce `Λ _ y X lg hy hs`. Break down `isEmpty_or_nonempty Λ with h | ⟨⟨w0⟩⟩` into its components or cases. Simplify using `at hs ⊢`. Establish `hc : (Fintype.card Λ : ℝ) ≠ 0`. Establish `: 0 < Fintype.card Λ` using `Fintype.card_pos_iff.mpr ⟨w0⟩`.

Check the signs of the components of the expression. Establish `h1 : ∀ w, y w = y w0` using `fun w => hy w w0`. Establish `h2 : lg = (Fintype.card Λ : ℝ) * y w0`. Rewrite using `[← hs, Finset.sum_congr rfl (fun w _ => h1 w)]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl (fun w _ => by rw [h1 w]), ← Finset.mul_sum, h2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem netUnitMean : NetUnitMean := by
  intro Λ _ y X lg hy hs
  rcases isEmpty_or_nonempty Λ with h | ⟨⟨w0⟩⟩
  · simp at hs ⊢
  · have hc : (Fintype.card Λ : ℝ) ≠ 0 := by
      have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨w0⟩
      positivity
    have h1 : ∀ w, y w = y w0 := fun w => hy w w0
    have h2 : lg = (Fintype.card Λ : ℝ) * y w0 := by
      rw [← hs, Finset.sum_congr rfl (fun w _ => h1 w)]; simp
    rw [Finset.sum_congr rfl (fun w _ => by rw [h1 w]), ← Finset.mul_sum, h2]
    field_simp

/- English proof (translation)
Introduce `ι _ P TT hT n a R1 R2 m k hm hk hmk h1 h2 hR2`. Use `set κ : ℝ := m * (1 + (m - 1) / (2 * k)) with hκ`. Establish `hq0 : 0 ≤ (m - 1) / (2 * k)` using `div_nonneg (by linarith) (by linarith)`. Establish `hq1 : (m - 1) / (2 * k) ≤ 1` using `by rw [div_le_one (by linarith)]; exact hmk`. Establish `hκ0 : 0 ≤ κ` using `by rw [hκ]; nlinarith`.

Establish `hκ2 : κ ≤ 2 * m` using `by rw [hκ]; nlinarith`. Establish `hsplit : ∑ τ ∈ P, n τ = ∑ τ ∈ P \ TT, n τ + ∑ t ∈ TT, n t` using `(Finset.sum_sdiff hT).symm`. Establish `e : (∑ τ ∈ P, n τ) * κ - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t) = κ * (∑ t ∈ TT, (n t - a t) + ∑ τ ∈ P \ TT, n τ)`. Rewrite using `[hsplit, Finset.sum_sub_distrib, hκ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `b1 : |∑ t ∈ TT, (n t - a t)| ≤ (TT.card : ℝ) * R1`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum h1).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `b2 : |∑ τ ∈ P \ TT, n τ| ≤ (P.card : ℝ) * R2`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum h2).trans ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_const, nsmul_eq_mul]`. Establish `: ((P \ TT).card : ℝ) ≤ P.card` using `by exact_mod_cast Finset.card_le_card Finset.sdiff_subset`. Conclude with `mul_le_mul_of_nonneg_right this hR2`.

Establish `b3` using `(abs_add_le (∑ t ∈ TT, (n t - a t)) (∑ τ ∈ P \ TT, n τ)).trans (add_le_add b1 b2)`. Rewrite using `[e, abs_mul, abs_of_nonneg hκ0]`. Conclude with `mul_le_mul hκ2 b3 (abs_nonneg _) (by linarith)`.
-/
theorem netReturnOfA : NetReturnOfA := by
  intro ι _ P TT hT n a R1 R2 m k hm hk hmk h1 h2 hR2
  set κ : ℝ := m * (1 + (m - 1) / (2 * k)) with hκ
  have hq0 : 0 ≤ (m - 1) / (2 * k) := div_nonneg (by linarith) (by linarith)
  have hq1 : (m - 1) / (2 * k) ≤ 1 := by rw [div_le_one (by linarith)]; exact hmk
  have hκ0 : 0 ≤ κ := by rw [hκ]; nlinarith
  have hκ2 : κ ≤ 2 * m := by rw [hκ]; nlinarith
  have hsplit : ∑ τ ∈ P, n τ = ∑ τ ∈ P \ TT, n τ + ∑ t ∈ TT, n t := (Finset.sum_sdiff hT).symm
  have e : (∑ τ ∈ P, n τ) * κ - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t)
      = κ * (∑ t ∈ TT, (n t - a t) + ∑ τ ∈ P \ TT, n τ) := by
    rw [hsplit, Finset.sum_sub_distrib, hκ]; ring
  have b1 : |∑ t ∈ TT, (n t - a t)| ≤ (TT.card : ℝ) * R1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h1).trans ?_
    simp
  have b2 : |∑ τ ∈ P \ TT, n τ| ≤ (P.card : ℝ) * R2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h2).trans ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    have : ((P \ TT).card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    exact mul_le_mul_of_nonneg_right this hR2
  have b3 := (abs_add_le (∑ t ∈ TT, (n t - a t)) (∑ τ ∈ P \ TT, n τ)).trans (add_le_add b1 b2)
  rw [e, abs_mul, abs_of_nonneg hκ0]
  exact mul_le_mul hκ2 b3 (abs_nonneg _) (by linarith)

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n]`. Establish `h1 : ∏ i ∈ range n, (q ^ n - q ^ i) = ∏ i ∈ range n, (q ^ i * (q ^ (n - i) - 1))`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ n` using `(Finset.mem_range.mp hi).le`. Rewrite using `[Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']`.

Rewrite using `[h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]`. Use `congr 1`. Establish `h2 : ∏ i ∈ range n, (q ^ (n - i) - 1) = ∏ i ∈ range n, (q ^ (i + 1) - 1)`. Rewrite using `[← Finset.prod_range_reflect]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi' : i < n` using `Finset.mem_range.mp hi`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h2, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => q ^ i - 1) 0 n 1]`. Both sides reduce to the same expression.
-/
theorem net_prod_GL (q n : ℕ) :
    ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) = q ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n]
  have h1 : ∏ i ∈ range n, (q ^ n - q ^ i) = ∏ i ∈ range n, (q ^ i * (q ^ (n - i) - 1)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i ≤ n := (Finset.mem_range.mp hi).le
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hi']
  rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
  congr 1
  have h2 : ∏ i ∈ range n, (q ^ (n - i) - 1) = ∏ i ∈ range n, (q ^ (i + 1) - 1) := by
    rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    congr 2
    omega
  rw [h2, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => q ^ i - 1) 0 n 1]
  rfl

/- English proof (translation)
Establish `h1 : ∏ i ∈ Icc 1 n, (q ^ i - 1) = ∏ i ∈ Icc 1 n, (q ^ i * (1 - (q ^ i)⁻¹))`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: q ^ i ≠ 0` using `(pow_pos hq i).ne'`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`.

Use `congr 2`. Establish `: ∑ i ∈ Icc 1 n, i = ∑ i ∈ range (n + 1), i`. Rewrite using `[Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite using `[this, Finset.sum_range_id, Nat.add_sub_cancel, mul_comm]`.
-/
theorem net_prod_real (q : ℝ) (hq : 0 < q) (n : ℕ) :
    ∏ i ∈ Icc 1 n, (q ^ i - 1) = q ^ (n * (n + 1) / 2) * ∏ i ∈ Icc 1 n, (1 - (q ^ i)⁻¹) := by
  have h1 : ∏ i ∈ Icc 1 n, (q ^ i - 1) = ∏ i ∈ Icc 1 n, (q ^ i * (1 - (q ^ i)⁻¹)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have : q ^ i ≠ 0 := (pow_pos hq i).ne'
    field_simp
  rw [h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  have : ∑ i ∈ Icc 1 n, i = ∑ i ∈ range (n + 1), i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp
    rfl
  rw [this, Finset.sum_range_id, Nat.add_sub_cancel, mul_comm]

/- English proof (translation)
Rewrite using `[Nat.cast_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ hq)]`. Simplify using the standard rewrite rules.
-/
theorem net_cast_prod (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    ((∏ i ∈ Icc 1 n, (q ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Icc 1 n, ((q : ℝ) ^ i - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  simp

/- English proof (translation)
Introduce `F _ _ n`. Establish `hq : 1 ≤ Fintype.card F` using `Fintype.card_pos`. Establish `h1 : Nat.card (GL (Fin n) F) = Fintype.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (Fintype.card F ^ i - 1)`. Rewrite using `[Matrix.card_GL_field, net_prod_GL]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[h1, Nat.cast_mul, net_cast_prod _ hq, net_prod_real _ (by exact_mod_cast hq), Nat.cast_pow, ← mul_assoc, ← pow_add, netExponent.2.2.2.2 n]`.
-/
theorem netCardGL : NetCardGL := by
  intro F _ _ n
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h1 : Nat.card (GL (Fin n) F)
      = Fintype.card F ^ (n * (n - 1) / 2) * ∏ i ∈ Icc 1 n, (Fintype.card F ^ i - 1) := by
    rw [Matrix.card_GL_field, net_prod_GL]
  refine ⟨h1, ?_⟩
  rw [h1, Nat.cast_mul, net_cast_prod _ hq, net_prod_real _ (by exact_mod_cast hq), Nat.cast_pow,
    ← mul_assoc, ← pow_add, netExponent.2.2.2.2 n]

section Pattern
variable {F : Type} [Field F] {n : ℕ} {S : Finset (Fin n × Fin n)}

/- English proof (translation)
Introduce `i j _`. Conclude with `Matrix.one_apply`.
-/
theorem net_pattern_one : netHasPattern S (1 : Matrix (Fin n) (Fin n) F) := by
  intro i j _
  exact Matrix.one_apply

/- English proof (translation)
Establish `ht : A.BlockTriangular id`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `hn : (i, j) ∉ S` using `fun h => absurd (hS _ h) (not_lt.mpr (le_of_lt hij'))`. Rewrite using `[hA i j hn, if_neg (ne_of_gt hij')]`.

Rewrite using `[Matrix.det_of_isUpperTriangular ht]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Establish `hn : (i, i) ∉ S` using `fun h => lt_irrefl _ (hS _ h)`. Rewrite using `[hA i i hn, if_pos rfl]`.
-/
theorem net_pattern_det (hS : ∀ x ∈ S, x.1 < x.2) {A : Matrix (Fin n) (Fin n) F}
    (hA : netHasPattern S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hn : (i, j) ∉ S := fun h => absurd (hS _ h) (not_lt.mpr (le_of_lt hij'))
    rw [hA i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun h => lt_irrefl _ (hS _ h)
  rw [hA i i hn, if_pos rfl]

/- English proof (translation)
Introduce `i l hil`. Rewrite using `[Matrix.mul_apply]`. Establish `hterm : ∀ j, A i j * B j l = if j = i then (if i = l then 1 else 0) else 0`. Introduce `j`. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Establish `hn : (j, j) ∉ S` using `fun h => lt_irrefl _ (hS _ h)`. Rewrite using `[hA j j hn, hB j l hil]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hji]`.

Distinguish the cases in `h1 : (i, j) ∈ S`. Distinguish the cases in `hjl : j = l`. Substitute `hjl` using the available equality. Conclude with `absurd h1 hil`. Establish `h2 : (j, l) ∉ S` using `fun h => hil (hT i j l h1 h)`.

Rewrite using `[hB j l h2, if_neg hjl, mul_zero]`. Rewrite using `[hA i j h1, if_neg (fun h => hji h.symm), zero_mul]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => hterm j)]`. Simplify using the standard rewrite rules.
-/
theorem net_pattern_mul (hS : ∀ x ∈ S, x.1 < x.2)
    (hT : ∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S) {A B : Matrix (Fin n) (Fin n) F}
    (hA : netHasPattern S A) (hB : netHasPattern S B) : netHasPattern S (A * B) := by
  intro i l hil
  rw [Matrix.mul_apply]
  have hterm : ∀ j, A i j * B j l = if j = i then (if i = l then 1 else 0) else 0 := by
    intro j
    by_cases hji : j = i
    · subst hji
      have hn : (j, j) ∉ S := fun h => lt_irrefl _ (hS _ h)
      rw [hA j j hn, hB j l hil]; simp
    · rw [if_neg hji]
      by_cases h1 : (i, j) ∈ S
      · by_cases hjl : j = l
        · subst hjl; exact absurd h1 hil
        · have h2 : (j, l) ∉ S := fun h => hil (hT i j l h1 h)
          rw [hB j l h2, if_neg hjl, mul_zero]
      · rw [hA i j h1, if_neg (fun h => hji h.symm), zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp

end Pattern

/- English proof (translation)
Introduce `F _ _ n S hS hT`. Set `M : Submonoid (GL (Fin n) F)` to `{ carrier := {A | netHasPattern S (A : Matrix (Fin n) (Fin n) F)} mul_mem' := fun {A B} hA hB => by`. Simplify using `using net_pattern_mul hS hT hA hB`. Use the proof step `one_mem' := by simpa using (net_pattern_one (F := F) (S := S)) }`. Set `H : Subgroup (GL (Fin n) F)` to `{ M with inv_mem' := fun {A} hA => by`.

Take `⟨N, hN, hAN⟩` from `(isOfFinOrder_iff_pow_eq_one).mp (isOfFinOrder_of_finite A)`. Establish `: A⁻¹ = A ^ (N - 1)`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← pow_succ', Nat.sub_add_cancel hN, hAN]`. Rewrite using `[this]`.

Conclude with `M.pow_mem hA _ }`. Use `⟨H, fun A => Iff.rfl, ?_⟩` and prove the remaining obligations. Set `φ : H → (S → F)` to `fun A s => (A.1 : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion.

Introduce `A B hAB`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Distinguish the cases in `h : (i, j) ∈ S`.

Conclude with `congrFun hAB ⟨(i, j), h⟩`. Rewrite using `[A.2 i j h, B.2 i j h]`. Introduce `f`. Set `A0 : Matrix (Fin n) (Fin n) F` to `fun i j => if h : (i, j) ∈ S then f ⟨(i, j), h⟩ else if i = j then 1 else 0`. Establish `hA0 : netHasPattern S A0` using `fun i j h => by simp only [A0, dif_neg h]`.

Establish `hdet : A0.det ≠ 0` using `by rw [net_pattern_det hS hA0]; exact one_ne_zero`. Use `⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A0 hdet, hA0⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Use `show A0 s.1.1 s.1.2 = f s`. Simplify using `only [A0, Prod.mk.eta, dif_pos s.2]`.

Rewrite using `[Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]`.
-/
theorem netPatternGroup : NetPatternGroup := by
  intro F _ _ n S hS hT
  classical
  let M : Submonoid (GL (Fin n) F) :=
    { carrier := {A | netHasPattern S (A : Matrix (Fin n) (Fin n) F)}
      mul_mem' := fun {A B} hA hB => by
        simpa using net_pattern_mul hS hT hA hB
      one_mem' := by simpa using (net_pattern_one (F := F) (S := S)) }
  let H : Subgroup (GL (Fin n) F) :=
    { M with
      inv_mem' := fun {A} hA => by
        obtain ⟨N, hN, hAN⟩ := (isOfFinOrder_iff_pow_eq_one).mp (isOfFinOrder_of_finite A)
        have : A⁻¹ = A ^ (N - 1) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ', Nat.sub_add_cancel hN, hAN]
        rw [this]
        exact M.pow_mem hA _ }
  refine ⟨H, fun A => Iff.rfl, ?_⟩
  let φ : H → (S → F) := fun A s => (A.1 : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  have hφ : Function.Bijective φ := by
    constructor
    · intro A B hAB
      apply Subtype.ext
      apply Units.ext
      ext i j
      by_cases h : (i, j) ∈ S
      · exact congrFun hAB ⟨(i, j), h⟩
      · rw [A.2 i j h, B.2 i j h]
    · intro f
      let A0 : Matrix (Fin n) (Fin n) F :=
        fun i j => if h : (i, j) ∈ S then f ⟨(i, j), h⟩ else if i = j then 1 else 0
      have hA0 : netHasPattern S A0 := fun i j h => by simp only [A0, dif_neg h]
      have hdet : A0.det ≠ 0 := by rw [net_pattern_det hS hA0]; exact one_ne_zero
      refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A0 hdet, hA0⟩, ?_⟩
      funext s
      show A0 s.1.1 s.1.2 = f s
      simp only [A0, Prod.mk.eta, dif_pos s.2]
  rw [Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_coe]

/- English proof (translation)
Unfold `netFull`. Rewrite using `[Finset.card_filter, Fintype.sum_prod_type_right]`. Establish `h : ∀ j : Fin n, ∑ i : Fin n, (if (i, j).1 < (i, j).2 then 1 else 0) = (j : ℕ)`. Introduce `j`. Rewrite using `[← Finset.card_filter]`.

Establish `: (univ.filter fun i : Fin n => (i, j).1 < (i, j).2) = Finset.Iio j`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this, Fin.card_Iio]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]`.
-/
theorem net_full_card (n : ℕ) : (netFull n).card = n * (n - 1) / 2 := by
  unfold netFull
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if (i, j).1 < (i, j).2 then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => (i, j).1 < (i, j).2) = Finset.Iio j := by
      ext i; simp
    rw [this, Fin.card_Iio]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) n,
    Finset.sum_range_id]

/- English proof (translation)
Establish `: ((netFull (k + c)).filter fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k) = (univ : Finset (Fin k)).image (fun i : Fin k => ((⟨p0 + i.val, by have` using `i.2; omega⟩ : Fin (k + c)), (⟨p0 + k, by omega⟩ : Fin (k + c)))) := by`. Use extensionality with `⟨a, b⟩`. Simplify using `only [netFull, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq, Fin.lt_def, Fin.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`.

Conclude with `⟨⟨a.val - p0, by omega⟩, by simp only []; omega, h3.symm⟩`. Introduce and unpack `⟨i, h1, h2⟩`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]`.

Introduce `i j hij`. Simplify using `only [Prod.mk.injEq, Fin.ext_iff, and_true] at hij`. Conclude with `Fin.ext (by omega)`.
-/
theorem net_removed_card (k c p0 : ℕ) (hp : p0 < c) :
    ((netFull (k + c)).filter fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k).card = k := by
  have : ((netFull (k + c)).filter fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k)
      = (univ : Finset (Fin k)).image
          (fun i : Fin k => ((⟨p0 + i.val, by have := i.2; omega⟩ : Fin (k + c)),
            (⟨p0 + k, by omega⟩ : Fin (k + c)))) := by
    ext ⟨a, b⟩
    simp only [netFull, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq, Fin.lt_def, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨a.val - p0, by omega⟩, by simp only []; omega, h3.symm⟩
    · rintro ⟨i, h1, h2⟩
      have := i.2
      omega
  rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j hij
  simp only [Prod.mk.injEq, Fin.ext_iff, and_true] at hij
  exact Fin.ext (by omega)

/- English proof (translation)
Use `⟨fun n => ⟨net_full_card n, ?_⟩, fun k c p0 hp => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `i j l h1 h2`. Simplify using `only [netFull, Finset.mem_filter, Finset.mem_univ, true_and] at *`. Conclude with `lt_trans h1 h2`. Establish `h1` using `Finset.card_filter_add_card_filter_not (s := netFull (k + c)) (fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k)`.

Establish `h2 : ((netFull (k + c)).filter fun x => ¬ (p0 ≤ x.1.val ∧ x.2.val = p0 + k)) = netPattern k c p0`. Unfold `netFull netPattern`. Rewrite using `[Finset.filter_filter]`. Rewrite `h1` using `[h2, net_removed_card k c p0 hp, net_full_card]`. Take `⟨d, rfl⟩ : ∃ d, c = d + 1` from `⟨c - 1, by omega⟩`.

Establish `e1` using `net_even_pred (d + 1)`. Establish `e2` using `net_even_pred k`. Establish `e3` using `net_even_pred (k + (d + 1))`. Break down `k with _ | k` into its components or cases. Simplify using `only [Nat.add_sub_cancel, zero_add, Nat.zero_mul, Nat.zero_div, add_zero, mul_zero] at *`.

Use linear arithmetic over natural numbers and integers. Establish `e4 : k + 1 + (d + 1) - 1 = k + 1 + d` using `by omega`. Simplify using `only [Nat.add_sub_cancel, e4] at *`. Use the polynomial consequences of the given equalities and inequalities. Introduce `i j l h1 h2`.

Simplify using `only [netPattern, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at *`. Use linear arithmetic over natural numbers and integers.
-/
theorem netPatternCard : NetPatternCard := by
  refine ⟨fun n => ⟨net_full_card n, ?_⟩, fun k c p0 hp => ⟨?_, ?_⟩⟩
  · intro i j l h1 h2
    simp only [netFull, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact lt_trans h1 h2
  · have h1 := Finset.card_filter_add_card_filter_not (s := netFull (k + c))
      (fun x => p0 ≤ x.1.val ∧ x.2.val = p0 + k)
    have h2 : ((netFull (k + c)).filter fun x => ¬ (p0 ≤ x.1.val ∧ x.2.val = p0 + k))
        = netPattern k c p0 := by
      unfold netFull netPattern
      rw [Finset.filter_filter]
    rw [h2, net_removed_card k c p0 hp, net_full_card] at h1
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    have e1 := net_even_pred (d + 1)
    have e2 := net_even_pred k
    have e3 := net_even_pred (k + (d + 1))
    rcases k with _ | k
    · simp only [Nat.add_sub_cancel, zero_add, Nat.zero_mul, Nat.zero_div, add_zero, mul_zero] at *
      omega
    · have e4 : k + 1 + (d + 1) - 1 = k + 1 + d := by omega
      simp only [Nat.add_sub_cancel, e4] at *
      nlinarith
  · intro i j l h1 h2
    simp only [netPattern, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at *
    omega

/- English proof (translation)
Establish `hq : (0 : ℝ) < Fintype.card F` using `by exact_mod_cast Fintype.card_pos`. Establish `h1 : (H.index : ℝ) * (Fintype.card F : ℝ) ^ e = (Nat.card (GL (Fin n) F) : ℝ)`. Rewrite using `[← H.index_mul_card, hH]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[(netCardGL F n).2, ← hE, pow_add]`. Establish `h2 : (Fintype.card F : ℝ) ^ e ≠ 0` using `(pow_pos hq e).ne'`. Apply `mul_right_cancel₀ h2` to reduce the goal to its premises. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem net_index_real (F : Type) [Field F] [Fintype F] (n e E : ℕ) (H : Subgroup (GL (Fin n) F))
    (hH : Nat.card H = Fintype.card F ^ e) (hE : e + E = n ^ 2) :
    (H.index : ℝ) = (Fintype.card F : ℝ) ^ E * ∏ i ∈ Icc 1 n, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 : (H.index : ℝ) * (Fintype.card F : ℝ) ^ e = (Nat.card (GL (Fin n) F) : ℝ) := by
    rw [← H.index_mul_card, hH]; push_cast; ring
  rw [(netCardGL F n).2, ← hE, pow_add] at h1
  have h2 : (Fintype.card F : ℝ) ^ e ≠ 0 := (pow_pos hq e).ne'
  apply mul_right_cancel₀ h2
  rw [h1]; ring

/- English proof (translation)
Take `⟨H', h1, h2⟩` from `netPatternGroup F n S hS hT`. Establish `: H = H'` using `Subgroup.ext fun A => by rw [hH, h1]`. Rewrite using `[this, h2]`.
-/
theorem net_card_of_pattern (F : Type) [Field F] [Fintype F] (n : ℕ) (S : Finset (Fin n × Fin n))
    (hS : ∀ x ∈ S, x.1 < x.2) (hT : ∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S)
    (H : Subgroup (GL (Fin n) F))
    (hH : ∀ A : GL (Fin n) F, A ∈ H ↔ netHasPattern S (A : Matrix (Fin n) (Fin n) F)) :
    Nat.card H = Fintype.card F ^ S.card := by
  obtain ⟨H', h1, h2⟩ := netPatternGroup F n S hS hT
  have : H = H' := Subgroup.ext fun A => by rw [hH, h1]
  rw [this, h2]

/- English proof (translation)
Establish `: 1 < q ^ i` using `one_lt_pow₀ hq (by omega)`. Use `inv_lt_one_of_one_lt₀ this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem net_factor_pos (q : ℝ) (hq : 1 < q) (i : ℕ) (hi : 1 ≤ i) : 0 < 1 - (q ^ i)⁻¹ := by
  have : 1 < q ^ i := one_lt_pow₀ hq (by omega)
  have := inv_lt_one_of_one_lt₀ this
  linarith

/- English proof (translation)
Introduce `J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA rL rLb Etw h1 hA h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2`. Establish `hb` using `balanceG J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA rL rLb Etw h1 hA h4 h5`. Establish `hr` using `netReturnOfA ℕ P T hTP n top R1 R2 (J.card : ℝ) k (by exact_mod_cast hJ) hk hJk hn1 hn2 hR2`. Establish `hr'` using `(abs_le.mp hr).1`. Establish `e : ∑ j ∈ J, ∑ τ ∈ P, (w j τ + e1 j τ + e2 j τ) = ∑ j ∈ J, ∑ τ ∈ P, w j τ + ∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ)`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hb` using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem netBalanceG : NetBalanceG := by
  intro J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA rL rLb Etw
    h1 hA h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2
  have hb := balanceG J T P D del hD hdel colL colLb aL aLb Dpi Dp Dm eta etab top k w e1 e2 Ecol CA
    rL rLb Etw h1 hA h4 h5
  have hr := netReturnOfA ℕ P T hTP n top R1 R2 (J.card : ℝ) k (by exact_mod_cast hJ) hk hJk hn1 hn2
    hR2
  have hr' := (abs_le.mp hr).1
  have e : ∑ j ∈ J, ∑ τ ∈ P, (w j τ + e1 j τ + e2 j τ)
      = ∑ j ∈ J, ∑ τ ∈ P, w j τ + ∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun τ _ => ?_; ring
  rw [e] at hb
  linarith

/- English proof (translation)
Use `Equiv.sum_comp (hc.toPerm c) X` as an intermediate fact. Simplify `this` using `only [Function.Involutive.coe_toPerm]`.
-/
theorem net_sum_inv {Λ : Type} [Fintype Λ] (c : Λ → Λ) (hc : Function.Involutive c) (X : Λ → ℝ) :
    ∑ u, X (c u) = ∑ u, X u := by
  have := Equiv.sum_comp (hc.toPerm c) X
  simpa only [Function.Involutive.coe_toPerm] using this

/- English proof (translation)
Introduce `Λ _ _ c hc y lg hy hys hlg J T P D del hD hdel col r a eta Dpi Dp Dm top k w e1 e2 Ecol CA Etw h1 hA h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2`. Use `set N : ℝ := (Fintype.card Λ : ℝ) with hN`. Establish `hN0 : 0 < N`. Rewrite using `[hN]`. Conclude with `Fintype.card_pos` after adjusting the coercions.

Use `set m : ℝ := (J.card : ℝ) with hm`. Use `set R' : ℝ := (∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k))) with hR'`. Use `set K : ℝ := -(∑ j ∈ J, ∑ τ ∈ P, w j τ) + m * (m - 1) / (2 * k) * ∑ t ∈ T, top t - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + Ecol + m * CA + Etw / (2 * D) + 2 * m * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2)) with hK`. Set `X : Λ → ℝ` to `fun u => 2 * col u - ∑ j ∈ J, a j u / D`. Establish `hu : ∀ u, K - ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) - m * ((r u + r (c u)) / (del * D)) ≤ (X u + X (c u)) / 2 + R'`.

Introduce `u`. Use `netBalanceG J T P D del hD hdel (col u) (col (c u)) (fun j => a j u) (fun j => a j (c u)) Dpi Dp Dm (fun j => eta j u) (fun j => eta j (c u)) top k w e1 e2 Ecol CA (r u) (r (c u)) Etw (h1 u) (hA u) h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2` as an intermediate fact. Establish `e : ∑ j ∈ J, (a j u + a j (c u)) / D = ∑ j ∈ J, a j u / D + ∑ j ∈ J, a j (c u) / D`. Rewrite using `[← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring`. Simplify using `only [X]`.

Rewrite `this` using `[e]`. Rewrite using `[hK, hR']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs` using `Finset.sum_le_sum (fun u (_ : u ∈ (univ : Finset Λ)) => hu u)`. Establish `eR : ∑ u, ((X u + X (c u)) / 2 + R') = ∑ u, X u + N * R'`.

Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, net_sum_inv c hc X]`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `eE : ∑ u, ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) = ∑ j ∈ J, (∑ u, eta j u) / D`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_div, Finset.sum_add_distrib, net_sum_inv c hc (eta j)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `eL : ∑ u, (K - ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) - m * ((r u + r (c u)) / (del * D))) = N * K - ∑ j ∈ J, (∑ u, eta j u) / D - m * ((∑ u, (r u + r (c u))) / (del * D))`.

Establish `e3 : ∑ u, m * ((r u + r (c u)) / (del * D)) = m * ((∑ u, (r u + r (c u))) / (del * D))`. Rewrite using `[← Finset.mul_sum, Finset.sum_div]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, eE, e3]`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]`. Rewrite `hs` using `[eL, eR]`.

Establish `hy'` using `netUnitMean Λ y X lg hy hys`. Establish `eM : ∑ j ∈ J, ((∑ u, eta j u) / N) / D = (∑ j ∈ J, (∑ u, eta j u) / D) / N`. Rewrite using `[Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring`. Establish `hfin` using `mul_le_mul_of_nonneg_left hs (div_nonneg hlg hN0.le)`. Use `show _ ≤ ∑ u, y u * X u + _`.

Rewrite using `[hy', eM]`. Establish `g1 : lg / N * (N * K - ∑ j ∈ J, (∑ u, eta j u) / D - m * ((∑ u, (r u + r (c u))) / (del * D))) = lg * (-(∑ j ∈ J, ∑ τ ∈ P, w j τ) + m * (m - 1) / (2 * k) * ∑ t ∈ T, top t - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + (∑ j ∈ J, (∑ u, eta j u) / D) / N + Ecol + m * (CA + ((∑ u, (r u + r …`. Rewrite using `[hK]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `g2 : lg / N * (∑ u, X u + N * R') = lg * ((∑ u, X u) / N) + R' * lg`. Clear the denominators using the available nonvanishing facts. Rewrite `hfin` using `[g1, g2]`. Conclude with `hfin`.
-/
theorem netBalanceMean : NetBalanceMean := by
  intro Λ _ _ c hc y lg hy hys hlg J T P D del hD hdel col r a eta Dpi Dp Dm top k w e1 e2 Ecol CA Etw
    h1 hA h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2
  set N : ℝ := (Fintype.card Λ : ℝ) with hN
  have hN0 : 0 < N := by
    rw [hN]; exact_mod_cast Fintype.card_pos
  set m : ℝ := (J.card : ℝ) with hm
  set R' : ℝ := (∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k))) with hR'
  set K : ℝ := -(∑ j ∈ J, ∑ τ ∈ P, w j τ) + m * (m - 1) / (2 * k) * ∑ t ∈ T, top t
      - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + Ecol + m * CA + Etw / (2 * D)
          + 2 * m * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2)) with hK
  let X : Λ → ℝ := fun u => 2 * col u - ∑ j ∈ J, a j u / D
  have hu : ∀ u, K - ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) - m * ((r u + r (c u)) / (del * D))
      ≤ (X u + X (c u)) / 2 + R' := by
    intro u
    have := netBalanceG J T P D del hD hdel (col u) (col (c u)) (fun j => a j u) (fun j => a j (c u))
      Dpi Dp Dm (fun j => eta j u) (fun j => eta j (c u)) top k w e1 e2 Ecol CA (r u) (r (c u)) Etw
      (h1 u) (hA u) h4 h5 n R1 R2 hTP hJ hk hJk hn1 hn2 hR2
    have e : ∑ j ∈ J, (a j u + a j (c u)) / D = ∑ j ∈ J, a j u / D + ∑ j ∈ J, a j (c u) / D := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    simp only [X]
    rw [e] at this
    rw [hK, hR']
    linarith
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ (univ : Finset Λ)) => hu u)
  have eR : ∑ u, ((X u + X (c u)) / 2 + R') = ∑ u, X u + N * R' := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, net_sum_inv c hc X]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have eE : ∑ u, ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D) = ∑ j ∈ J, (∑ u, eta j u) / D := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_div, Finset.sum_add_distrib, net_sum_inv c hc (eta j)]
    field_simp
    ring
  have eL : ∑ u, (K - ∑ j ∈ J, (eta j u + eta j (c u)) / (2 * D)
        - m * ((r u + r (c u)) / (del * D)))
      = N * K - ∑ j ∈ J, (∑ u, eta j u) / D - m * ((∑ u, (r u + r (c u))) / (del * D)) := by
    have e3 : ∑ u, m * ((r u + r (c u)) / (del * D)) = m * ((∑ u, (r u + r (c u))) / (del * D)) := by
      rw [← Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, eE, e3]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  rw [eL, eR] at hs
  have hy' := netUnitMean Λ y X lg hy hys
  have eM : ∑ j ∈ J, ((∑ u, eta j u) / N) / D = (∑ j ∈ J, (∑ u, eta j u) / D) / N := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  have hfin := mul_le_mul_of_nonneg_left hs (div_nonneg hlg hN0.le)
  show _ ≤ ∑ u, y u * X u + _
  rw [hy', eM]
  have g1 : lg / N * (N * K - ∑ j ∈ J, (∑ u, eta j u) / D
        - m * ((∑ u, (r u + r (c u))) / (del * D)))
      = lg * (-(∑ j ∈ J, ∑ τ ∈ P, w j τ) + m * (m - 1) / (2 * k) * ∑ t ∈ T, top t
        - (∑ j ∈ J, ∑ τ ∈ P, (e1 j τ + e2 j τ) + (∑ j ∈ J, (∑ u, eta j u) / D) / N + Ecol
            + m * (CA + ((∑ u, (r u + r (c u))) / N) / (del * D)) + Etw / (2 * D)
            + 2 * m * ((T.card : ℝ) * R1 + (P.card : ℝ) * R2))) := by
    rw [hK]
    field_simp
    ring
  have g2 : lg / N * (∑ u, X u + N * R') = lg * ((∑ u, X u) / N) + R' * lg := by
    field_simp
  rw [g1, g2] at hfin
  exact hfin

/- English proof (translation)
Introduce `h` and use `by have := h 1 0 norm_num at this`.
-/
example : ¬ ∀ k c : ℕ, (c * (c - 1) / 2 + (c - 1) * k + k * (k - 1) / 2)
    + ((k + c) * (k + c + 1) / 2 + k) = (k + c) ^ 2 := fun h => by
  have := h 1 0
  norm_num at this

/- English proof (translation)
Take `⟨Ha, h1, -⟩` from `netPatternGroup F k (netFull k) (fun x hx => by simpa [netFull] using hx) (netPatternCard.1 k).2`. Take `⟨Hb, h2, -⟩` from `netPatternGroup F (k + c) (netPattern k c p0) (fun x hx => by`. Simplify using `only [netPattern, Finset.mem_filter] at hx`. Conclude with `hx.2.1)`. Use the proof step `(netPatternCard.2 k c p0 hp).2`.

Conclude with `⟨Ha, Hb, h1, h2⟩`.
-/
example (F : Type) [Field F] [Fintype F] (k c p0 : ℕ) (hp : p0 < c) :
    ∃ (Ha : Subgroup (GL (Fin k) F)) (Hb : Subgroup (GL (Fin (k + c)) F)),
    (∀ A : GL (Fin k) F, A ∈ Ha ↔ netHasPattern (netFull k) (A : Matrix (Fin k) (Fin k) F)) ∧
    (∀ A : GL (Fin (k + c)) F, A ∈ Hb ↔
      netHasPattern (netPattern k c p0) (A : Matrix (Fin (k + c)) (Fin (k + c)) F)) := by
  obtain ⟨Ha, h1, -⟩ := netPatternGroup F k (netFull k) (fun x hx => by simpa [netFull] using hx)
    (netPatternCard.1 k).2
  obtain ⟨Hb, h2, -⟩ := netPatternGroup F (k + c) (netPattern k c p0)
    (fun x hx => by
      simp only [netPattern, Finset.mem_filter] at hx
      exact hx.2.1)
    (netPatternCard.2 k c p0 hp).2
  exact ⟨Ha, Hb, h1, h2⟩

/- English proof (translation)
Establish `: Icc 1 (1 + 1) = ({1, 2} : Finset ℕ)` using `by decide`. Rewrite using `[this]`. Evaluate the numerical expressions.
-/
example : (2 : ℝ) ^ ((1 + 1) * (1 + 1 + 1) / 2 + 1) * ∏ i ∈ Icc 1 (1 + 1), (1 - ((2 : ℝ) ^ i)⁻¹) = 6 := by
  have : Icc 1 (1 + 1) = ({1, 2} : Finset ℕ) := by decide
  rw [this]
  norm_num

/- English proof (translation)
Evaluate the decidable proposition.
-/
example : netPattern 1 1 0 = ∅ := by decide

/- English proof (translation)
Establish `hq1 : 1 < Fintype.card F` using `Fintype.one_lt_card`. Establish `hq : (1 : ℝ) < Fintype.card F` using `by exact_mod_cast hq1`. Establish `cc : ∀ (n : ℕ) (H : Subgroup (GL (Fin n) F)), (∀ A : GL (Fin n) F, A ∈ H ↔ netHasPattern (netFull n) (A : Matrix (Fin n) (Fin n) F)) → Nat.card H = Fintype.card F ^ (n * (n - 1) / 2)` using `fun n H hH => by`. Rewrite using `[net_card_of_pattern F n (netFull n) (fun x hx => by simpa [netFull] using hx) (netPatternCard.1 n).2 H hH, (netPatternCard.1 n).1]`. Rewrite using `[net_index_real F k _ _ Ha (cc k Ha hHa) (netExponent.2.2.2.2 k), net_index_real F (k + c) _ _ Hb (cc (k + c) Hb hHb) (netExponent.2.2.2.2 (k + c))]`.

Establish `hI : ∀ n : ℕ, Icc 1 n = Ioc 0 n` using `fun n => by ext i; simp; omega`. Establish `hsplit` using `Finset.prod_Ioc_consecutive (fun i => 1 - ((Fintype.card F : ℝ) ^ i)⁻¹) (Nat.zero_le k) (Nat.le_add_right k c)`. Establish `hexp : (k + c) * (k + c + 1) / 2 = k * (k + 1) / 2 + (k * c + c * (c + 1) / 2)`. Establish `e1` using `net_even_succ (k + c)`. Establish `e2` using `net_even_succ k`.

Establish `e3` using `net_even_succ c`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpos : (∏ i ∈ Ioc 0 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)) ≠ 0`. Apply `ne_of_gt` to reduce the goal to its premises. Apply `Finset.prod_pos` to reduce the goal to its premises.

Introduce `i hi`. Conclude with `net_factor_pos _ hq i (by simp at hi; omega)`. Establish `hpw : (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) ≠ 0` using `(pow_pos (by linarith) _).ne'`. Rewrite using `[hI, hI, ← hsplit, hexp, pow_add]`. Generalize the expression as in `(∏ i ∈ Ioc 0 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)) = X at hpos ⊢`.

Generalize the expression as in `(∏ i ∈ Ioc k (k + c), (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)) = Y`. Clear the denominators using the available nonvanishing facts.
-/
example (F : Type) [Field F] [Fintype F] (k c : ℕ)
    (Ha : Subgroup (GL (Fin k) F)) (Hb : Subgroup (GL (Fin (k + c)) F))
    (hHa : ∀ A : GL (Fin k) F, A ∈ Ha ↔ netHasPattern (netFull k) (A : Matrix (Fin k) (Fin k) F))
    (hHb : ∀ A : GL (Fin (k + c)) F, A ∈ Hb ↔
      netHasPattern (netFull (k + c)) (A : Matrix (Fin (k + c)) (Fin (k + c)) F)) :
    (Hb.index : ℝ) / (Ha.index : ℝ) = (Fintype.card F : ℝ) ^ (k * c + c * (c + 1) / 2)
        * ∏ i ∈ Ioc k (k + c), (1 - ((Fintype.card F : ℝ) ^ i)⁻¹) := by
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast hq1
  have cc : ∀ (n : ℕ) (H : Subgroup (GL (Fin n) F)),
      (∀ A : GL (Fin n) F, A ∈ H ↔ netHasPattern (netFull n) (A : Matrix (Fin n) (Fin n) F)) →
      Nat.card H = Fintype.card F ^ (n * (n - 1) / 2) := fun n H hH => by
    rw [net_card_of_pattern F n (netFull n) (fun x hx => by simpa [netFull] using hx)
      (netPatternCard.1 n).2 H hH, (netPatternCard.1 n).1]
  rw [net_index_real F k _ _ Ha (cc k Ha hHa) (netExponent.2.2.2.2 k),
    net_index_real F (k + c) _ _ Hb (cc (k + c) Hb hHb) (netExponent.2.2.2.2 (k + c))]
  have hI : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n => by ext i; simp; omega
  have hsplit := Finset.prod_Ioc_consecutive
    (fun i => 1 - ((Fintype.card F : ℝ) ^ i)⁻¹) (Nat.zero_le k) (Nat.le_add_right k c)
  have hexp : (k + c) * (k + c + 1) / 2 = k * (k + 1) / 2 + (k * c + c * (c + 1) / 2) := by
    have e1 := net_even_succ (k + c)
    have e2 := net_even_succ k
    have e3 := net_even_succ c
    nlinarith
  have hpos : (∏ i ∈ Ioc 0 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    exact net_factor_pos _ hq i (by simp at hi; omega)
  have hpw : (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) ≠ 0 := (pow_pos (by linarith) _).ne'
  rw [hI, hI, ← hsplit, hexp, pow_add]
  generalize (∏ i ∈ Ioc 0 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)) = X at hpos ⊢
  generalize (∏ i ∈ Ioc k (k + c), (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)) = Y
  field_simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
example : ¬ (∏ i ∈ Ioc 3 3, (1 - ((2 : ℝ) ^ i)⁻¹) < 1) := by simp

/- English proof (translation)
The claim follows from `|(∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k))) - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t)| ≤ 2 * m * ((TT.card : ℝ) * R1 + (P.card : ℝ) * R2) := fun h => by have := h {0} ∅ (by simp) (fun _ => 1) (fun _ => 0) 0 1 5 1 (by norm_num) (by norm_num) (by simp) (by s …`.
-/
example : ¬ ∀ (P TT : Finset ℕ), TT ⊆ P → ∀ (n a : ℕ → ℝ) (R1 R2 m k : ℝ),
    1 ≤ m → 0 < k →
    (∀ t ∈ TT, |n t - a t| ≤ R1) → (∀ τ ∈ P \ TT, |n τ| ≤ R2) → 0 ≤ R2 →
    |(∑ τ ∈ P, n τ) * (m * (1 + (m - 1) / (2 * k)))
        - (m * ∑ t ∈ TT, a t + m * (m - 1) / (2 * k) * ∑ t ∈ TT, a t)|
      ≤ 2 * m * ((TT.card : ℝ) * R1 + (P.card : ℝ) * R2) := fun h => by
  have := h {0} ∅ (by simp) (fun _ => 1) (fun _ => 0) 0 1 5 1 (by norm_num) (by norm_num)
    (by simp) (by simp) (by norm_num)
  norm_num at this

/- English proof (translation)
Introduce `h` and use `by have := h (fun b => if b then 1 else 0) (fun b => if b then 1 else 0) norm_num at this`.
-/
example : ¬ ∀ (x X : Bool → ℝ), ∑ w, x w * X w = ∑ w, x w * ((X w + X (!w)) / 2) := fun h => by
  have := h (fun b => if b then 1 else 0) (fun b => if b then 1 else 0)
  norm_num at this

/- English proof (translation)
Introduce `h` and use `by have := h 5 1 1 1 0 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) norm_num at this`.
-/
example : ¬ ∀ (k m t L S η : ℕ), 1 ≤ m → 1 ≤ t → 1 ≤ L → m * k * t * L ≤ η →
    k * (k + m - 1 + t) ≤ k * S + m * η := fun h => by
  have := h 5 1 1 1 0 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/- English proof (translation)
Establish `h` using `netBalanceG {0} {0} {0} 1 1 one_pos one_pos x 0 (fun _ => 0) (fun _ => 0) (fun _ => 6) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 5) 1 (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) 0 0 0 0 0 (by simpa using hx) (by simp) (by norm_num) (by simp) (fun _ => 5) 0 0 …`. Evaluate the numerical expressions using `at h`. Conclude with `h`.
-/
example (x : ℝ) (hx : -6 ≤ x) : -1 ≤ x + 5 := by
  have h := netBalanceG {0} {0} {0} 1 1 one_pos one_pos x 0 (fun _ => 0) (fun _ => 0) (fun _ => 6)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 5) 1 (fun _ _ => 1) (fun _ _ => 0)
    (fun _ _ => 0) 0 0 0 0 0 (by simpa using hx) (by simp) (by norm_num) (by simp)
    (fun _ => 5) 0 0 (by simp) (by simp) one_pos (by simp) (by simp) (by simp) le_rfl
  norm_num at h
  exact h

/- English proof (translation)
Apply the tactic sequence `have h := netBalanceMean Bool (fun b => !b) (fun b => by simp) (fun _ => 1 / 2) 1 (fun _ _ => rfl) (by norm_num) zero_le_one {0} {0} {0} 1 1 one_pos one_pos (fun b => if b then x else 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 6) (fun _ => 0) (fun _ => 0) (fun _ => 5 …`. Evaluate the numerical expressions using `at h`. Establish `e : 1 / 2 * (2 * x) = x` using `by ring`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
example (x : ℝ) (hx : -6 ≤ x) : -1 ≤ x + 5 := by
  have h := netBalanceMean Bool (fun b => !b) (fun b => by simp) (fun _ => 1 / 2) 1 (fun _ _ => rfl)
    (by norm_num) zero_le_one {0} {0} {0} 1 1 one_pos one_pos (fun b => if b then x else 0)
    (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 6)
    (fun _ => 0) (fun _ => 0) (fun _ => 5) 1 (fun _ _ => 1) (fun _ _ => 0)
    (fun _ _ => 0) 0 0 0 (by intro u; cases u <;> simpa using hx) (by simp) (by norm_num) (by simp)
    (fun _ => 5) 0 0 (by simp) (by simp) one_pos (by simp) (by simp) (by simp) le_rfl
  norm_num at h
  have e : 1 / 2 * (2 * x) = x := by ring
  rwa [e] at h

/- English proof (translation)
Introduce and unpack `⟨H, hH⟩`. Set `A0 : Matrix (Fin 3) (Fin 3) (ZMod 2)` to `!![1, 1, 0; 0, 1, 0; 0, 0, 1]`. Set `B0 : Matrix (Fin 3) (Fin 3) (ZMod 2)` to `!![1, 0, 0; 0, 1, 1; 0, 0, 1]`. Establish `dA : A0.det ≠ 0` using `by simp [A0, Matrix.det_fin_three]`. Establish `dB : B0.det ≠ 0` using `by simp [B0, Matrix.det_fin_three]`.

Establish `hA : Matrix.GeneralLinearGroup.mkOfDetNeZero A0 dA ∈ H` using `(hH _).2 (by show netHasPattern _ A0`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | (simp [A0]; done) | (exfalso; exact hij (by decide)))`. Establish `hB : Matrix.GeneralLinearGroup.mkOfDetNeZero B0 dB ∈ H` using `(hH _).2 (by show netHasPattern _ B0`. Introduce `i j hij`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | (simp [B0]; done) | (exfalso; exact hij (by decide)))`. Establish `h` using `(hH _).1 (H.mul_mem hA hB) 0 2 (by decide)`. Establish `h' : (A0 * B0) 0 2 = 0` using `h`. Use `revert h'`. Evaluate the decidable proposition.
-/
example : ¬ ∃ H : Subgroup (GL (Fin 3) (ZMod 2)), ∀ A : GL (Fin 3) (ZMod 2), A ∈ H ↔
    netHasPattern ({(0, 1), (1, 2)} : Finset (Fin 3 × Fin 3))
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rintro ⟨H, hH⟩
  let A0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]
  let B0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]
  have dA : A0.det ≠ 0 := by simp [A0, Matrix.det_fin_three]
  have dB : B0.det ≠ 0 := by simp [B0, Matrix.det_fin_three]
  have hA : Matrix.GeneralLinearGroup.mkOfDetNeZero A0 dA ∈ H := (hH _).2 (by
    show netHasPattern _ A0
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (simp [A0]; done) | (exfalso; exact hij (by decide)))
  have hB : Matrix.GeneralLinearGroup.mkOfDetNeZero B0 dB ∈ H := (hH _).2 (by
    show netHasPattern _ B0
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (simp [B0]; done) | (exfalso; exact hij (by decide)))
  have h := (hH _).1 (H.mul_mem hA hB) 0 2 (by decide)
  have h' : (A0 * B0) 0 2 = 0 := h
  revert h'
  decide

/- English proof (translation)
Take `⟨H, h, -⟩` from `netPatternGroup (IsLocalRing.ResidueField O) n S hS hT`. Conclude with `⟨H.comap (Matrix.GeneralLinearGroup.map (IsLocalRing.residue O)), fun A => by`. Rewrite using `[Subgroup.mem_comap, h]`. Use the proof step `rfl⟩`.
-/
example (O : Type) [CommRing O] [IsLocalRing O] [Fintype (IsLocalRing.ResidueField O)] (n : ℕ)
    (S : Finset (Fin n × Fin n)) (hS : ∀ x ∈ S, x.1 < x.2)
    (hT : ∀ i j l, (i, j) ∈ S → (j, l) ∈ S → (i, l) ∈ S) :
    ∃ K : Subgroup (GL (Fin n) O), ∀ A : GL (Fin n) O, A ∈ K ↔
      netHasPattern S ((A : Matrix (Fin n) (Fin n) O).map (IsLocalRing.residue O)) := by
  obtain ⟨H, h, -⟩ := netPatternGroup (IsLocalRing.ResidueField O) n S hS hT
  exact ⟨H.comap (Matrix.GeneralLinearGroup.map (IsLocalRing.residue O)), fun A => by
    rw [Subgroup.mem_comap, h]; rfl⟩

/- English proof (translation)
Set `_ : Fintype (IsLocalRing.ResidueField ℤ_[g])` to `Fintype.ofEquiv (ZMod g) PadicInt.residueField.toEquiv.symm`. Conclude with `⟨inferInstance, by rw [Fintype.card_congr PadicInt.residueField.toEquiv, ZMod.card]⟩`.
-/
example (g : ℕ) [Fact g.Prime] : ∃ _ : Fintype (IsLocalRing.ResidueField ℤ_[g]),
    Fintype.card (IsLocalRing.ResidueField ℤ_[g]) = g := by
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[g]) :=
    Fintype.ofEquiv (ZMod g) PadicInt.residueField.toEquiv.symm
  exact ⟨inferInstance, by rw [Fintype.card_congr PadicInt.residueField.toEquiv, ZMod.card]⟩

end Formalism.CG
