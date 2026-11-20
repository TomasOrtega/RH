import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

namespace Formalism.RepresentationBoundsCohomology.N2.SumVal

open Finset

variable (ℓ : ℕ) [Fact ℓ.Prime]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `zero => simp`. Consider the case `succ w ih`. Rewrite using `[← add_assoc, Finset.sum_Ioc_succ_top (by omega), Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ← ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_Ioc_add (n w : ℕ) :
    (∑ k ∈ Ioc n (n + w), padicValNat ℓ k) + padicValNat ℓ n.factorial =
      padicValNat ℓ (n + w).factorial := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _), ← ih]
    ring

/- English proof (translation)
Establish `h1` using `sum_Ioc_add ℓ n w`. Establish `h2` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left w n)`. Rewrite `h2` using `[Nat.add_sub_cancel]`. Rewrite `h1` using `[← h2, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (Nat.le_add_left w n)).ne' (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _), padicValNat.mul (Nat.choose_pos (Nat.le_add_left w n)).ne' (Nat.factorial_ne_zero _)]`. Use linear arithmetic over natural numbers and integers.
-/
lemma sum_Ioc_eq (n w : ℕ) :
    (∑ k ∈ Ioc n (n + w), padicValNat ℓ k) =
      padicValNat ℓ w.factorial + padicValNat ℓ ((n + w).choose w) := by
  have h1 := sum_Ioc_add ℓ n w
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left w n)
  rw [Nat.add_sub_cancel] at h2
  rw [← h2, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (Nat.le_add_left w n)).ne'
      (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.choose_pos (Nat.le_add_left w n)).ne' (Nat.factorial_ne_zero _)] at h1
  omega

/- English proof (translation)
Conclude with `(Fact.out : ℓ.Prime).one_lt` after adjusting the coercions.
-/
lemma one_lt_cast : (1 : ℝ) < (ℓ : ℝ) := by
  exact_mod_cast (Fact.out : ℓ.Prime).one_lt

/- English proof (translation)
Establish `h` using `sub_one_mul_padicValNat_factorial (p := ℓ) w`. Establish `h' : (ℓ - 1) * padicValNat ℓ w.factorial ≤ w` using `by rw [h]; exact Nat.sub_le _ _`. Establish `hl` using `one_lt_cast ℓ`. Rewrite using `[le_div_iff₀ (by linarith)]`. Establish `e : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1`.

Rewrite using `[Nat.cast_sub (Fact.out : ℓ.Prime).one_lt.le]`. Simplify using the standard rewrite rules. Establish `h2 : (((ℓ - 1) * padicValNat ℓ w.factorial : ℕ) : ℝ) ≤ w` using `by exact_mod_cast h'`. Rewrite `h2` using `[Nat.cast_mul, e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma val_factorial_le (w : ℕ) :
    (padicValNat ℓ w.factorial : ℝ) ≤ (w : ℝ) / ((ℓ : ℝ) - 1) := by
  have h := sub_one_mul_padicValNat_factorial (p := ℓ) w
  have h' : (ℓ - 1) * padicValNat ℓ w.factorial ≤ w := by rw [h]; exact Nat.sub_le _ _
  have hl := one_lt_cast ℓ
  rw [le_div_iff₀ (by linarith)]
  have e : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (Fact.out : ℓ.Prime).one_lt.le]; simp
  have h2 : (((ℓ - 1) * padicValNat ℓ w.factorial : ℕ) : ℝ) ≤ w := by exact_mod_cast h'
  rw [Nat.cast_mul, e] at h2
  linarith

/- English proof (translation)
Establish `h1 : padicValNat ℓ (N.choose w) ≤ Nat.log ℓ N`. Rewrite using `[← Nat.factorization_def _ (Fact.out : ℓ.Prime)]`. Conclude with `Nat.factorization_choose_le_log`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma val_choose_le (N w : ℕ) :
    (padicValNat ℓ (N.choose w) : ℝ) ≤ Real.logb ℓ N := by
  have h1 : padicValNat ℓ (N.choose w) ≤ Nat.log ℓ N := by
    rw [← Nat.factorization_def _ (Fact.out : ℓ.Prime)]
    exact Nat.factorization_choose_le_log
  calc (padicValNat ℓ (N.choose w) : ℝ) ≤ (Nat.log ℓ N : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb ℓ N := Real.natLog_le_logb N ℓ

/- English proof (translation)
Use `set N' := min (n + (y + 1)) D with hN'`. Establish `hsub : T ⊆ Ioc n N'` using `fun k hk => by`. Take `⟨h1, h2, h3⟩` from `hT k hk`. Conclude with `Finset.mem_Ioc.2 ⟨h1, le_min h2 h3⟩`. Establish `hle : (∑ k ∈ T, padicValNat ℓ k) ≤ ∑ k ∈ Ioc n N', padicValNat ℓ k` using `Finset.sum_le_sum_of_subset hsub`.

Establish `hl` using `one_lt_cast ℓ`. Establish `hD0 : (0 : ℝ) ≤ Real.logb ℓ D` using `Real.logb_nonneg hl (by exact_mod_cast hD)`. Distinguish the cases in `hnN : n ≤ N'`. Take `⟨w, hw⟩ : ∃ w, N' = n + w` from `⟨N' - n, by omega⟩`. Rewrite `hle` using `[hw, sum_Ioc_eq]`.

Establish `hwle : w ≤ y + 1` using `by have := min_le_left (n + (y + 1)) D; omega`. Establish `hND : n + w ≤ D` using `by have := min_le_right (n + (y + 1)) D; omega`. Establish `e1` using `val_factorial_le ℓ w`. Establish `e2` using `val_choose_le ℓ (n + w) w`. Establish `e3 : (w : ℝ) / ((ℓ : ℝ) - 1) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1)` using `div_le_div_of_nonneg_right (by exact_mod_cast hwle) (by linarith)`.

Establish `e4 : Real.logb ℓ (n + w : ℕ) ≤ Real.logb ℓ D`. Break down `Nat.eq_zero_or_pos (n + w) with h0 | h0` into its components or cases. Rewrite using `[h0, Nat.cast_zero, Real.logb_zero]`. Conclude with `hD0`. Conclude with `Real.logb_le_logb_of_le hl (by exact_mod_cast h0) (by exact_mod_cast hND)`.

Establish `e5 : ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤ (padicValNat ℓ w.factorial : ℝ) + padicValNat ℓ ((n + w).choose w)` using `by exact_mod_cast hle`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : Ioc n N' = ∅` using `Finset.Ioc_eq_empty (by omega)`. Rewrite `hle` using `[hE, Finset.sum_empty, Nat.le_zero]`. Rewrite using `[hle]`.

Establish `: (0 : ℝ) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1)` using `div_nonneg (by positivity) (by linarith)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_nat_le (n y D : ℕ) (hD : 1 ≤ D) (T : Finset ℕ)
    (hT : ∀ k ∈ T, n < k ∧ k ≤ n + (y + 1) ∧ k ≤ D) :
    ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  set N' := min (n + (y + 1)) D with hN'
  have hsub : T ⊆ Ioc n N' := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := hT k hk
    exact Finset.mem_Ioc.2 ⟨h1, le_min h2 h3⟩
  have hle : (∑ k ∈ T, padicValNat ℓ k) ≤ ∑ k ∈ Ioc n N', padicValNat ℓ k :=
    Finset.sum_le_sum_of_subset hsub
  have hl := one_lt_cast ℓ
  have hD0 : (0 : ℝ) ≤ Real.logb ℓ D := Real.logb_nonneg hl (by exact_mod_cast hD)
  by_cases hnN : n ≤ N'
  · obtain ⟨w, hw⟩ : ∃ w, N' = n + w := ⟨N' - n, by omega⟩
    rw [hw, sum_Ioc_eq] at hle
    have hwle : w ≤ y + 1 := by have := min_le_left (n + (y + 1)) D; omega
    have hND : n + w ≤ D := by have := min_le_right (n + (y + 1)) D; omega
    have e1 := val_factorial_le ℓ w
    have e2 := val_choose_le ℓ (n + w) w
    have e3 : (w : ℝ) / ((ℓ : ℝ) - 1) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hwle) (by linarith)
    have e4 : Real.logb ℓ (n + w : ℕ) ≤ Real.logb ℓ D := by
      rcases Nat.eq_zero_or_pos (n + w) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.logb_zero]; exact hD0
      · exact Real.logb_le_logb_of_le hl (by exact_mod_cast h0) (by exact_mod_cast hND)
    have e5 : ((∑ k ∈ T, padicValNat ℓ k : ℕ) : ℝ) ≤
        (padicValNat ℓ w.factorial : ℝ) + padicValNat ℓ ((n + w).choose w) := by exact_mod_cast hle
    linarith
  · have hE : Ioc n N' = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hE, Finset.sum_empty, Nat.le_zero] at hle
    rw [hle]
    have : (0 : ℝ) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
    push_cast
    linarith

end Formalism.RepresentationBoundsCohomology.N2.SumVal

namespace Formalism.RepresentationBoundsCohomology.N2

open Finset

/- English proof (translation)
Establish `hsum : ∑ b ∈ S', padicValInt ℓ (a - b) = ∑ k ∈ S'.image (fun b => (f b).toNat), padicValNat ℓ k`. Rewrite using `[Finset.sum_image]`. Conclude with `Finset.sum_congr rfl hg`. Introduce `b hb b' hb' h`. Establish `h' : (f b).toNat = (f b').toNat` using `h`.

Establish `h1` using `(hf b hb).1`. Establish `h2` using `(hf b' hb').1`. Conclude with `hinj b hb b' hb' (by omega)`. Rewrite using `[hsum]`. Use `SumVal.sum_nat_le ℓ n y D hD _ ?_` and prove the remaining obligations.

Introduce `k hk`. Take `⟨b, hb, rfl⟩` from `Finset.mem_image.1 hk`. Take `⟨h1, h2, h3⟩` from `hf b hb`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_padicValInt_sub_le_of_injective_bound (ℓ : ℕ) [Fact ℓ.Prime] (S' : Finset ℤ) (a : ℤ) (f : ℤ → ℤ)
    (n y D : ℕ) (hD : 1 ≤ D) (hf : ∀ b ∈ S', (n : ℤ) < f b ∧ f b ≤ n + (y + 1) ∧ f b ≤ D)
    (hinj : ∀ b ∈ S', ∀ b' ∈ S', f b = f b' → b = b')
    (hg : ∀ b ∈ S', padicValInt ℓ (a - b) = padicValNat ℓ (f b).toNat) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  have hsum : ∑ b ∈ S', padicValInt ℓ (a - b) =
      ∑ k ∈ S'.image (fun b => (f b).toNat), padicValNat ℓ k := by
    rw [Finset.sum_image]
    · exact Finset.sum_congr rfl hg
    · intro b hb b' hb' h
      have h' : (f b).toNat = (f b').toNat := h
      have h1 := (hf b hb).1
      have h2 := (hf b' hb').1
      exact hinj b hb b' hb' (by omega)
  rw [hsum]
  refine SumVal.sum_nat_le ℓ n y D hD _ ?_
  intro k hk
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hk
  obtain ⟨h1, h2, h3⟩ := hf b hb
  omega

/- English proof (translation)
Use `sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => a - b) (a - m - y - 1).toNat y D hD ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Establish `h1` using `Finset.mem_Icc.1 (hS hb)`. Establish `h2` using `abs_le.1 (hSD b hb)`. Establish `h3` using `hlt b hb`.

Use `beta_reduce`. Use linear arithmetic over natural numbers and integers. Introduce `b _ b' _ h`. Establish `h' : a - b = a - b'` using `h`. Use linear arithmetic over natural numbers and integers.

Introduce `b hb`. Establish `h3` using `hlt b hb`. Simplify using `only [padicValInt]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_padicValInt_sub_le_of_lt_forall (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S' : Finset ℤ) (a : ℤ)
    (hS : S' ⊆ Finset.Icc m (m + y)) (hD : 1 ≤ D) (hSD : ∀ b ∈ S', |a - b| ≤ D)
    (hlt : ∀ b ∈ S', b < a) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  refine sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => a - b) (a - m - y - 1).toNat y D hD ?_ ?_ ?_
  · intro b hb
    have h1 := Finset.mem_Icc.1 (hS hb)
    have h2 := abs_le.1 (hSD b hb)
    have h3 := hlt b hb
    beta_reduce
    omega
  · intro b _ b' _ h
    have h' : a - b = a - b' := h
    omega
  · intro b hb
    have h3 := hlt b hb
    simp only [padicValInt]
    congr 1
    omega

/- English proof (translation)
Use `sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => b - a) (m - a - 1).toNat y D hD ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Establish `h1` using `Finset.mem_Icc.1 (hS hb)`. Establish `h2` using `abs_le.1 (hSD b hb)`. Establish `h3` using `hgt b hb`.

Use `beta_reduce`. Use linear arithmetic over natural numbers and integers. Introduce `b _ b' _ h`. Establish `h' : b - a = b' - a` using `h`. Use linear arithmetic over natural numbers and integers.

Introduce `b hb`. Establish `h3` using `hgt b hb`. Simplify using `only [padicValInt]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sum_padicValInt_sub_le_of_gt_forall (ℓ : ℕ) [Fact ℓ.Prime] (m : ℤ) (y D : ℕ) (S' : Finset ℤ) (a : ℤ)
    (hS : S' ⊆ Finset.Icc m (m + y)) (hD : 1 ≤ D) (hSD : ∀ b ∈ S', |a - b| ≤ D)
    (hgt : ∀ b ∈ S', a < b) :
    ((∑ b ∈ S', padicValInt ℓ (a - b) : ℕ) : ℝ) ≤
      ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D := by
  refine sum_padicValInt_sub_le_of_injective_bound ℓ S' a (fun b => b - a) (m - a - 1).toNat y D hD ?_ ?_ ?_
  · intro b hb
    have h1 := Finset.mem_Icc.1 (hS hb)
    have h2 := abs_le.1 (hSD b hb)
    have h3 := hgt b hb
    beta_reduce
    omega
  · intro b _ b' _ h
    have h' : b - a = b' - a := h
    omega
  · intro b hb
    have h3 := hgt b hb
    simp only [padicValInt]
    congr 1
    omega

/- English proof (translation)
Introduce `ℓ _ m y D S a hS ha hD hSD`. Establish `hS' : S.erase a ⊆ Finset.Icc m (m + y)` using `(Finset.erase_subset a S).trans hS`. Establish `hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D` using `fun b hb => hSD b (Finset.mem_of_mem_erase hb)`. Break down `ha with ha | ha` into its components or cases. Use `sum_padicValInt_sub_le_of_gt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_` and prove the remaining obligations.

Establish `h1` using `Finset.mem_Icc.1 (hS' hb)`. Establish `h2` using `Finset.ne_of_mem_erase hb`. Use linear arithmetic over natural numbers and integers. Use `sum_padicValInt_sub_le_of_lt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_` and prove the remaining obligations. Establish `h1` using `Finset.mem_Icc.1 (hS' hb)`.

Establish `h2` using `Finset.ne_of_mem_erase hb`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_sum_at_endpoint : StatSumValEnd := by
  intro ℓ _ m y D S a hS ha hD hSD
  have hS' : S.erase a ⊆ Finset.Icc m (m + y) := (Finset.erase_subset a S).trans hS
  have hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D := fun b hb => hSD b (Finset.mem_of_mem_erase hb)
  rcases ha with ha | ha
  · refine sum_padicValInt_sub_le_of_gt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_
    have h1 := Finset.mem_Icc.1 (hS' hb)
    have h2 := Finset.ne_of_mem_erase hb
    omega
  · refine sum_padicValInt_sub_le_of_lt_forall ℓ m y D (S.erase a) a hS' hD hSD' fun b hb => ?_
    have h1 := Finset.mem_Icc.1 (hS' hb)
    have h2 := Finset.ne_of_mem_erase hb
    omega

/- English proof (translation)
Introduce `ℓ _ m y D S a hS hD hSD`. Establish `hS' : S.erase a ⊆ Finset.Icc m (m + y)` using `(Finset.erase_subset a S).trans hS`. Establish `hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D` using `fun b hb => hSD b (Finset.mem_of_mem_erase hb)`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not (S.erase a) (fun b => b < a), Nat.cast_add, two_mul]`. Apply `add_le_add` to reduce the goal to its premises.

Conclude with `sum_padicValInt_sub_le_of_lt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => (Finset.mem_filter.1 hb).2)`. Use `sum_padicValInt_sub_le_of_gt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => ?_)` and prove the remaining obligations. Take `⟨hb1, hb2⟩` from `Finset.mem_filter.1 hb`. Use `Finset.ne_of_mem_erase hb1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_sum_general_index : StatSumValGen := by
  intro ℓ _ m y D S a hS hD hSD
  have hS' : S.erase a ⊆ Finset.Icc m (m + y) := (Finset.erase_subset a S).trans hS
  have hSD' : ∀ b ∈ S.erase a, |a - b| ≤ D := fun b hb => hSD b (Finset.mem_of_mem_erase hb)
  rw [← Finset.sum_filter_add_sum_filter_not (S.erase a) (fun b => b < a), Nat.cast_add, two_mul]
  apply add_le_add
  · exact sum_padicValInt_sub_le_of_lt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD
      (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => (Finset.mem_filter.1 hb).2)
  · refine sum_padicValInt_sub_le_of_gt_forall ℓ m y D _ a ((Finset.filter_subset _ _).trans hS') hD
      (fun b hb => hSD' b (Finset.mem_of_mem_filter b hb)) (fun b hb => ?_)
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    have := Finset.ne_of_mem_erase hb1
    omega

end Formalism.RepresentationBoundsCohomology.N2
