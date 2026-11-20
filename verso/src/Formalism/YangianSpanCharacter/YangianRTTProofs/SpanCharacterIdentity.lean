import Formalism.YangianSpanCharacter.StatementE

namespace Formalism.YangianSpanCharacter.P

open Finset

/- English proof (translation)
Introduce `g hg k`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi1 : i ≠ 0`. Use `(Finset.mem_Ico.mp hi).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hgi : 1 < g ^ i` using `one_lt_pow₀ hg hi1`. Establish `h0 : g ^ i ≠ 0` using `by positivity`. Establish `h1 : g ^ i - 1 ≠ 0` using `by linarith`. Establish `h2 : 1 - (g ^ i)⁻¹ ≠ 0`.

Rewrite using `[sub_ne_zero]`. Introduce `h`. Establish `: g ^ i = 1` using `by rw [eq_comm, inv_eq_one] at h; exact h`. Combine the linear equalities and inequalities to obtain the conclusion. Clear the denominators using the available nonvanishing facts.
-/
theorem gamma_ratio_identity : Formalism.YangianSpanCharacter.E.GGRatio := by
  intro g hg k
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi1 : i ≠ 0 := by
    have := (Finset.mem_Ico.mp hi).1; omega
  have hgi : 1 < g ^ i := one_lt_pow₀ hg hi1
  have h0 : g ^ i ≠ 0 := by positivity
  have h1 : g ^ i - 1 ≠ 0 := by linarith
  have h2 : 1 - (g ^ i)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : g ^ i = 1 := by rw [eq_comm, inv_eq_one] at h; exact h
    linarith
  field_simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.prod_insert hj]`. Establish `ih'` using `ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi)) (fun i hi => h1 i (Finset.mem_insert_of_mem hi))`.

Establish `haj0` using `h0 j (Finset.mem_insert_self j s)`. Establish `haj1` using `h1 j (Finset.mem_insert_self j s)`. Establish `hS : 0 ≤ ∑ i ∈ s, a i` using `Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)`. Use `mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr haj1)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma weier {ι : Type} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have haj0 := h0 j (Finset.mem_insert_self j s)
    have haj1 := h1 j (Finset.mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have := mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr haj1)
    nlinarith

/- English proof (translation)
Establish `hr0 : 0 < g⁻¹` using `by positivity`. Establish `hr1 : g⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Repeatedly rewrite using `[← inv_pow]`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Rewrite using `[Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty]`.

Conclude with `div_nonneg zero_le_one (by linarith)`. Establish `hm` using `geom_sum_Ico_mul g⁻¹ (show 1 ≤ k from hk)`. Establish `hS : (∑ i ∈ Finset.Ico 1 k, g⁻¹ ^ i) * (1 - g⁻¹) ≤ g⁻¹`. Establish `: 0 ≤ g⁻¹ ^ k` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hpos : 0 < 1 - g⁻¹` using `by linarith`. Establish `he : 1 / (g - 1) = g⁻¹ / (1 - g⁻¹)`. Establish `: g ≠ 0` using `by linarith`. Establish `: g - 1 ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[he, le_div_iff₀ hpos]`. Conclude with `hS`.
-/
private lemma geom_le (g : ℝ) (hg : 3 ≤ g) (k : ℕ) :
    ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ 1 / (g - 1) := by
  have hr0 : 0 < g⁻¹ := by positivity
  have hr1 : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simp_rw [← inv_pow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith)
  · have hm := geom_sum_Ico_mul g⁻¹ (show 1 ≤ k from hk)
    have hS : (∑ i ∈ Finset.Ico 1 k, g⁻¹ ^ i) * (1 - g⁻¹) ≤ g⁻¹ := by
      have : 0 ≤ g⁻¹ ^ k := by positivity
      nlinarith
    have hpos : 0 < 1 - g⁻¹ := by linarith
    have he : 1 / (g - 1) = g⁻¹ / (1 - g⁻¹) := by
      have : g ≠ 0 := by linarith
      have : g - 1 ≠ 0 := by linarith
      field_simp
    rw [he, le_div_iff₀ hpos]
    exact hS

/- English proof (translation)
Introduce `g hg k`. Establish `hg0 : 0 < g` using `by linarith`. Rewrite using `[Finset.prod_inv_distrib]`. Establish `hW` using `weier (Finset.Ico 1 k) (fun i => (g ^ i)⁻¹) (fun i _ => by positivity) (fun i hi => by`. Establish `hi1 : i ≠ 0`.

Use `(Finset.mem_Ico.mp hi).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))`. Establish `hG` using `geom_le g hg k`. Establish `hq : g / (g + 3) ≤ 1 - 1 / (g - 1)`.

Establish `h1 : 0 < g - 1` using `by linarith`. Establish `h3 : 0 < g + 3` using `by linarith`. Rewrite using `[div_le_iff₀ h3, sub_mul, div_mul_eq_mul_div, one_mul, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ h1]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP : g / (g + 3) ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)`.

Establish `hW' : 1 - ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)` using `hW`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hPpos : 0 < ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)` using `lt_of_lt_of_le (by positivity) hP`. Rewrite using `[inv_le_comm₀ hPpos (by positivity)]`. Establish `: (1 + 3 / g)⁻¹ = g / (g + 3)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `hP`.
-/
theorem gamma_product_identity : Formalism.YangianSpanCharacter.E.GGProd := by
  intro g hg k
  have hg0 : 0 < g := by linarith
  rw [Finset.prod_inv_distrib]
  have hW := weier (Finset.Ico 1 k) (fun i => (g ^ i)⁻¹)
    (fun i _ => by positivity)
    (fun i hi => by
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Ico.mp hi).1; omega
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))
  have hG := geom_le g hg k
  have hq : g / (g + 3) ≤ 1 - 1 / (g - 1) := by
    have h1 : 0 < g - 1 := by linarith
    have h3 : 0 < g + 3 := by linarith
    rw [div_le_iff₀ h3, sub_mul, div_mul_eq_mul_div, one_mul, le_sub_iff_add_le,
      ← le_sub_iff_add_le', div_le_iff₀ h1]
    nlinarith
  have hP : g / (g + 3) ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) := by
    have hW' : 1 - ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) := hW
    linarith
  have hPpos : 0 < ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) :=
    lt_of_lt_of_le (by positivity) hP
  rw [inv_le_comm₀ hPpos (by positivity)]
  have : (1 + 3 / g)⁻¹ = g / (g + 3) := by
    field_simp
  rw [this]; exact hP

/- English proof (translation)
Establish `key` using `(Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q') (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)`. Conclude with `fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩`.
-/
private lemma rep_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (f f' : Fin n → V) (hli : LinearIndependent K (Sum.elim f f')) (p q p' q' : Fin n → K)
    (h : ∑ i, (p i • f i + q i • f' i) = ∑ i, (p' i • f i + q' i • f' i)) :
    ∀ i, p i = p' i ∧ q i = q' i := by
  have key := (Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q')
    (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)
  exact fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩

end Formalism.YangianSpanCharacter.P
