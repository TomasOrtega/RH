import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFS

noncomputable section

namespace PI.VolStabW

namespace FiniteFieldCounting

/- English proof (translation)
The claim follows from `|∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by classical induction s using Finset.induction_on with | empty => simp | insert j s hj ih => rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj] set P := ∏ j ∈ s, (1 + δ j) have hP : |P| ≤ 1 + |P - 1| := by have := abs_s …`.
-/
theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    set P := ∏ j ∈ s, (1 + δ j)
    have hP : |P| ≤ 1 + |P - 1| := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have e : (1 + δ j) * P - 1 = (P - 1) + δ j * P := by ring
    rw [e]
    have h1 := abs_add_le (P - 1) (δ j * P)
    rw [abs_mul] at h1
    have hpow : (2 : ℝ) ^ (s.card + 1) = 2 * 2 ^ s.card := by ring
    rw [hpow]
    have h2 : |δ j| * |P| ≤ t * (1 + |P - 1|) := mul_le_mul (h j) hP (abs_nonneg _) ht0
    have h3 : 0 ≤ |P - 1| := abs_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h3]

/- English proof (translation)
Establish `ht0 : 0 ≤ (q⁻¹) ^ 2` using `by positivity`. Establish `ht1 : (q⁻¹) ^ 2 ≤ 1` using `pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)`. Use `prod_bound δ _ ht0 ht1 h Finset.univ` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin]`. Establish `h2 : (2 : ℝ) ^ a ≤ 2 ^ M` using `pow_le_pow_right₀ (by norm_num) ha`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

/- English proof (translation)
The claim follows from `pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm`.
-/
theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

/- English proof (translation)
Establish `h1 : a ^ 2 ≤ 2 * M * a` using `by nlinarith`. Use `zify [h1, ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
  zify [h1, ha]
  ring

/- English proof (translation)
Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ a ih`.

Introduce `ha`. Rewrite using `[Finset.sum_range_succ, ih (by omega)]`. Establish `h1 : a ^ 2 ≤ 2 * M * a` using `by nlinarith`. Establish `h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1)` using `by nlinarith`. Establish `h3 : a ≤ M` using `by omega`.

Establish `h4 : 1 ≤ 2 * (M - a)` using `by omega`. Use `zify [h1, h2, h3, h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
    have h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1) := by nlinarith
    have h3 : a ≤ M := by omega
    have h4 : 1 ≤ 2 * (M - a) := by omega
    zify [h1, h2, h3, h4]
    ring

/- English proof (translation)
Establish `hM : q ^ M ≠ 0` using `pow_ne_zero _ hq`. Establish `e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M))`. Introduce `i`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]`. Establish `h1 : q ^ (M * a) ≠ 0` using `pow_ne_zero _ hq`. Establish `h2 : q ^ (a * (M - a)) ≠ 0` using `pow_ne_zero _ hq`. Clear the denominators using the available nonvanishing facts.
-/
theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hM : q ^ M ≠ 0 := pow_ne_zero _ hq
  have e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]
  have h1 : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  field_simp

/- English proof (translation)
Establish `e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) = q ^ (2 * (M - j) - 1) * (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1)))`. Introduce `j`. Establish `: q ^ (2 * (M - j) - 1) ≠ 0` using `pow_ne_zero _ hq`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]`. Establish `h1 : q ^ (2 * M * a - a ^ 2) ≠ 0` using `pow_ne_zero _ hq`. Clear the denominators using the available nonvanishing facts.
-/
theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) =
      q ^ (2 * (M - j) - 1) *
        (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
    intro j
    have : q ^ (2 * (M - j) - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring
  rw [Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]
  have h1 : q ^ (2 * M * a - a ^ 2) ≠ 0 := pow_ne_zero _ hq
  field_simp

/- English proof (translation)
The claim follows from `|-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by have hq0 : q ≠ 0 := by positivity have hMi : q ^ M = q ^ (i : ℕ) * q ^ (M - i) := by rw [← pow_add] congr 1 omega have hi : q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hq0 have e : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by rw [hMi, inv_pow] field …`.
-/
theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hMi : q ^ M = q ^ (i : ℕ) * q ^ (M - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hq0
  have e : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    rw [hMi, inv_pow]
    field_simp
  rw [abs_neg, e, abs_of_nonneg (by positivity)]
  exact inv_pow_le q hq _ (by omega)

/- English proof (translation)
The claim follows from `|-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by have hq0 : q ≠ 0 := by positivity have hexp : q ^ (2 * (M - j) - 1) = q ^ (M - j - 1) * q ^ (M - j) := by rw [← pow_add] congr 1 omega have hi : q ^ (M - j - 1) ≠ 0 := pow_ne_zero _ hq0 have e : |-((- …`.
-/
theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hexp : q ^ (2 * (M - j) - 1) = q ^ (M - j - 1) * q ^ (M - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (M - j - 1) ≠ 0 := pow_ne_zero _ hq0
  have e : |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| = (q⁻¹) ^ (M - j) := by
    rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hexp,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), inv_pow]
    field_simp
  rw [e]
  exact inv_pow_le q hq _ (by omega)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

/- English proof (translation)
Apply `Nat.card_congr` to reduce the goal to its premises. Use `Equiv.subtypeEquiv (p := fun X ↦ ffGram (σ : K →+* K) J X = T) (q := fun Y ↦ ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e) { toFun := fun X r i ↦ e (X r i) invFun := fun Y r i ↦ e.symm (Y r i) left_inv := fun X ↦ by` and prove the remaining obligations. Use function extensionality and compare the values at `r i`. Simplify using the standard rewrite rules. Use `right_inv := fun Y ↦ by`.

Use function extensionality and compare the values at `r i`. Simplify using `} ?_`. Introduce `X`. Establish `key : ∀ r s, ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s = e (ffGram (σ : K →+* K) J X r s)`. Introduce `r s`.

Simplify using `only [ffGram, ffH, map_sum, map_mul, Matrix.map_apply, swapR_apply, ← he]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `r s`.

Express the relevant statement in the definitionally equal form `ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s = _`. Rewrite using `[key, h]`. Both sides reduce to the same expression. Introduce `h`. Use function extensionality and compare the values at `r s`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← key]`. Conclude with `congrFun (congrFun h r) s`.
-/
theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (p := fun X ↦ ffGram (σ : K →+* K) J X = T)
    (q := fun Y ↦ ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e)
    { toFun := fun X r i ↦ e (X r i)
      invFun := fun Y r i ↦ e.symm (Y r i)
      left_inv := fun X ↦ by
        funext r i
        simp
      right_inv := fun Y ↦ by
        funext r i
        simp } ?_
  intro X
  have key : ∀ r s, ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s =
      e (ffGram (σ : K →+* K) J X r s) := by
    intro r s
    simp only [ffGram, ffH, map_sum, map_mul, Matrix.map_apply, swapR_apply, ← he]
    rfl
  constructor
  · intro h
    funext r s
    change ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s = _
    rw [key, h]
    rfl
  · intro h
    funext r s
    apply e.injective
    rw [← key]
    exact congrFun (congrFun h r) s

end FiniteFieldCounting

/- English proof (translation)
Introduce `M`. Use `⟨2 ^ M, ?_⟩` and prove the remaining obligations. Introduce `k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd`. Establish `hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ)` using `by exact_mod_cast Nat.card_pos (α := k)`. Establish `hq0 : (Nat.card k : ℝ) ≠ 0` using `by positivity`.

Break down `hσ.2 with ⟨hK, hdeg, hne⟩ | ⟨e, he⟩` into its components or cases. Use `letI : Field K := hK.toField`. Rewrite using `[hI k K σ hσ.1 hdeg hne h2 M a (by omega) J hJ hJd T hT hTd, FiniteFieldCounting.inert_ratio M a (by omega) _ hq0]`. Conclude with `FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _ (FiniteFieldCounting.inert_delta M a ha _ hq1)`. Establish `hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j`.

Introduce `i j`. Simplify using `only [Matrix.map_apply, ← he, hJ]`. Establish `hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j`. Introduce `i j`. Simplify using `only [Matrix.map_apply, ← he, hT]`.

Establish `hJd' : IsUnit (J.map e).det`. Establish `hd : e J.det = (J.map e).det` using `(e : K →+* k × k).map_det J`. Rewrite using `[← hd]`. Conclude with `hJd.map e`. Establish `hTd' : IsUnit (T.map e).det`.

Establish `hd : e T.det = (T.map e).det` using `(e : K →+* k × k).map_det T`. Rewrite using `[← hd]`. Conclude with `hTd.map e`. Rewrite using `[FiniteFieldCounting.card_transport σ e he J T, hS k M a (by omega) _ hJ' hJd' _ hT' hTd', FiniteFieldCounting.split_ratio M a (by omega) _ hq0]`. Conclude with `FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _ (FiniteFieldCounting.split_delta M a ha _ hq1)`.
-/
theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos (α := k)
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by positivity
  rcases hσ.2 with ⟨hK, hdeg, hne⟩ | ⟨e, he⟩
  · letI : Field K := hK.toField
    rw [hI k K σ hσ.1 hdeg hne h2 M a (by omega) J hJ hJd T hT hTd,
      FiniteFieldCounting.inert_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.inert_delta M a ha _ hq1)
  · have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have hd : e J.det = (J.map e).det := (e : K →+* k × k).map_det J
      rw [← hd]
      exact hJd.map e
    have hTd' : IsUnit (T.map e).det := by
      have hd : e T.det = (T.map e).det := (e : K →+* k × k).map_det T
      rw [← hd]
      exact hTd.map e
    rw [FiniteFieldCounting.card_transport σ e he J T, hS k M a (by omega) _ hJ' hJd' _ hT' hTd',
      FiniteFieldCounting.split_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.split_delta M a ha _ hq1)

/- English proof (translation)
The claim follows from `fFCount_of fFSplit_holds hI`.
-/
theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabW
