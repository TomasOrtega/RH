import Mathlib

noncomputable section

open Classical

namespace PI.OrbShared.ExpSum

open MvPowerSeries

variable {K : Type*} [Field K] [CharZero K]

abbrev eS {τ : Type*} (f : MvPowerSeries τ K) : MvPowerSeries τ K :=
  PowerSeries.subst f (PowerSeries.exp K)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h0, h1⟩`. Use extensionality with `i`.

Apply the tactic sequence `fin_cases i <;> simp [h0, h1]`.
-/
theorem fin_two_vector_eq_matrixVecCons (e : Fin 2 →₀ ℕ) (k j : ℕ) :
    e = Finsupp.single 0 k + Finsupp.single 1 j ↔ e 0 = k ∧ e 1 = j := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [h0, h1]

/- English proof (translation)
Rewrite using `[add_pow, map_sum]`. Establish `hterm : ∀ m ∈ Finset.range (n + 1), coeff e ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (n - m) * (n.choose m : MvPowerSeries (Fin 2) K)) = if e 0 = m ∧ e 1 = n - m then (n.choose m : K) else 0`. Introduce `m _`. Rewrite using `[mul_comm, ← nsmul_eq_mul, map_nsmul, X_pow_eq, X_pow_eq, monomial_mul_monomial, coeff_monomial, mul_one, nsmul_eq_mul]`. Simplify using `only [fin_two_vector_eq_matrixVecCons]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Finset.sum_congr rfl hterm]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single (e 0)]`. Rewrite using `[if_pos ⟨rfl, by omega⟩]`.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, _⟩`. Conclude with `hb h1.symm`. Introduce `hb`.

It suffices to derive a contradiction. Apply `hb` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `m hm`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Rewrite `hm` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_X_add_X_pow (n : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) K) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : K) else 0 := by
  rw [add_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (n + 1), coeff e ((X 0 : MvPowerSeries (Fin 2) K) ^ m * X 1 ^ (n - m) *
      (n.choose m : MvPowerSeries (Fin 2) K)) = if e 0 = m ∧ e 1 = n - m then (n.choose m : K) else 0 := by
    intro m _
    rw [mul_comm, ← nsmul_eq_mul, map_nsmul, X_pow_eq, X_pow_eq, monomial_mul_monomial, coeff_monomial,
      mul_one, nsmul_eq_mul]
    simp only [fin_two_vector_eq_matrixVecCons]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h
  · rw [Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro b _ hb
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hb h1.symm
    · intro hb
      exfalso
      apply hb
      rw [Finset.mem_range]
      omega
  · apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rw [Finset.mem_range] at hm
    omega

/- English proof (translation)
Simplify using `[PowerSeries.coeff_exp]`.
-/
theorem coeff_exp_K (n : ℕ) : PowerSeries.coeff n (PowerSeries.exp K) = ((n.factorial : K))⁻¹ := by
  simp [PowerSeries.coeff_exp]

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]`. Simplify using `only [coeff_X_pow, coeff_exp_K, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Use `split_ifs with h`. Rewrite using `[finsum_eq_single _ (e i)]`. Rewrite using `[if_pos h]`.

Introduce `d hd`. Rewrite using `[if_neg]`. Introduce `h'`. Apply `hd` to reduce the goal to its premises. Rewrite using `[h']`.

Simplify using the standard rewrite rules. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `d`. Rewrite using `[if_neg]`. Introduce `h'`.

Apply `h` to reduce the goal to its premises. Rewrite using `[h']`. Simplify using the standard rewrite rules.
-/
private lemma coeff_eS_X (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    coeff e (eS (X i : MvPowerSeries (Fin 2) K)) =
      if e = Finsupp.single i (e i) then ((e i).factorial : K)⁻¹ else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp only [coeff_X_pow, coeff_exp_K, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro h'
      apply hd
      rw [h']
      simp
  · apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp

/- English proof (translation)
Use extensionality with `e`. Establish `hL : coeff e (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) = ((e 0 + e 1).factorial : K)⁻¹ * ((e 0 + e 1).choose (e 0) : K)`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]`. Rewrite using `[finsum_eq_single _ (e 0 + e 1)]`. Rewrite using `[coeff_exp_K, coeff_X_add_X_pow, if_pos rfl, smul_eq_mul]`.

Introduce `d hd`. Rewrite using `[coeff_X_add_X_pow, if_neg (fun h => hd h.symm), smul_zero]`. Rewrite using `[hL, MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]`. Rewrite using `[coeff_eS_X, coeff_eS_X, if_pos (by simp), if_pos (by simp)]`. Simplify using `only [Finsupp.single_eq_same]`.

Establish `h1` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))`. Rewrite `h1` using `[Nat.add_sub_cancel_left]`. Establish `h2 : ((e 0 + e 1).choose (e 0) : K) * (e 0).factorial * (e 1).factorial = (e 0 + e 1).factorial` using `by exact_mod_cast h1`. Establish `f0 : ((e 0).factorial : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`. Establish `f1 : ((e 1).factorial : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`.

Establish `hC : ((e 0 + e 1).choose (e 0) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'`. Rewrite using `[← h2]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨p1, p2⟩ hp hne`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[coeff_eS_X, coeff_eS_X]`. Distinguish the cases in `h1 : p1 = Finsupp.single 0 (p1 0)`. Distinguish the cases in `h2 : p2 = Finsupp.single 1 (p2 1)`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises.

Establish `e0 : e 0 = p1 0`. Rewrite using `[← hp, Finsupp.add_apply, h2]`. Simplify using the standard rewrite rules. Establish `e1 : e 1 = p2 1`. Rewrite using `[← hp, Finsupp.add_apply, h1]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, h2, e0, e1]`. Rewrite using `[if_neg h2, mul_zero]`. Rewrite using `[if_neg h1, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_vector_eq_matrixVecCons e (e 0) (e 1)).mpr ⟨rfl, rfl⟩).symm) h`.
-/
theorem eS_X_add_X : eS (X 0 + X 1 : MvPowerSeries (Fin 2) K) = eS (X 0) * eS (X 1) := by
  ext e
  have hL : coeff e (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) =
      ((e 0 + e 1).factorial : K)⁻¹ * ((e 0 + e 1).choose (e 0) : K) := by
    rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    rw [finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_exp_K, coeff_X_add_X_pow, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_X_add_X_pow, if_neg (fun h => hd h.symm), smul_zero]
  rw [hL, MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
  · rw [coeff_eS_X, coeff_eS_X, if_pos (by simp), if_pos (by simp)]
    simp only [Finsupp.single_eq_same]
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (e 0) (e 1))
    rw [Nat.add_sub_cancel_left] at h1
    have h2 : ((e 0 + e 1).choose (e 0) : K) * (e 0).factorial * (e 1).factorial =
        (e 0 + e 1).factorial := by exact_mod_cast h1
    have f0 : ((e 0).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have f1 : ((e 1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hC : ((e 0 + e 1).choose (e 0) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    rw [← h2]
    field_simp
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_eS_X, coeff_eS_X]
    by_cases h1 : p1 = Finsupp.single 0 (p1 0)
    · by_cases h2 : p2 = Finsupp.single 1 (p2 1)
      · exfalso
        apply hne
        have e0 : e 0 = p1 0 := by
          rw [← hp, Finsupp.add_apply, h2]
          simp
        have e1 : e 1 = p2 1 := by
          rw [← hp, Finsupp.add_apply, h1]
          simp
        rw [h1, h2, e0, e1]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr ((fin_two_vector_eq_matrixVecCons e (e 0) (e 1)).mpr ⟨rfl, rfl⟩).symm) h

variable {τ υ : Type*}

/- English proof (translation)
Rewrite using `[PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb]`.
-/
theorem subst_psubst {b : τ → MvPowerSeries υ K} (hb : HasSubst b) {a : MvPowerSeries τ K}
    (ha : PowerSeries.HasSubst a) (φ : PowerSeries K) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb]

/- English proof (translation)
Set `b : Fin 2 → MvPowerSeries τ K` to `![f, g]`. Apply the tactic sequence `have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [b, hf, hg]`. Establish `h1 : subst b (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) = eS (f + g)`. Rewrite using `[subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_add hb, subst_X hb, subst_X hb]`. Both sides reduce to the same expression.

Establish `h2 : subst b (eS (X 0 : MvPowerSeries (Fin 2) K) * eS (X 1)) = eS f * eS g`. Rewrite using `[subst_mul hb, subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_X hb, subst_X hb]`. Both sides reduce to the same expression. Rewrite using `[← h1, eS_X_add_X, h2]`.
-/
theorem eS_add (f g : MvPowerSeries τ K) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    eS (f + g) = eS f * eS g := by
  let b : Fin 2 → MvPowerSeries τ K := ![f, g]
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun i => by
    fin_cases i <;> simp [b, hf, hg]
  have h1 : subst b (eS (X 0 + X 1 : MvPowerSeries (Fin 2) K)) = eS (f + g) := by
    rw [subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_add hb, subst_X hb,
      subst_X hb]
    rfl
  have h2 : subst b (eS (X 0 : MvPowerSeries (Fin 2) K) * eS (X 1)) = eS f * eS g := by
    rw [subst_mul hb, subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)),
      subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), subst_X hb, subst_X hb]
    rfl
  rw [← h1, eS_X_add_X, h2]

/- English proof (translation)
Use extensionality with `e`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]`. Simplify using `[coeff_exp_K]`. Introduce `d hd`. Simplify using `[zero_pow hd]`.
-/
theorem eS_zero : eS (0 : MvPowerSeries τ K) = 1 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]
  · simp [coeff_exp_K]
  · intro d hd
    simp [zero_pow hd]

/- English proof (translation)
Use `revert hf`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `_`. Simplify using `only [Finset.sum_empty, Finset.prod_empty]`.

Conclude with `eS_zero`. Consider the case `@insert a s ha ih`. Introduce `hf`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, eS_add _ _ (hf a (Finset.mem_insert_self a s)) ?_, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_eq_zero fun i hi => hf i (Finset.mem_insert_of_mem hi)`.
-/
theorem eS_sum {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries τ K)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) : eS (∑ i ∈ s, f i) = ∏ i ∈ s, eS (f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact eS_zero
  | @insert a s ha ih =>
    intro hf
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      eS_add _ _ (hf a (Finset.mem_insert_self a s)) ?_,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => hf i (Finset.mem_insert_of_mem hi)

/- English proof (translation)
Conclude with `subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero hf) _`.
-/
theorem subst_eS {b : τ → MvPowerSeries υ K} (hb : HasSubst b) (f : MvPowerSeries τ K)
    (hf : constantCoeff f = 0) : subst b (eS f) = eS (subst b f) := by
  exact subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero hf) _

/- English proof (translation)
Rewrite using `[rename_eq_subst, rename_eq_subst]`. Conclude with `subst_eS (HasSubst.X_comp e) f hf`.
-/
theorem rename_eS (e : τ → υ) [Filter.TendstoCofinite e] (f : MvPowerSeries τ K) (hf : constantCoeff f = 0) :
    rename e (eS f) = eS (rename e f) := by
  rw [rename_eq_subst, rename_eq_subst]
  exact subst_eS (HasSubst.X_comp e) f hf

end PI.OrbShared.ExpSum

end
