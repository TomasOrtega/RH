import Mathlib

open MvPowerSeries

namespace GlobalTheory.FiltrationMultiplicative

section

variable {O : Type} [CommRing O] [IsLocalRing O]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ↔
      coeff 0 f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff, coeff_zero_eq_constantCoeff_apply]

variable (O) in

def Filt (σ : Type) (N : ℕ) : Set (MvPowerSeries σ O) :=
  {f | ∀ m : σ →₀ ℕ, coeff m f ∈ IsLocalRing.maximalIdeal O ^ (N - Finsupp.degree m)}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem filt_mul {σ : Type} {a b : ℕ} {f g : MvPowerSeries σ O}
    (hf : f ∈ Filt O σ a) (hg : g ∈ Filt O σ b) : f * g ∈ Filt O σ (a + b) := by
  classical
  intro m
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree m := by
    rw [← map_add, hpm]
  have := Ideal.mul_mem_mul (hf p.1) (hg p.2)
  rw [← pow_add] at this
  exact Ideal.pow_le_pow_right (by omega) this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem filt_zero {σ : Type} (f : MvPowerSeries σ O) : f ∈ Filt O σ 0 := by
  intro m
  simp

variable (O) in

def FiltIdeal (σ : Type) (N : ℕ) : Ideal (MvPowerSeries σ O) where
  carrier := Filt O σ N
  add_mem' := by
    intro f g hf hg m
    rw [map_add]
    exact Ideal.add_mem _ (hf m) (hg m)
  zero_mem' := by
    intro m
    simp
  smul_mem' := by
    intro c f hf
    have := filt_mul (filt_zero c) hf
    simpa using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem max_le_filt_one {σ : Type} :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ≤ FiltIdeal O σ 1 := by
  intro f hf m
  by_cases h : Finsupp.degree m = 0
  · have hm : m = 0 := (Finsupp.degree_eq_zero_iff m).mp h
    subst hm
    simpa using (mem_max_iff f).mp hf
  · have : 1 - Finsupp.degree m = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem pow_le_filt {σ : Type} (N : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ N ≤ FiltIdeal O σ N := by
  induction N with
  | zero => intro f _; exact filt_zero f
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs
    exact filt_mul (ih hr) (max_le_filt_one hs)

def IsFirst {a : ℕ} (m : Fin a →₀ ℕ) (i : Fin a) : Prop := m i ≠ 0 ∧ ∀ j, j < i → m j = 0

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem isFirst_unique {a : ℕ} {m : Fin a →₀ ℕ} {i j : Fin a} (hi : IsFirst m i)
    (hj : IsFirst m j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (hj.2 i h) hi.1
  · exact h
  · exact absurd (hi.2 j h) hj.1

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem isFirst_exists {a : ℕ} {m : Fin a →₀ ℕ} (hm : m ≠ 0) : ∃ i, IsFirst m i := by
  have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
  refine ⟨m.support.min' hne, Finsupp.mem_support_iff.mp (Finset.min'_mem _ _), fun j hj => ?_⟩
  by_contra h
  exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hj)

open Classical in

noncomputable def part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) :
    MvPowerSeries (Fin a) O :=
  fun q => if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (q : Fin a →₀ ℕ) :
    coeff q (part f i) =
      if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0 :=
  rfl

open Classical in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_X_mul_part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if IsFirst m i then coeff m f else 0 := by
  rw [X_def, coeff_monomial_mul, one_mul]
  by_cases h : Finsupp.single i 1 ≤ m
  · rw [if_pos h, coeff_part, tsub_add_cancel_of_le h]
  · rw [if_neg h, if_neg]
    intro hf
    apply h
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hf.1

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem decomp {a : ℕ} (f : MvPowerSeries (Fin a) O) :
    f = C (coeff 0 f) + ∑ i, X i * part f i := by
  classical
  ext m
  rw [map_add, map_sum]
  simp_rw [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm
    simp [IsFirst]
  · obtain ⟨i, hi⟩ := isFirst_exists hm
    rw [Finset.sum_eq_single i, if_pos hi, coeff_C, if_neg hm, zero_add]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (isFirst_unique h hi)
    · intro h
      exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem part_mem {a N : ℕ} {f : MvPowerSeries (Fin a) O} (hf : f ∈ Filt O (Fin a) (N + 1))
    (i : Fin a) : part f i ∈ Filt O (Fin a) N := by
  classical
  intro q
  rw [coeff_part]
  split_ifs
  · have := hf (q + Finsupp.single i 1)
    rwa [map_add, Finsupp.degree_single,
      show N + 1 - (Finsupp.degree q + 1) = N - Finsupp.degree q by omega] at this
  · exact Ideal.zero_mem _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem C_mem_pow {σ : Type} (n : ℕ) {c : O} (hc : c ∈ IsLocalRing.maximalIdeal O ^ n) :
    (C c : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ n := by
  have h1 : Ideal.map (C : O →+* MvPowerSeries σ O) (IsLocalRing.maximalIdeal O) ≤
      IsLocalRing.maximalIdeal (MvPowerSeries σ O) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff, coeff_zero_C]
    exact hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* MvPowerSeries σ O) hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem filt_le_pow {a : ℕ} (N : ℕ) : ∀ f : MvPowerSeries (Fin a) O, f ∈ Filt O (Fin a) N →
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N := by
  induction N with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    rw [decomp f]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)
    · apply C_mem_pow
      simpa using hf 0
    · rw [pow_succ']
      exact Ideal.mul_mem_mul ((mem_max_iff _).mpr (by simp)) (ih _ (part_mem hf i))

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {a : ℕ} (N : ℕ)
    (f : MvPowerSeries (Fin a) O),
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ↔
      ∀ (m : Fin a →₀ ℕ), (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f ∈
        IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m) := by
  intro O _ _ a N f
  exact ⟨fun h => pow_le_filt N h, filt_le_pow N f⟩

end GlobalTheory.FiltrationMultiplicative
