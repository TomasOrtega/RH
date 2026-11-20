import Mathlib

namespace GlobalTheory.PowerSeriesIdealPowers

open MvPowerSeries IsLocalRing

variable {O : Type} [CommRing O] [IsLocalRing O]

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`.
-/
theorem mem_max_iff {σ : Type} (f : MvPowerSeries σ O) :
    f ∈ maximalIdeal (MvPowerSeries σ O) ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top]`.
-/
theorem mem_smul_top_iff {S : Type} [CommRing S] (I : Ideal S) (x : S) :
    x ∈ (I • ⊤ : Submodule S S) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro f _ d`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `f hf`.

Rewrite `hf` using `[pow_succ]`. Use `Submodule.mul_induction_on hf ?_ ?_` and prove the remaining obligations. Introduce `x hx y hy d`. Rewrite using `[coeff_mul]`. Use `Ideal.sum_mem _ fun p hp => ?_` and prove the remaining obligations.

Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h1` using `ih x hx p.1`. Establish `h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree)`. Distinguish the cases in `h0 : p.2.degree = 0`. Rewrite `h0` using `[Finsupp.degree_eq_zero_iff]`.

Rewrite using `[h0, coeff_zero_eq_constantCoeff_apply]`. Simplify using `using (mem_max_iff y).1 hy`. Rewrite using `[show 1 - p.2.degree = 0 by omega]; simp`. Establish `hdeg : d.degree = p.1.degree + p.2.degree` using `by rw [← hp, map_add]`. Establish `hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree)` using `by omega`.

Conclude with `Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)`. Introduce `x y hx hy d`. Rewrite using `[map_add]`. Conclude with `add_mem (hx d) (hy d)`.
-/
theorem coeff_mem_of_mem_pow {σ : Type} (n : ℕ) :
    ∀ f ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n, ∀ d : σ →₀ ℕ,
      coeff d f ∈ (maximalIdeal O) ^ (n - d.degree) := by
  classical
  induction n with
  | zero => intro f _ d; simp
  | succ n ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy d
      rw [coeff_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 := ih x hx p.1
      have h2 : coeff p.2 y ∈ (maximalIdeal O) ^ (1 - p.2.degree) := by
        by_cases h0 : p.2.degree = 0
        · rw [Finsupp.degree_eq_zero_iff] at h0
          rw [h0, coeff_zero_eq_constantCoeff_apply]
          simpa using (mem_max_iff y).1 hy
        · rw [show 1 - p.2.degree = 0 by omega]; simp
      have hdeg : d.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
      have hle : n + 1 - d.degree ≤ (n - p.1.degree) + (1 - p.2.degree) := by omega
      exact Ideal.pow_le_pow_right hle (by rw [pow_add]; exact Ideal.mul_mem_mul h1 h2)
    · intro x y hx hy d
      rw [map_add]; exact add_mem (hx d) (hy d)

/- English proof (translation)
Rewrite using `[X, coeff_monomial_mul]`. Simplify using the standard rewrite rules.
-/
theorem coeff_X_mul_add {σ : Type} [DecidableEq σ] (i : σ) (g : MvPowerSeries σ O) (d : σ →₀ ℕ) :
    coeff (d + Finsupp.single i 1) (X i * g) = coeff d g := by
  rw [X, coeff_monomial_mul]
  simp

/- English proof (translation)
Establish `h1 : C c ∈ Ideal.map (C (σ` using `σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc`. Rewrite `h1` using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ n h1` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Rewrite using `[Ideal.mem_comap, mem_max_iff, constantCoeff_C]`. Conclude with `hx`.
-/
theorem C_mem_pow {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by
  have h1 : C c ∈ Ideal.map (C (σ := σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ n h1
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_max_iff, constantCoeff_C]
  exact hx

/- English proof (translation)
Rewrite using `[mem_max_iff, constantCoeff_X]`. Conclude with `zero_mem _`.
-/
theorem X_mem_max {σ : Type} (i : σ) : (X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := by
  rw [mem_max_iff, constantCoeff_X]; exact zero_mem _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro f _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `f hf`.

Set `P : Fin a → (Fin a →₀ ℕ) → Prop` to `fun i d => d i ≠ 0 ∧ ∀ j < i, d j = 0`. Set `fi : Fin a → MvPowerSeries (Fin a) O` to `fun i d => if P i d then coeff d f else 0`. Establish `hfi : ∀ i d, coeff d (fi i) = if P i d then coeff d f else 0` using `fun i d => rfl`. Establish `huniq : ∀ i j d, P i d → P j d → i = j`. Introduce `i j d hi hj`.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. Conclude with `absurd (hj.2 i h) hi.1`. Conclude with `h`. Conclude with `absurd (hi.2 j h) hj.1`. Establish `hexists : ∀ d : Fin a →₀ ℕ, d ≠ 0 → ∃ i, P i d`.

Introduce `d hd`. Establish `hs : d.support.Nonempty` using `Finsupp.support_nonempty_iff.2 hd`. Use `⟨d.support.min' hs, Finsupp.mem_support_iff.1 (Finset.min'_mem _ hs), fun j hj => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.2 hne)) (not_le.2 hj)`.

Establish `hdecomp : f = C (constantCoeff f) + ∑ i, fi i`. Use extensionality with `d`. Rewrite using `[map_add, map_sum, coeff_C]`. Simplify using `only [hfi]`. Distinguish the cases in `hd : d = 0`.

Substitute `hd` using the available equality. Establish `: ∀ i, ¬ P i 0` using `fun i h => h.1 rfl`. Simplify using `[this, coeff_zero_eq_constantCoeff_apply]`. Take `⟨i, hi⟩` from `hexists d hd`. Rewrite using `[if_neg hd, zero_add, Finset.sum_eq_single i (fun j _ hj => by`.

Rewrite using `[if_neg (fun h => hj (huniq _ _ _ h hi))]) (fun h => absurd (Finset.mem_univ i) h),`. Use `if_pos hi]`. Rewrite using `[hdecomp]`. Use `add_mem (C_mem_pow _ _ ?_) (Ideal.sum_mem _ fun i _ => ?_)` and prove the remaining obligations. Simplify `hf 0` using `[coeff_zero_eq_constantCoeff_apply]`.

Establish `hdvd : (X i : MvPowerSeries (Fin a) O) ∣ fi i`. Rewrite using `[X_dvd_iff]`. Introduce `m hm`. Rewrite using `[hfi, if_neg (fun h => h.1 hm)]`. Take `⟨g, hg⟩` from `hdvd`.

Rewrite using `[hg, pow_succ']`. Use `Ideal.mul_mem_mul (X_mem_max i) (ih g fun d => ?_)` and prove the remaining obligations. Rewrite using `[← coeff_X_mul_add i g d, ← hg, hfi]`. Use `split_ifs`. Use `hf (d + Finsupp.single i 1)` as an intermediate fact.

Rewrite `this` using `[map_add, Finsupp.degree_single, show n + 1 - (d.degree + 1) = n - d.degree by omega]`. Then use the resulting hypothesis. Conclude with `zero_mem _`.
-/
theorem mem_pow_of_coeff_mem (a n : ℕ) :
    ∀ f : MvPowerSeries (Fin a) O, (∀ d : Fin a →₀ ℕ, coeff d f ∈ (maximalIdeal O) ^ (n - d.degree)) →
      f ∈ (maximalIdeal (MvPowerSeries (Fin a) O)) ^ n := by
  classical
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    let P : Fin a → (Fin a →₀ ℕ) → Prop := fun i d => d i ≠ 0 ∧ ∀ j < i, d j = 0
    let fi : Fin a → MvPowerSeries (Fin a) O := fun i d => if P i d then coeff d f else 0
    have hfi : ∀ i d, coeff d (fi i) = if P i d then coeff d f else 0 := fun i d => rfl
    have huniq : ∀ i j d, P i d → P j d → i = j := by
      intro i j d hi hj
      rcases lt_trichotomy i j with h | h | h
      · exact absurd (hj.2 i h) hi.1
      · exact h
      · exact absurd (hi.2 j h) hj.1
    have hexists : ∀ d : Fin a →₀ ℕ, d ≠ 0 → ∃ i, P i d := by
      intro d hd
      have hs : d.support.Nonempty := Finsupp.support_nonempty_iff.2 hd
      refine ⟨d.support.min' hs, Finsupp.mem_support_iff.1 (Finset.min'_mem _ hs), fun j hj => ?_⟩
      by_contra hne
      exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.2 hne)) (not_le.2 hj)
    have hdecomp : f = C (constantCoeff f) + ∑ i, fi i := by
      ext d
      rw [map_add, map_sum, coeff_C]
      simp only [hfi]
      by_cases hd : d = 0
      · subst hd
        have : ∀ i, ¬ P i 0 := fun i h => h.1 rfl
        simp [this, coeff_zero_eq_constantCoeff_apply]
      · obtain ⟨i, hi⟩ := hexists d hd
        rw [if_neg hd, zero_add, Finset.sum_eq_single i (fun j _ hj => by
          rw [if_neg (fun h => hj (huniq _ _ _ h hi))]) (fun h => absurd (Finset.mem_univ i) h),
          if_pos hi]
    rw [hdecomp]
    refine add_mem (C_mem_pow _ _ ?_) (Ideal.sum_mem _ fun i _ => ?_)
    · simpa [coeff_zero_eq_constantCoeff_apply] using hf 0
    · have hdvd : (X i : MvPowerSeries (Fin a) O) ∣ fi i := by
        rw [X_dvd_iff]
        intro m hm
        rw [hfi, if_neg (fun h => h.1 hm)]
      obtain ⟨g, hg⟩ := hdvd
      rw [hg, pow_succ']
      refine Ideal.mul_mem_mul (X_mem_max i) (ih g fun d => ?_)
      rw [← coeff_X_mul_add i g d, ← hg, hfi]
      split_ifs
      · have := hf (d + Finsupp.single i 1)
        rwa [map_add, Finsupp.degree_single, show n + 1 - (d.degree + 1) = n - d.degree by omega] at this
      · exact zero_mem _

/- English proof (translation)
Introduce `O _ _ hO a`. Prove the components needed by the constructor for the conclusion. Introduce `f hf`. Simplify using `only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢`. Set `s : (Fin a →₀ ℕ) → ℕ → O` to `fun d k => coeff d (f (k + d.degree))`.

Establish `hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)]`. Introduce `d`. Use `IsPrecomplete.prec hO ?_` and prove the remaining obligations. Introduce `k l hkl`. Rewrite using `[SModEq.sub_mem, mem_smul_top_iff]`.

Establish `h` using `coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d`. Rewrite `h` using `[map_sub, Nat.add_sub_cancel]`. Then use the resulting hypothesis. Use `choose L hL using hs`. Set `Lim : MvPowerSeries (Fin a) O` to `fun d => L d`. Establish `hLim : ∀ d, coeff d Lim = L d` using `fun d => rfl`.

Use `⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hLim]`. Distinguish the cases in `hd : d.degree ≤ n`. Establish `h` using `hL d (n - d.degree)`. Rewrite `h` using `[SModEq.sub_mem, mem_smul_top_iff]`.

Simplify using `only [s, Nat.sub_add_cancel hd] at h`. Conclude with `h`. Rewrite using `[show n - d.degree = 0 by omega]; simp`.
-/
theorem main : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    [IsPrecomplete (IsLocalRing.maximalIdeal O) O] (a : ℕ),
    IsPrecomplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) := by
  intro O _ _ hO a
  constructor
  intro f hf
  simp only [SModEq.sub_mem, mem_smul_top_iff] at hf ⊢
  let s : (Fin a →₀ ℕ) → ℕ → O := fun d k => coeff d (f (k + d.degree))
  have hs : ∀ d, ∃ L : O, ∀ k, s d k ≡ L [SMOD ((maximalIdeal O) ^ k • ⊤ : Submodule O O)] := by
    intro d
    refine IsPrecomplete.prec hO ?_
    intro k l hkl
    rw [SModEq.sub_mem, mem_smul_top_iff]
    have h := coeff_mem_of_mem_pow (k + d.degree) _ (hf (Nat.add_le_add_right hkl _)) d
    rwa [map_sub, Nat.add_sub_cancel] at h
  choose L hL using hs
  let Lim : MvPowerSeries (Fin a) O := fun d => L d
  have hLim : ∀ d, coeff d Lim = L d := fun d => rfl
  refine ⟨Lim, fun n => mem_pow_of_coeff_mem a n _ fun d => ?_⟩
  rw [map_sub, hLim]
  by_cases hd : d.degree ≤ n
  · have h := hL d (n - d.degree)
    rw [SModEq.sub_mem, mem_smul_top_iff] at h
    simp only [s, Nat.sub_add_cancel hd] at h
    exact h
  · rw [show n - d.degree = 0 by omega]; simp
end GlobalTheory.PowerSeriesIdealPowers
