import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.OddLogRelation
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

/- English proof (translation)
Rewrite using `[MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]`. Both sides reduce to the same expression.
-/
theorem frobVar_eq_expand {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K) :
    frobVar p f = MvPowerSeries.expand p hp f := by
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  rfl

/- English proof (translation)
Rewrite using `[frobVar_eq_expand hp, MvPowerSeries.coeff_expand_smul]`.
-/
theorem coeff_frobVar_smul {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K)
    (m : ι →₀ ℕ) : MvPowerSeries.coeff (p • m) (frobVar p f) = MvPowerSeries.coeff m f := by
  rw [frobVar_eq_expand hp, MvPowerSeries.coeff_expand_smul]

/- English proof (translation)
Rewrite using `[frobVar_eq_expand hp, MvPowerSeries.coeff_expand_of_not_dvd p hp f h]`.
-/
theorem coeff_frobVar_of_not_dvd {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0)
    (f : MvPowerSeries ι K) {n : ι →₀ ℕ} {i : ι} (h : ¬ p ∣ n i) :
    MvPowerSeries.coeff n (frobVar p f) = 0 := by
  rw [frobVar_eq_expand hp, MvPowerSeries.coeff_expand_of_not_dvd p hp f h]

/- English proof (translation)
Establish `hd : ∀ i, p ∣ n i`. Introduce `i`. Assume the negation of the conclusion as `hc`. Conclude with `h (coeff_frobVar_of_not_dvd hp f hc)`. Establish `hn : n = p • n.mapRange (· / p) (by simp)`.

Use extensionality with `i`. Simplify using `only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Conclude with `(Nat.mul_div_cancel' (hd i)).symm`. Use `⟨_, hn, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hn, coeff_frobVar_smul hp]`.

Conclude with `h`.
-/
theorem coeff_frobVar_ne_zero {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0)
    {f : MvPowerSeries ι K} {n : ι →₀ ℕ} (h : MvPowerSeries.coeff n (frobVar p f) ≠ 0) :
    ∃ m : ι →₀ ℕ, n = p • m ∧ MvPowerSeries.coeff m f ≠ 0 := by
  have hd : ∀ i, p ∣ n i := by
    intro i
    by_contra hc
    exact h (coeff_frobVar_of_not_dvd hp f hc)
  have hn : n = p • n.mapRange (· / p) (by simp) := by
    ext i
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact (Nat.mul_div_cancel' (hd i)).symm
  refine ⟨_, hn, ?_⟩
  rw [hn, coeff_frobVar_smul hp] at h
  exact h

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)` using `PowerSeries.HasSubst.of_constantCoeff_zero (by simp)`. Unfold `at1`. Rewrite using `[PowerSeries.coeff_subst hs]`. Simplify using `only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]`. Rewrite using `[finsum_eq_single _ (n x)]`.

Simplify using the standard rewrite rules. Introduce `d hd`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem coeff_single_variable_series {K ι : Type} [Field K] [DecidableEq ι] (x : ι) (f : PowerSeries K)
    (n : ι →₀ ℕ) : MvPowerSeries.coeff n (at1 x f) =
      if n = Finsupp.single x (n x) then PowerSeries.coeff (n x) f else 0 := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold at1
  rw [PowerSeries.coeff_subst hs]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]
  rw [finsum_eq_single _ (n x)]
  · simp
  · intro d hd
    rw [if_neg, mul_zero]
    intro h
    apply hd
    rw [h]
    simp

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_mul, Finset.sum_eq_single (Finsupp.single x (n x), Finsupp.single y (n y))]`. Simplify using `[coeff_single_variable_series]`. Introduce and unpack `⟨a, b⟩ hab hne`. Rewrite `hab` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using `only at hab`.

Simplify using `only [coeff_single_variable_series]`. Distinguish the cases in `ha : a = Finsupp.single x (a x)`. Distinguish the cases in `hb : b = Finsupp.single y (b y)`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises.

Establish `hbx : b x = 0` using `by rw [hb, Finsupp.single_apply, if_neg hxy.symm]`. Establish `hay : a y = 0` using `by rw [ha, Finsupp.single_apply, if_neg hxy]`. Establish `hx : n x = a x` using `by rw [← hab, Finsupp.add_apply, hbx, add_zero]`. Establish `hy : n y = b y` using `by rw [← hab, Finsupp.add_apply, hay, zero_add]`. Rewrite using `[hx, hy, ← ha, ← hb]`.

Rewrite using `[if_neg hb, mul_zero]`. Rewrite using `[if_neg ha, zero_mul]`. Introduce `h`. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises.

Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use extensionality with `z`. Apply the tactic sequence `rcases hall z with rfl | rfl <;> simp [hxy, hxy.symm]`.
-/
theorem coeff_product_single_variables {K ι : Type} [Field K] {x y : ι} (hxy : x ≠ y)
    (hall : ∀ z : ι, z = x ∨ z = y) (f g : PowerSeries K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (at1 x f * at1 y g) =
      PowerSeries.coeff (n x) f * PowerSeries.coeff (n y) g := by
  classical
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single x (n x), Finsupp.single y (n y))]
  · simp [coeff_single_variable_series]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    simp only at hab
    simp only [coeff_single_variable_series]
    by_cases ha : a = Finsupp.single x (a x)
    · by_cases hb : b = Finsupp.single y (b y)
      · exfalso
        apply hne
        have hbx : b x = 0 := by rw [hb, Finsupp.single_apply, if_neg hxy.symm]
        have hay : a y = 0 := by rw [ha, Finsupp.single_apply, if_neg hxy]
        have hx : n x = a x := by rw [← hab, Finsupp.add_apply, hbx, add_zero]
        have hy : n y = b y := by rw [← hab, Finsupp.add_apply, hay, zero_add]
        rw [hx, hy, ← ha, ← hb]
      · rw [if_neg hb, mul_zero]
    · rw [if_neg ha, zero_mul]
  · intro h
    exfalso
    apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext z
    rcases hall z with rfl | rfl <;> simp [hxy, hxy.symm]

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero hf`. Unfold `mvExp`. Rewrite using `[PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := range (n.degree + 1))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_exp, smul_eq_mul]`.

Simplify using the standard rewrite rules. Introduce `k hk`. Simplify using `only [Function.mem_support] at hk`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Assume the negation of the conclusion as `hlt`.

Apply `hk` to reduce the goal to its premises. Rewrite using `[MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using hf) (by omega), smul_zero]`.
-/
theorem coeff_mvExp {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (mvExp f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) := by
  classical
  have hs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  unfold mvExp
  rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := range (n.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp
  · intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using hf)
      (by omega), smul_zero]

/- English proof (translation)
Establish `h2 : 2 ≤ p ^ 2` using `by nlinarith`. Conclude with `Nat.pow_right_injective h2 h`.
-/
theorem powq_inj {p : ℕ} (hp : 2 ≤ p) {i j : ℕ} (h : (p ^ 2) ^ i = (p ^ 2) ^ j) : i = j := by
  have h2 : 2 ≤ p ^ 2 := by nlinarith
  exact Nat.pow_right_injective h2 h

/- English proof (translation)
Establish `h' : (p ^ 2) ^ i = (p ^ 2) ^ j` using `Nat.eq_of_mul_eq_mul_left (by omega) h`. Conclude with `powq_inj hp h'`.
-/
theorem ppowq_inj {p : ℕ} (hp : 2 ≤ p) {i j : ℕ} (h : p * (p ^ 2) ^ i = p * (p ^ 2) ^ j) : i = j := by
  have h' : (p ^ 2) ^ i = (p ^ 2) ^ j := Nat.eq_of_mul_eq_mul_left (by omega) h
  exact powq_inj hp h'

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma lt_pow_self_of_two_le {b : ℕ} (hb : 2 ≤ b) (j : ℕ) : j < b ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith

/- English proof (translation)
Use `lt_pow_self_of_two_le (b := p ^ 2) (by nlinarith) j` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem lt_powq {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : j < (p ^ 2) ^ j + 1 := by
  have := lt_pow_self_of_two_le (b := p ^ 2) (by nlinarith) j
  omega

/- English proof (translation)
Establish `h1` using `lt_powq hp j`. Use polynomial arithmetic with `[Nat.zero_le ((p ^ 2) ^ j)]`.
-/
theorem lt_ppowq {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : j < p * (p ^ 2) ^ j + 1 := by
  have h1 := lt_powq hp j
  nlinarith [Nat.zero_le ((p ^ 2) ^ j)]

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem powq_succ (p j : ℕ) : (p ^ 2) ^ (j + 1) = p * (p * (p ^ 2) ^ j) := by
  ring

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single j0]`. Rewrite using `[if_pos hP]`. Introduce `b _ hb`. Rewrite using `[if_neg (fun h => hb (hu b h))]`. Introduce `h`.

Conclude with `absurd (Finset.mem_range.mpr h0) h`.
-/
theorem sum_range_ite_unique {M : Type} [AddCommMonoid M] (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c : ℕ → M) (j0 : ℕ) (h0 : j0 < N) (hP : P j0) (hu : ∀ j, P j → j = j0) :
    (∑ j ∈ range N, if P j then c j else 0) = c j0 := by
  rw [Finset.sum_eq_single j0]
  · rw [if_pos hP]
  · intro b _ hb
    rw [if_neg (fun h => hb (hu b h))]
  · intro h
    exact absurd (Finset.mem_range.mpr h0) h

/- English proof (translation)
Unfold `lgF`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `sum_range_ite_unique _ (fun i => (p ^ 2) ^ j = (p ^ 2) ^ i) (fun i => ((p : K) ^ i)⁻¹) j (lt_powq hp j) rfl (fun i h => powq_inj hp h.symm)`.
-/
theorem coeff_lgF_pow (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ j) (lgF K p) = ((p : K) ^ j)⁻¹ := by
  unfold lgF
  rw [PowerSeries.coeff_mk]
  exact sum_range_ite_unique _ (fun i => (p ^ 2) ^ j = (p ^ 2) ^ i) (fun i => ((p : K) ^ i)⁻¹) j
    (lt_powq hp j) rfl (fun i h => powq_inj hp h.symm)

/- English proof (translation)
Unfold `lgF at h`. Rewrite `h` using `[PowerSeries.coeff_mk]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg (hc i)]`.
-/
theorem coeff_lgF_ne_zero {K : Type} [Field K] {p n : ℕ}
    (h : PowerSeries.coeff n (lgF K p) ≠ 0) : ∃ j, n = (p ^ 2) ^ j := by
  unfold lgF at h
  rw [PowerSeries.coeff_mk] at h
  by_contra hc
  push_neg at hc
  apply h
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (hc i)]

/- English proof (translation)
Unfold `g0F`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `sum_range_ite_unique _ (fun i => p * (p ^ 2) ^ j = p * (p ^ 2) ^ i) (fun i => ((p : K) ^ (i + 1))⁻¹) j (lt_ppowq hp j) rfl (fun i h => ppowq_inj hp h.symm)`.
-/
theorem coeff_g0F_of (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ j) (g0F K p) = ((p : K) ^ (j + 1))⁻¹ := by
  unfold g0F
  rw [PowerSeries.coeff_mk]
  exact sum_range_ite_unique _ (fun i => p * (p ^ 2) ^ j = p * (p ^ 2) ^ i)
    (fun i => ((p : K) ^ (i + 1))⁻¹) j (lt_ppowq hp j) rfl (fun i h => ppowq_inj hp h.symm)

/- English proof (translation)
Unfold `g0F at h`. Rewrite `h` using `[PowerSeries.coeff_mk]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg (hc i)]`.
-/
theorem coeff_g0F_ne_zero {K : Type} [Field K] {p n : ℕ}
    (h : PowerSeries.coeff n (g0F K p) ≠ 0) : ∃ j, n = p * (p ^ 2) ^ j := by
  unfold g0F at h
  rw [PowerSeries.coeff_mk] at h
  by_contra hc
  push_neg at hc
  apply h
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg (hc i)]

def AA (K : Type) [Field K] (p : ℕ) (x y : Fin 2) : MvPowerSeries (Fin 2) K :=
  fun n => ∑ i ∈ range (n x + 1), ∑ j ∈ range (n y + 1),
    if i ≤ j ∧ n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Aser_eq (K : Type) [Field K] (p : ℕ) : Aser K p = AA K p 0 1 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Aser'_eq (K : Type) [Field K] (p : ℕ) : Aser' K p = AA K p 1 0 := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `AA K p x y n = _`. Simplify using `only [AA]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[if_pos ⟨hij, hx, hy⟩]`.

Introduce `b _ hb`. Use `if_neg ?_` and prove the remaining obligations. Introduce and unpack `⟨_, _, h⟩`. Conclude with `hb (ppowq_inj hp (h.symm.trans hy))`. Introduce `hj`.

Conclude with `absurd (Finset.mem_range.mpr (by rw [hy]; exact lt_ppowq hp j)) hj`. Introduce `b _ hb`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`. Use `if_neg ?_` and prove the remaining obligations.

Introduce and unpack `⟨_, h, _⟩`. Conclude with `hb (powq_inj hp (h.symm.trans hx))`. Introduce `hi`. Conclude with `absurd (Finset.mem_range.mpr (by rw [hx]; exact lt_powq hp i)) hi`.
-/
theorem coeff_AA_of (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    {i j : ℕ} (hij : i ≤ j) (hx : n x = (p ^ 2) ^ i) (hy : n y = p * (p ^ 2) ^ j) :
    MvPowerSeries.coeff n (AA K p x y) = ((p : K) ^ (i + j + 1))⁻¹ := by
  change AA K p x y n = _
  simp only [AA]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hij, hx, hy⟩]
    · intro b _ hb
      refine if_neg ?_
      rintro ⟨_, _, h⟩
      exact hb (ppowq_inj hp (h.symm.trans hy))
    · intro hj
      exact absurd (Finset.mem_range.mpr (by rw [hy]; exact lt_ppowq hp j)) hj
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    refine if_neg ?_
    rintro ⟨_, h, _⟩
    exact hb (powq_inj hp (h.symm.trans hx))
  · intro hi
    exact absurd (Finset.mem_range.mpr (by rw [hx]; exact lt_powq hp i)) hi

/- English proof (translation)
Express the relevant statement in the definitionally equal form `AA K p x y n ≠ 0 at h`. Simplify using `only [AA] at h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Use `if_neg ?_` and prove the remaining obligations.

Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `hc i j h1 h2 h3`.
-/
theorem coeff_AA_ne_zero {K : Type} [Field K] {p : ℕ} {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    (h : MvPowerSeries.coeff n (AA K p x y) ≠ 0) :
    ∃ i j, i ≤ j ∧ n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j := by
  change AA K p x y n ≠ 0 at h
  simp only [AA] at h
  by_contra hc
  push_neg at hc
  apply h
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  refine if_neg ?_
  rintro ⟨h1, h2, h3⟩
  exact hc i j h1 h2 h3

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem finset_fin_two_eq_cases : ∀ x y : Fin 2, x ≠ y → ∀ z, z = x ∨ z = y := by
  decide

/- English proof (translation)
Establish `hn : n = p • (Finsupp.single x ((p ^ 2) ^ i) + Finsupp.single y (p * (p ^ 2) ^ j))`. Use extensionality with `z`. Break down `finset_fin_two_eq_cases x y hxy z with rfl | rfl` into its components or cases. Simplify using `[hx, hxy.symm]`. Simplify using `[hy, hxy, powq_succ]`.

Rewrite using `[hn, coeff_frobVar_smul (by omega)]`. Conclude with `coeff_AA_of K hp hij (by simp [hxy.symm]) (by simp [hxy])`.
-/
theorem coeff_frobVar_AA_of (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2} (hxy : x ≠ y)
    {n : Fin 2 →₀ ℕ} {i j : ℕ} (hij : i ≤ j) (hx : n x = p * (p ^ 2) ^ i)
    (hy : n y = (p ^ 2) ^ (j + 1)) :
    MvPowerSeries.coeff n (frobVar p (AA K p x y)) = ((p : K) ^ (i + j + 1))⁻¹ := by
  have hn : n = p • (Finsupp.single x ((p ^ 2) ^ i) + Finsupp.single y (p * (p ^ 2) ^ j)) := by
    ext z
    rcases finset_fin_two_eq_cases x y hxy z with rfl | rfl
    · simp [hx, hxy.symm]
    · simp [hy, hxy, powq_succ]
  rw [hn, coeff_frobVar_smul (by omega)]
  exact coeff_AA_of K hp hij (by simp [hxy.symm]) (by simp [hxy])

/- English proof (translation)
Take `⟨m, rfl, hm⟩` from `coeff_frobVar_ne_zero (by omega) h`. Take `⟨i, j, hij, hx, hy⟩` from `coeff_AA_ne_zero hm`. Conclude with `⟨i, j, hij, by simp [hx], by simp [hy, powq_succ]⟩`.
-/
theorem coeff_frobVar_AA_ne_zero {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2}
    {n : Fin 2 →₀ ℕ} (h : MvPowerSeries.coeff n (frobVar p (AA K p x y)) ≠ 0) :
    ∃ i j, i ≤ j ∧ n x = p * (p ^ 2) ^ i ∧ n y = (p ^ 2) ^ (j + 1) := by
  obtain ⟨m, rfl, hm⟩ := coeff_frobVar_ne_zero (by omega) h
  obtain ⟨i, j, hij, hx, hy⟩ := coeff_AA_ne_zero hm
  exact ⟨i, j, hij, by simp [hx], by simp [hy, powq_succ]⟩

/- English proof (translation)
Introduce `K _ p hp _`. Establish `hp0 : p ≠ 0` using `by omega`. Rewrite using `[← PowerSeries.expand_apply p hp0, ← PowerSeries.expand_apply p hp0]`. Prove the components needed by the constructor for the conclusion. Use extensionality with `n`.

Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]`. Distinguish the cases in `hc : ∃ j, n = p * (p ^ 2) ^ j`. Take `⟨j, rfl⟩` from `hc`. Rewrite using `[coeff_g0F_of K hp, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by omega), coeff_lgF_pow K hp, pow_succ, mul_inv, mul_comm]`. Establish `h1 : PowerSeries.coeff n (g0F K p) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hc (coeff_g0F_ne_zero h)`. Rewrite using `[h1]`. Use `split_ifs with hd`. Take `⟨m, rfl⟩` from `hd`.

Rewrite using `[Nat.mul_div_cancel_left _ (by omega)]`. Establish `h2 : PowerSeries.coeff m (lgF K p) = 0`. Assume the negation of the conclusion as `h`. Take `⟨j, rfl⟩` from `coeff_lgF_ne_zero h`. Conclude with `hc ⟨j, rfl⟩`.

Rewrite using `[h2, mul_zero]`. Rewrite using `[mul_zero]`. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_expand, map_sub, PowerSeries.coeff_X]`. Distinguish the cases in `hc : ∃ j, n = (p ^ 2) ^ j`.

Take `⟨j, rfl⟩` from `hc`. Rewrite using `[coeff_lgF_pow K hp]`. Consider the cases of `j with`. Consider the case `zero`. Establish `: ¬ p ∣ 1`.

Introduce `h`. Use `Nat.le_of_dvd one_pos h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`. Consider the case `succ k`.

Establish `h1 : (p ^ 2) ^ (k + 1) ≠ 1`. Use `lt_powq hp (k + 1)` as an intermediate fact. Establish `h2 : (p ^ 2) ^ (k + 1) = (p ^ 2) ^ 0 → k + 1 = 0` using `powq_inj hp`. Introduce `h`. Conclude with `absurd (h2 (by simpa using h)) (by omega)`.

Rewrite using `[if_neg h1, sub_zero, powq_succ, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by omega), coeff_g0F_of K hp]`. Establish `h1 : PowerSeries.coeff n (lgF K p) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hc (coeff_lgF_ne_zero h)`. Establish `h2 : n ≠ 1` using `fun h => hc ⟨0, by simpa using h⟩`.

Rewrite using `[h1, if_neg h2, sub_zero]`. Use `split_ifs with hd`. Take `⟨m, rfl⟩` from `hd`. Rewrite using `[Nat.mul_div_cancel_left _ (by omega)]`. Assume the negation of the conclusion as `h`.

Take `⟨j, rfl⟩` from `coeff_g0F_ne_zero h`. Conclude with `hc ⟨j + 1, (powq_succ p j).symm⟩`. Both sides reduce to the same expression.
-/
theorem g_zero_relation_holds : OddLogRelation := by
  intro K _ p hp _
  have hp0 : p ≠ 0 := by omega
  rw [← PowerSeries.expand_apply p hp0, ← PowerSeries.expand_apply p hp0]
  constructor
  · ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
    by_cases hc : ∃ j, n = p * (p ^ 2) ^ j
    · obtain ⟨j, rfl⟩ := hc
      rw [coeff_g0F_of K hp, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by omega),
        coeff_lgF_pow K hp, pow_succ, mul_inv, mul_comm]
    · have h1 : PowerSeries.coeff n (g0F K p) = 0 := by
        by_contra h
        exact hc (coeff_g0F_ne_zero h)
      rw [h1]
      split_ifs with hd
      · obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left _ (by omega)]
        have h2 : PowerSeries.coeff m (lgF K p) = 0 := by
          by_contra h
          obtain ⟨j, rfl⟩ := coeff_lgF_ne_zero h
          exact hc ⟨j, rfl⟩
        rw [h2, mul_zero]
      · rw [mul_zero]
  · ext n
    rw [PowerSeries.coeff_expand, map_sub, PowerSeries.coeff_X]
    by_cases hc : ∃ j, n = (p ^ 2) ^ j
    · obtain ⟨j, rfl⟩ := hc
      rw [coeff_lgF_pow K hp]
      cases j with
      | zero =>
        have : ¬ p ∣ 1 := by
          intro h
          have := Nat.le_of_dvd one_pos h
          omega
        simp [this]
      | succ k =>
        have h1 : (p ^ 2) ^ (k + 1) ≠ 1 := by
          have := lt_powq hp (k + 1)
          have h2 : (p ^ 2) ^ (k + 1) = (p ^ 2) ^ 0 → k + 1 = 0 := powq_inj hp
          intro h
          exact absurd (h2 (by simpa using h)) (by omega)
        rw [if_neg h1, sub_zero, powq_succ, if_pos (Dvd.intro _ rfl),
          Nat.mul_div_cancel_left _ (by omega), coeff_g0F_of K hp]
    · have h1 : PowerSeries.coeff n (lgF K p) = 0 := by
        by_contra h
        exact hc (coeff_lgF_ne_zero h)
      have h2 : n ≠ 1 := fun h => hc ⟨0, by simpa using h⟩
      rw [h1, if_neg h2, sub_zero]
      split_ifs with hd
      · obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left _ (by omega)]
        by_contra h
        obtain ⟨j, rfl⟩ := coeff_g0F_ne_zero h
        exact hc ⟨j + 1, (powq_succ p j).symm⟩
      · rfl

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_C_mul, map_sub, coeff_product_single_variables hxy (finset_fin_two_eq_cases x y hxy)]`. Distinguish the cases in `hc : ∃ a b, n x = p * (p ^ 2) ^ a ∧ n y = (p ^ 2) ^ b`. Take `⟨a, b, hnx, hny⟩` from `hc`. Rewrite using `[hnx, hny, coeff_g0F_of K hp, coeff_lgF_pow K hp]`.

Distinguish the cases in `hab : b ≤ a`. Rewrite using `[coeff_AA_of K hp hab hny hnx]`. Establish `h0 : MvPowerSeries.coeff n (frobVar p (AA K p x y)) = 0`. Assume the negation of the conclusion as `hne`. Take `⟨i, j, hij, hx, hy⟩` from `coeff_frobVar_AA_ne_zero hp hne`.

Establish `e1` using `ppowq_inj hp (hnx.symm.trans hx)`. Establish `e2` using `powq_inj hp (hny.symm.trans hy)`. Use linear arithmetic over natural numbers and integers. Establish `e : ((p : K) ^ (a + 1))⁻¹ * ((p : K) ^ b)⁻¹ = ((p : K) ^ (b + a + 1))⁻¹`. Rewrite using `[← mul_inv, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h0, e, sub_self, mul_zero]`. Take `⟨b', rfl⟩ : ∃ b', b = b' + 1` from `⟨b - 1, by omega⟩`. Rewrite using `[coeff_frobVar_AA_of K hp hxy (show a ≤ b' by omega) hnx hny]`.

Establish `h0 : MvPowerSeries.coeff n (AA K p y x) = 0`. Assume the negation of the conclusion as `hne`. Take `⟨i, j, hij, hy, hx⟩` from `coeff_AA_ne_zero hne`. Establish `e1` using `ppowq_inj hp (hnx.symm.trans hx)`. Establish `e2` using `powq_inj hp (hny.symm.trans hy)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h0, sub_zero]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : MvPowerSeries.coeff n (frobVar p (AA K p x y)) = 0`.

Assume the negation of the conclusion as `hne`. Take `⟨i, j, _, hx, hy⟩` from `coeff_frobVar_AA_ne_zero hp hne`. Conclude with `hc ⟨i, j + 1, hx, hy⟩`. Establish `h2 : MvPowerSeries.coeff n (AA K p y x) = 0`. Assume the negation of the conclusion as `hne`.

Take `⟨i, j, _, hy, hx⟩` from `coeff_AA_ne_zero hne`. Conclude with `hc ⟨j, i, hx, hy⟩`. Establish `h3 : PowerSeries.coeff (n x) (g0F K p) * PowerSeries.coeff (n y) (lgF K p) = 0`. Assume the negation of the conclusion as `hne`. Take `⟨a, ha⟩` from `coeff_g0F_ne_zero (left_ne_zero_of_mul hne)`.

Take `⟨b, hb⟩` from `coeff_lgF_ne_zero (right_ne_zero_of_mul hne)`. Conclude with `hc ⟨a, b, ha, hb⟩`. Rewrite using `[h1, h2, h3, sub_zero, mul_zero]`.
-/
theorem frobVar_AA_eq (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {x y : Fin 2}
    (hxy : x ≠ y) :
    frobVar p (AA K p x y) =
      MvPowerSeries.C (p : K) * (at1 x (g0F K p) * at1 y (lgF K p) - AA K p y x) := by
  ext n
  rw [MvPowerSeries.coeff_C_mul, map_sub, coeff_product_single_variables hxy (finset_fin_two_eq_cases x y hxy)]
  by_cases hc : ∃ a b, n x = p * (p ^ 2) ^ a ∧ n y = (p ^ 2) ^ b
  · obtain ⟨a, b, hnx, hny⟩ := hc
    rw [hnx, hny, coeff_g0F_of K hp, coeff_lgF_pow K hp]
    by_cases hab : b ≤ a
    · rw [coeff_AA_of K hp hab hny hnx]
      have h0 : MvPowerSeries.coeff n (frobVar p (AA K p x y)) = 0 := by
        by_contra hne
        obtain ⟨i, j, hij, hx, hy⟩ := coeff_frobVar_AA_ne_zero hp hne
        have e1 := ppowq_inj hp (hnx.symm.trans hx)
        have e2 := powq_inj hp (hny.symm.trans hy)
        omega
      have e : ((p : K) ^ (a + 1))⁻¹ * ((p : K) ^ b)⁻¹ = ((p : K) ^ (b + a + 1))⁻¹ := by
        rw [← mul_inv, ← pow_add]
        congr 2
        omega
      rw [h0, e, sub_self, mul_zero]
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [coeff_frobVar_AA_of K hp hxy (show a ≤ b' by omega) hnx hny]
      have h0 : MvPowerSeries.coeff n (AA K p y x) = 0 := by
        by_contra hne
        obtain ⟨i, j, hij, hy, hx⟩ := coeff_AA_ne_zero hne
        have e1 := ppowq_inj hp (hnx.symm.trans hx)
        have e2 := powq_inj hp (hny.symm.trans hy)
        omega
      rw [h0, sub_zero]
      field_simp
      ring
  · have h1 : MvPowerSeries.coeff n (frobVar p (AA K p x y)) = 0 := by
      by_contra hne
      obtain ⟨i, j, _, hx, hy⟩ := coeff_frobVar_AA_ne_zero hp hne
      exact hc ⟨i, j + 1, hx, hy⟩
    have h2 : MvPowerSeries.coeff n (AA K p y x) = 0 := by
      by_contra hne
      obtain ⟨i, j, _, hy, hx⟩ := coeff_AA_ne_zero hne
      exact hc ⟨j, i, hx, hy⟩
    have h3 : PowerSeries.coeff (n x) (g0F K p) * PowerSeries.coeff (n y) (lgF K p) = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := coeff_g0F_ne_zero (left_ne_zero_of_mul hne)
      obtain ⟨b, hb⟩ := coeff_lgF_ne_zero (right_ne_zero_of_mul hne)
      exact hc ⟨a, b, ha, hb⟩
    rw [h1, h2, h3, sub_zero, mul_zero]

/- English proof (translation)
Introduce `K _ p hp hpK`. Use `⟨frobVar_AA_eq K hp hpK (by decide), ?_⟩` and prove the remaining obligations. Establish `h` using `frobVar_AA_eq K hp hpK (x := 1) (y := 0) (by decide)`. Rewrite using `[mul_comm (at1 0 (lgF K p))]`. Conclude with `h`.
-/
theorem identity_b : IdentityB := by
  intro K _ p hp hpK
  refine ⟨frobVar_AA_eq K hp hpK (by decide), ?_⟩
  have h := frobVar_AA_eq K hp hpK (x := 1) (y := 0) (by decide)
  rw [mul_comm (at1 0 (lgF K p))]
  exact h

/- English proof (translation)
Introduce `K _ p c c' hp hpK`. Establish `hp0 : p ≠ 0` using `by omega`. Take `⟨h1, h2⟩` from `identity_b K p hp hpK`. Unfold `Gser`. Rewrite using `[frobVar_eq_expand hp0, map_sub, map_mul, map_mul, MvPowerSeries.expand_C, MvPowerSeries.expand_C, ← frobVar_eq_expand hp0, ← frobVar_eq_expand hp0, h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem frobenius_expression_g : FrobExprG := by
  intro K _ p c c' hp hpK
  have hp0 : p ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := identity_b K p hp hpK
  unfold Gser
  rw [frobVar_eq_expand hp0, map_sub, map_mul, map_mul, MvPowerSeries.expand_C,
    MvPowerSeries.expand_C, ← frobVar_eq_expand hp0, ← frobVar_eq_expand hp0, h1, h2]
  ring

/- English proof (translation)
Introduce `p i j hp hij`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hq1 : (0 : ℝ) < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Establish `hp1 : (0 : ℝ) < (p : ℝ) - 1` using `by linarith`. Establish `hq0 : (p : ℝ) ^ 2 - 1 ≠ 0` using `hq1.ne'`.

Establish `hp0 : (p : ℝ) - 1 ≠ 0` using `hp1.ne'`. Establish `hLHS : 1 / ((p : ℝ) - 1) + p - 2 = (1 + p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1) - 2`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion.

Introduce `hj`. Substitute `hj` using the available equality. Establish `hi : i = 0` using `by omega`. Substitute `hi` using the available equality. Simplify using `only [pow_zero, mul_one, Nat.cast_zero, zero_add]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `hj`. Rewrite using `[hLHS]`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`.

Establish `hB : ∀ m : ℕ, 1 + (m : ℝ) * ((p : ℝ) ^ 2 - 1) ≤ ((p : ℝ) ^ 2) ^ m`. Introduce `m`. Establish `h` using `one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) ^ 2 - 1 by nlinarith) m`. Establish `e : (1 : ℝ) + ((p : ℝ) ^ 2 - 1) = (p : ℝ) ^ 2` using `by ring`. Rewrite `h` using `[e]`.

Conclude with `h`. Establish `h1` using `hB i`. Establish `h2` using `hB k`. Establish `hk0 : (0 : ℝ) ≤ (k : ℝ) * ((p : ℝ) ^ 2 - 1)` using `mul_nonneg (Nat.cast_nonneg k) hq1.le`. Establish `hpk : (0 : ℝ) ≤ ((p : ℝ) ^ 2) ^ k - 1` using `by linarith`.

Establish `hpq : (1 : ℝ) ≤ p * (p : ℝ) ^ 2` using `by nlinarith`. Establish `hsplit : (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1)) / ((p : ℝ) ^ 2 - 1) - (1 + p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1) = (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1) - 1 - p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1)`. Expand and normalize the polynomial expressions, which then agree. Establish `hmain : (i : ℝ) + k ≤ (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1) - 1 - p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1)`. Rewrite using `[le_div_iff₀ hq1, pow_succ ((p : ℝ) ^ 2) k]`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hpq) hpk]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem valuation_table : ValTable := by
  intro p i j hp hij
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq0 : (p : ℝ) ^ 2 - 1 ≠ 0 := hq1.ne'
  have hp0 : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hLHS : 1 / ((p : ℝ) - 1) + p - 2 = (1 + p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1) - 2 := by
    field_simp
    ring
  constructor
  · intro hj
    subst hj
    have hi : i = 0 := by omega
    subst hi
    simp only [pow_zero, mul_one, Nat.cast_zero, zero_add]
    field_simp
    ring
  · intro hj
    rw [hLHS]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hB : ∀ m : ℕ, 1 + (m : ℝ) * ((p : ℝ) ^ 2 - 1) ≤ ((p : ℝ) ^ 2) ^ m := by
      intro m
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) ^ 2 - 1 by nlinarith) m
      have e : (1 : ℝ) + ((p : ℝ) ^ 2 - 1) = (p : ℝ) ^ 2 := by ring
      rw [e] at h
      exact h
    have h1 := hB i
    have h2 := hB k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) * ((p : ℝ) ^ 2 - 1) := mul_nonneg (Nat.cast_nonneg k) hq1.le
    have hpk : (0 : ℝ) ≤ ((p : ℝ) ^ 2) ^ k - 1 := by linarith
    have hpq : (1 : ℝ) ≤ p * (p : ℝ) ^ 2 := by nlinarith
    have hsplit : (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1)) / ((p : ℝ) ^ 2 - 1) -
        (1 + p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1) =
        (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1) - 1 - p * (p : ℝ) ^ 2) /
          ((p : ℝ) ^ 2 - 1) := by
      ring
    have hmain : (i : ℝ) + k ≤
        (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1) - 1 - p * (p : ℝ) ^ 2) /
          ((p : ℝ) ^ 2 - 1) := by
      rw [le_div_iff₀ hq1, pow_succ ((p : ℝ) ^ 2) k]
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) hpk]
    push_cast
    linarith

/- English proof (translation)
Introduce `K _ _ p ϖ hp hnp hϖ i`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hlt : ‖(p : K)‖ < 1` using `by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1`. Establish `hpow : ‖ϖ‖ ^ (p ^ 2 - 1) = ‖(p : K)‖` using `by rw [← norm_pow, hϖ]`.

Establish `hne : p ^ 2 - 1 ≠ 0`. Establish `: 2 ^ 2 ≤ p ^ 2` using `Nat.pow_le_pow_left hp.two_le 2`. Use linear arithmetic over natural numbers and integers. Establish `hle : ‖ϖ‖ ≤ 1`. Rewrite using `[← pow_le_one_iff_of_nonneg (norm_nonneg ϖ) hne, hpow]`.

Conclude with `hlt.le`. Establish `hfac : (i.factorial : K) ≠ 0`. Introduce `h`. Establish `h2` using `Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat (K := K) hp hlt (Nat.factorial_ne_zero i)`. Rewrite `h2` using `[h, norm_zero, hnp]`.

Conclude with `absurd h2.symm (by positivity)`. Rewrite using `[norm_div, div_le_one (norm_pos_iff.mpr hfac), Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero i), ← hpow, ← pow_mul, norm_pow]`. Use `pow_le_pow_of_le_one (norm_nonneg _) hle ?_` and prove the remaining obligations. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hleg` using `sub_one_mul_padicValNat_factorial (p := p) i`.

Establish `hsq : p ^ 2 - 1 = (p + 1) * (p - 1)`. Take `⟨m, rfl⟩ : ∃ m, p = m + 1` from `⟨p - 1, by have := hp.one_lt; omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `: (m + 1) ^ 2 = (m + 1 + 1) * m + 1` using `by ring`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hsq, mul_assoc, hleg]`. Conclude with `Nat.mul_le_mul_left _ (Nat.sub_le _ _)`.
-/
theorem pi_factorial : PiFactorial := by
  intro K _ _ p ϖ hp hnp hϖ i
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlt : ‖(p : K)‖ < 1 := by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  have hpow : ‖ϖ‖ ^ (p ^ 2 - 1) = ‖(p : K)‖ := by rw [← norm_pow, hϖ]
  have hne : p ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    omega
  have hle : ‖ϖ‖ ≤ 1 := by
    rw [← pow_le_one_iff_of_nonneg (norm_nonneg ϖ) hne, hpow]; exact hlt.le
  have hfac : (i.factorial : K) ≠ 0 := by
    intro h
    have h2 := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat (K := K) hp hlt (Nat.factorial_ne_zero i)
    rw [h, norm_zero, hnp] at h2
    exact absurd h2.symm (by positivity)
  rw [norm_div, div_le_one (norm_pos_iff.mpr hfac),
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero i), ← hpow, ← pow_mul,
    norm_pow]
  refine pow_le_pow_of_le_one (norm_nonneg _) hle ?_
  have : Fact p.Prime := ⟨hp⟩
  have hleg := sub_one_mul_padicValNat_factorial (p := p) i
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
    omega
  rw [hsq, mul_assoc, hleg]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/- English proof (translation)
Introduce `K ι _ _ _ p hp hnp f hf0 hf n`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.one_lt`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hlt : ‖(p : K)‖ < 1` using `by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1`. Establish `hd : ∀ m : ι →₀ ℕ, Formalism.DworkPowerSeriesWeights.dot m (fun _ => (0 : ℝ)) = 0`.

Introduce `m`. Simplify using `[Formalism.DworkPowerSeriesWeights.dot]`. Establish `h` using `Formalism.DworkPowerSeriesWeights.exponential_weight_le.{0, 0} K p hp hlt ι (fun _ => 0) n f hf0 (by`. Introduce `m _`. Rewrite using `[Formalism.DworkPowerSeriesWeights.monoWtGe_iff, hd, sub_zero, hnp, Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]`.

Conclude with `hf m) n le_rfl`. Rewrite `h` using `[Formalism.DworkPowerSeriesWeights.monoWtGe_iff, hd]`. Simplify using `using h`.
-/
theorem exp_integral : ExpIntegral := by
  intro K ι _ _ _ p hp hnp f hf0 hf n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlt : ‖(p : K)‖ < 1 := by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  have hd : ∀ m : ι →₀ ℕ, Formalism.DworkPowerSeriesWeights.dot m (fun _ => (0 : ℝ)) = 0 := by
    intro m; simp [Formalism.DworkPowerSeriesWeights.dot]
  have h := Formalism.DworkPowerSeriesWeights.exponential_weight_le.{0, 0} K p hp hlt ι (fun _ => 0) n f hf0 (by
    intro m _
    rw [Formalism.DworkPowerSeriesWeights.monoWtGe_iff, hd, sub_zero, hnp, Real.inv_rpow hp0.le, ← Real.rpow_neg hp0.le]
    exact hf m) n le_rfl
  rw [Formalism.DworkPowerSeriesWeights.monoWtGe_iff, hd] at h
  simpa using h

/- English proof (translation)
Introduce `K ι _ _ _ p ϖ hp hnp hϖ hh hh0`. Use `⟨fun i => MvPowerSeries.C ((-1) ^ i * (ϖ ^ ((p + 1) * i) / (i.factorial : K))), ?_, ?_⟩` and prove the remaining obligations. Introduce `i n`. Rewrite using `[MvPowerSeries.coeff_C]`. Use `split_ifs`.

Rewrite using `[norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Conclude with `pi_factorial K p ϖ hp hnp hϖ i`. Simplify using the standard rewrite rules. Introduce `n`. Establish `h0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)) = 0`.

Simplify using `[hh0]`. Rewrite using `[coeff_mvExp h0]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e : (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)) ^ k = MvPowerSeries.C ((-(ϖ ^ (p + 1) / (p : K))) ^ k) * hh ^ k`. Rewrite using `[← neg_mul, ← map_neg, mul_pow, ← map_pow]`.

Rewrite using `[e, MvPowerSeries.coeff_C_mul, mul_comm (hh ^ k), MvPowerSeries.coeff_C_mul, neg_pow, div_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem class_exponential : ClassExp := by
  intro K ι _ _ _ p ϖ hp hnp hϖ hh hh0
  classical
  refine ⟨fun i => MvPowerSeries.C ((-1) ^ i * (ϖ ^ ((p + 1) * i) / (i.factorial : K))), ?_, ?_⟩
  · intro i n
    rw [MvPowerSeries.coeff_C]
    split_ifs
    · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact pi_factorial K p ϖ hp hnp hϖ i
    · simp
  · intro n
    have h0 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)) = 0 := by
      simp [hh0]
    rw [coeff_mvExp h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh)) ^ k =
        MvPowerSeries.C ((-(ϖ ^ (p + 1) / (p : K))) ^ k) * hh ^ k := by
      rw [← neg_mul, ← map_neg, mul_pow, ← map_pow]
    rw [e, MvPowerSeries.coeff_C_mul, mul_comm (hh ^ k), MvPowerSeries.coeff_C_mul, neg_pow, div_pow,
      ← pow_mul]
    ring

end Formalism.InvariantFactorPaths.G7
