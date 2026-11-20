import Formalism.FormalGroupWitt.Statement

noncomputable section

universe u

namespace Formalism.FG
namespace ShiftFEAux

open MvPowerSeries

variable {K : Type*} [Field K] {l m : ℕ}

/- English proof (translation)
The claim follows from `Nat.pow_right_injective (le_trans hl (Nat.le_self_pow two_ne_zero l)) h`.
-/
lemma pow_inj (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b :=
  Nat.pow_right_injective (le_trans hl (Nat.le_self_pow two_ne_zero l)) h

/- English proof (translation)
The claim follows from `pow_inj hl (h.trans (pow_zero _).symm)`.
-/
lemma eq_zero_of_pow_eq_one (hl : 2 ≤ l) {a : ℕ} (h : (l ^ 2) ^ a = 1) : a = 0 :=
  pow_inj hl (h.trans (pow_zero _).symm)

/- English proof (translation)
Rewrite using `[coeff_apply]`. Both sides reduce to the same expression.
-/
lemma coeff_shiftLog (j : ZMod m) (n : ZMod m →₀ ℕ) :
    coeff n (shiftLog K l m j) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  rw [coeff_apply]; rfl

/- English proof (translation)
Rewrite using `[coeff_shiftLog, Finsupp.degree_single]`. Rewrite using `[Finset.sum_eq_single e]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `h`. Use `congrArg Finsupp.degree h` as an intermediate fact. Simplify using `only [Finsupp.degree_single] at this`. Conclude with `hb (pow_inj hl this).symm`. Introduce `he exfalso`.

Apply `he` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`. Establish `: e < (l ^ 2) ^ e` using `Nat.lt_pow_self (by nlinarith)`. Use linear arithmetic over natural numbers and integers.
-/
lemma coeff_shiftLog_single (hl : 2 ≤ l) (j : ZMod m) (e : ℕ) :
    coeff (Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) (shiftLog K l m j) =
      ((l : K) ^ e)⁻¹ := by
  rw [coeff_shiftLog, Finsupp.degree_single]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    exact hb (pow_inj hl this).symm
  · intro he
    exfalso; apply he
    rw [Finset.mem_range]
    have : e < (l ^ 2) ^ e := Nat.lt_pow_self (by nlinarith)
    omega

/- English proof (translation)
Rewrite using `[coeff_shiftLog]`. Conclude with `Finset.sum_eq_zero fun e _ => if_neg (h e)`.
-/
lemma coeff_shiftLog_zero (j : ZMod m) (n : ZMod m →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) :
    coeff n (shiftLog K l m j) = 0 := by
  rw [coeff_shiftLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_map, coeff_shiftLog, map_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [map_inv₀]`.
-/
lemma map_shiftLog (σ : K →+* K) (k : ZMod m) :
    map σ (shiftLog K l m k) = shiftLog K l m k := by
  ext n
  rw [coeff_map, coeff_shiftLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [map_inv₀]

/- English proof (translation)
Use `⟨fun j => ?_, fun j i => ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Apply `coeff_shiftLog_zero` to reduce the goal to its premises. Introduce `e h`. Use `congrArg Finsupp.degree h` as an intermediate fact.

Simplify using `only [Finsupp.degree_single] at this`. Establish `hpos : 0 < (l ^ 2) ^ e` using `by positivity`. Establish `h0 : (0 : ZMod m →₀ ℕ).degree = 0` using `by simp [Finsupp.degree]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Use `coeff_shiftLog_single (K := K) hl i 0` as an intermediate fact. Simplify using `using this`. Rewrite using `[if_neg hij]`. Apply `coeff_shiftLog_zero` to reduce the goal to its premises.

Introduce `e h`. Establish `hd` using `congrArg Finsupp.degree h`. Simplify using `only [Finsupp.degree_single] at hd`. Establish `he` using `eq_zero_of_pow_eq_one hl hd.symm`. Substitute `he` using the available equality.

Apply `hij` to reduce the goal to its premises. Simplify using `using (Finsupp.single_left_inj one_ne_zero).mp h`.
-/
lemma idMod2 (hl : 2 ≤ l) : IsIdMod2 (shiftLog K l m) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_shiftLog_zero
    intro e h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    have hpos : 0 < (l ^ 2) ^ e := by positivity
    have h0 : (0 : ZMod m →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega
  · by_cases hij : i = j
    · subst hij
      have := coeff_shiftLog_single (K := K) hl i 0
      simpa using this
    · rw [if_neg hij]
      apply coeff_shiftLog_zero
      intro e h
      have hd := congrArg Finsupp.degree h
      simp only [Finsupp.degree_single] at hd
      have he := eq_zero_of_pow_eq_one hl hd.symm
      subst he
      apply hij
      simpa using (Finsupp.single_left_inj one_ne_zero).mp h

/- English proof (translation)
Establish `hl2 : 2 ≤ l` using `hl.two_le`. Establish `hsum : ∑ k, shiftMat K m j k • MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (shiftLog K l m (j - 1))`. Simplify using `[shiftMat, map_shiftLog]`. Rewrite using `[hsum]`. Use extensionality with `n`.

Simplify using `only [map_sub, map_smul, smul_eq_mul, coeff_X]`. Distinguish the cases in `hA : ∃ e : ℕ, n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)`. Take `⟨e, rfl⟩` from `hA`. Rewrite using `[coeff_shiftLog_single hl2]`. Take `_ | e` from `e`.

Simplify using `only [Nat.cast_zero, sub_zero, pow_zero, inv_one, if_true]`. Rewrite using `[coeff_expand_of_not_dvd (i := j)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finsupp.single_eq_same, Nat.dvd_one]`. Introduce `h`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hne : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) ≠ Finsupp.single j 1`. Introduce `h`. Establish `hd` using `congrArg Finsupp.degree h`. Simplify using `only [Finsupp.degree_single] at hd`.

Conclude with `absurd (eq_zero_of_pow_eq_one hl2 hd) (Nat.succ_ne_zero e)`. Rewrite using `[if_neg hne]`. Establish `hn : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) = (l ^ 2) • Finsupp.single ((j - 1) - (e : ZMod m)) ((l ^ 2) ^ e)`. Rewrite using `[Finsupp.smul_single, smul_eq_mul, ← pow_succ']`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hn, coeff_expand_smul, coeff_shiftLog_single hl2]`. Expand and normalize the polynomial expressions, which then agree. Use `push Not at hA`.

Rewrite using `[coeff_shiftLog_zero j n hA, if_neg (by simpa using hA 0)]`. It suffices to establish `h : coeff n (MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (shiftLog K l m (j - 1))) = 0 by rw [h]; ring`. Distinguish the cases in `hd : ∀ i, l ^ 2 ∣ n i`. Establish `hn : n = (l ^ 2) • Finsupp.mapRange (fun x => x / l ^ 2) (Nat.zero_div _) n`. Use extensionality with `i`.

Simplify using `[Nat.mul_div_cancel' (hd i)]`. Rewrite using `[hn, coeff_expand_smul]`. Apply `coeff_shiftLog_zero` to reduce the goal to its premises. Introduce `e he`. Apply `hA (e + 1)` to reduce the goal to its premises.

Rewrite using `[hn, he, Finsupp.smul_single, smul_eq_mul, ← pow_succ']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `push Not at hd`.

Take `⟨i, hi⟩` from `hd`. Conclude with `coeff_expand_of_not_dvd _ _ _ hi`.
-/
lemma main [CharZero K] (hl : l.Prime) [NeZero m] (σ : K →+* K) (j : ZMod m) :
    shiftLog K l m j - (l : K)⁻¹ • ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.X j := by
  have hl2 : 2 ≤ l := hl.two_le
  have hsum : ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) =
      MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (shiftLog K l m (j - 1)) := by
    simp [shiftMat, map_shiftLog]
  rw [hsum]
  ext n
  simp only [map_sub, map_smul, smul_eq_mul, coeff_X]
  by_cases hA : ∃ e : ℕ, n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)
  · obtain ⟨e, rfl⟩ := hA
    rw [coeff_shiftLog_single hl2]
    obtain _ | e := e
    · simp only [Nat.cast_zero, sub_zero, pow_zero, inv_one, if_true]
      rw [coeff_expand_of_not_dvd (i := j)]
      · ring
      · rw [Finsupp.single_eq_same, Nat.dvd_one]
        intro h
        nlinarith
    · have hne : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) ≠
          Finsupp.single j 1 := by
        intro h
        have hd := congrArg Finsupp.degree h
        simp only [Finsupp.degree_single] at hd
        exact absurd (eq_zero_of_pow_eq_one hl2 hd) (Nat.succ_ne_zero e)
      rw [if_neg hne]
      have hn : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) =
          (l ^ 2) • Finsupp.single ((j - 1) - (e : ZMod m)) ((l ^ 2) ^ e) := by
        rw [Finsupp.smul_single, smul_eq_mul, ← pow_succ']
        congr 1
        push_cast
        ring
      rw [hn, coeff_expand_smul, coeff_shiftLog_single hl2]
      ring
  · push Not at hA
    rw [coeff_shiftLog_zero j n hA, if_neg (by simpa using hA 0)]
    suffices h : coeff n (MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
        (shiftLog K l m (j - 1))) = 0 by rw [h]; ring
    by_cases hd : ∀ i, l ^ 2 ∣ n i
    · have hn : n = (l ^ 2) • Finsupp.mapRange (fun x => x / l ^ 2) (Nat.zero_div _) n := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [hn, coeff_expand_smul]
      apply coeff_shiftLog_zero
      intro e he
      apply hA (e + 1)
      rw [hn, he, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      congr 1
      push_cast
      ring
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      exact coeff_expand_of_not_dvd _ _ _ hi

end ShiftFEAux

open ShiftFEAux in
/- English proof (translation)
Introduce `K _ _ l hl m _ σ`. Conclude with `⟨idMod2 hl.two_le, fun j => main hl σ j⟩`.
-/
theorem shift_functional_equation : Formalism.FG.ShiftFunEq.{u} := by
  intro K _ _ l hl m _ σ
  exact ⟨idMod2 hl.two_le, fun j => main hl σ j⟩

end Formalism.FG
