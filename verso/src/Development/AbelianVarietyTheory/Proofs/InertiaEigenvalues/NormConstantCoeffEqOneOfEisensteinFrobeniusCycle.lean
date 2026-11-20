import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

namespace GlobalTheory.BK.Cycle

open PowerSeries GlobalTheory.BK

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def DomTerm (ρ : ℝ) (f : K⟦X⟧) (i : ℕ) (c : ℝ) : Prop :=
  0 < c ∧ ‖coeff i f‖ * ρ ^ i = c ∧ (∀ n, ‖coeff n f‖ * ρ ^ n ≤ c) ∧
    ∀ n < i, ‖coeff n f‖ * ρ ^ n < c

omit [IsUltrametricDist K] in
/- English proof (translation)
Take `⟨hc, hi, hle, hlt⟩` from `h`. Take `⟨hd, hj, hle', hlt'⟩` from `h'`. Establish `hcd : c = d` using `le_antisymm (by rw [← hi]; exact hle' i) (by rw [← hj]; exact hle j)`. Use `⟨?_, hcd⟩` and prove the remaining obligations. Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases.

Establish `hx` using `hlt' i hij`. Rewrite `hx` using `[hi, hcd]`. Conclude with `absurd hx (lt_irrefl d)`. Conclude with `hij`. Establish `hx` using `hlt j hij`.

Rewrite `hx` using `[hj, ← hcd]`. Conclude with `absurd hx (lt_irrefl c)`.
-/
theorem DomTerm.unique {ρ : ℝ} {f : K⟦X⟧} {i j : ℕ} {c d : ℝ} (h : DomTerm ρ f i c)
    (h' : DomTerm ρ f j d) : i = j ∧ c = d := by
  obtain ⟨hc, hi, hle, hlt⟩ := h
  obtain ⟨hd, hj, hle', hlt'⟩ := h'
  have hcd : c = d := le_antisymm (by rw [← hi]; exact hle' i) (by rw [← hj]; exact hle j)
  refine ⟨?_, hcd⟩
  rcases lt_trichotomy i j with hij | hij | hij
  · have hx := hlt' i hij
    rw [hi, hcd] at hx
    exact absurd hx (lt_irrefl d)
  · exact hij
  · have hx := hlt j hij
    rw [hj, ← hcd] at hx
    exact absurd hx (lt_irrefl c)

/- English proof (translation)
Break down `s.eq_empty_or_nonempty with rfl | hs` into its components or cases. Simplify using `using hc`. Take `⟨p, hp, hle⟩` from `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs F`. Conclude with `lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hw) (h p hp)`.
-/
theorem norm_sum_mul_lt {ι : Type} (s : Finset ι) (F : ι → K) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 < c)
    (h : ∀ p ∈ s, ‖F p‖ * w < c) : ‖∑ p ∈ s, F p‖ * w < c := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hc
  · obtain ⟨p, hp, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs F
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hw) (h p hp)

/- English proof (translation)
Rewrite using `[norm_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma norm_mul_mul_pow_add_eq_mul_weighted {L : Type} [NormedField L] (ρ : ℝ) (x y : L) (a b : ℕ) :
    ‖x * y‖ * ρ ^ (a + b) = (‖x‖ * ρ ^ a) * (‖y‖ * ρ ^ b) := by
  rw [norm_mul, pow_add]
  ring

/- English proof (translation)
Establish `hb : ‖∑ p ∈ s, F p‖ ≤ c / w` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hc hw.le) (fun p hp => (le_div_iff₀ hw).mpr (h p hp))`. Conclude with `(le_div_iff₀ hw).mp hb`.
-/
private lemma norm_sum_mul_le_of_forall_norm_mul_le {ι : Type} (s : Finset ι) (F : ι → K) {w c : ℝ} (hw : 0 < w)
    (hc : 0 ≤ c) (h : ∀ p ∈ s, ‖F p‖ * w ≤ c) : ‖∑ p ∈ s, F p‖ * w ≤ c := by
  have hb : ‖∑ p ∈ s, F p‖ ≤ c / w :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hc hw.le)
      (fun p hp => (le_div_iff₀ hw).mpr (h p hp))
  exact (le_div_iff₀ hw).mp hb

/- English proof (translation)
Take `⟨hc, hi, hle, hlt⟩` from `h`. Take `⟨hd, hj, hle', hlt'⟩` from `h'`. Establish `hcd : 0 < c * d` using `mul_pos hc hd`. Establish `hnn : ∀ (x : K) (n : ℕ), 0 ≤ ‖x‖ * ρ ^ n` using `fun x n => mul_nonneg (norm_nonneg x) (pow_pos hρ n).le`. Establish `term_lt : ∀ a b, (a < i ∨ b < j) → ‖coeff a f * coeff b g‖ * ρ ^ (a + b) < c * d`.

Introduce `a b hab`. Rewrite using `[norm_mul_mul_pow_add_eq_mul_weighted]`. Break down `hab with ha | hb` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Establish `sum_lt : ∀ (n : ℕ) (s : Finset (ℕ × ℕ)), (∀ p ∈ s, p.1 + p.2 = n ∧ (p.1 < i ∨ p.2 < j)) → ‖∑ p ∈ s, coeff p.1 f * coeff p.2 g‖ * ρ ^ n < c * d`. Introduce `n s hs`. Use `norm_sum_mul_lt s (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g) (pow_pos hρ n).le hcd fun p hp => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hs p hp`. Rewrite using `[← h1]`.

Conclude with `term_lt p.1 p.2 h2`. Use `⟨hcd, ?_, fun n => ?_, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j)` using `Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl`. Rewrite using `[coeff_mul, ← Finset.add_sum_erase _ _ hmem]`. Establish `hmain : ‖coeff i f * coeff j g‖ * ρ ^ (i + j) = c * d`.

Rewrite using `[norm_mul_mul_pow_add_eq_mul_weighted, hi, hj]`. Establish `hrest` using `sum_lt (i + j) ((Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j)) (by`. Introduce and unpack `⟨a, b⟩ hp`. Simplify using `only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp`. Use `show a + b = i + j ∧ (a < i ∨ b < j)`.

Use the proof step `omega)`. Establish `hlt2 : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g‖ < ‖coeff i f * coeff j g‖` using `lt_of_mul_lt_mul_right (by rw [hmain]; exact hrest) (pow_pos hρ (i + j)).le`. Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt2.ne', max_eq_left hlt2.le, hmain]`. Rewrite using `[coeff_mul]`. Use `norm_sum_mul_le_of_forall_norm_mul_le _ (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g) (pow_pos hρ n) hcd.le fun p hp => ?_` and prove the remaining obligations.

Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hp, norm_mul_mul_pow_add_eq_mul_weighted]`. Conclude with `mul_le_mul (hle p.1) (hle' p.2) (hnn _ _) hc.le`. Rewrite using `[coeff_mul]`. Apply `sum_lt` to reduce the goal to its premises.

Introduce and unpack `⟨a, b⟩ hp`. Simplify using `only [Finset.HasAntidiagonal.mem_antidiagonal] at hp`. Use `show a + b = n ∧ (a < i ∨ b < j)`. Use linear arithmetic over natural numbers and integers.
-/
theorem DomTerm.mul {ρ : ℝ} (hρ : 0 < ρ) {f g : K⟦X⟧} {i j : ℕ} {c d : ℝ} (h : DomTerm ρ f i c)
    (h' : DomTerm ρ g j d) : DomTerm ρ (f * g) (i + j) (c * d) := by
  obtain ⟨hc, hi, hle, hlt⟩ := h
  obtain ⟨hd, hj, hle', hlt'⟩ := h'
  have hcd : 0 < c * d := mul_pos hc hd
  have hnn : ∀ (x : K) (n : ℕ), 0 ≤ ‖x‖ * ρ ^ n := fun x n => mul_nonneg (norm_nonneg x) (pow_pos hρ n).le
  have term_lt : ∀ a b, (a < i ∨ b < j) → ‖coeff a f * coeff b g‖ * ρ ^ (a + b) < c * d := by
    intro a b hab
    rw [norm_mul_mul_pow_add_eq_mul_weighted]
    rcases hab with ha | hb
    · calc ‖coeff a f‖ * ρ ^ a * (‖coeff b g‖ * ρ ^ b)
          ≤ ‖coeff a f‖ * ρ ^ a * d := mul_le_mul_of_nonneg_left (hle' b) (hnn _ a)
        _ < c * d := mul_lt_mul_of_pos_right (hlt a ha) hd
    · calc ‖coeff a f‖ * ρ ^ a * (‖coeff b g‖ * ρ ^ b)
          ≤ c * (‖coeff b g‖ * ρ ^ b) := mul_le_mul_of_nonneg_right (hle a) (hnn _ b)
        _ < c * d := mul_lt_mul_of_pos_left (hlt' b hb) hc
  have sum_lt : ∀ (n : ℕ) (s : Finset (ℕ × ℕ)), (∀ p ∈ s, p.1 + p.2 = n ∧ (p.1 < i ∨ p.2 < j)) →
      ‖∑ p ∈ s, coeff p.1 f * coeff p.2 g‖ * ρ ^ n < c * d := by
    intro n s hs
    refine norm_sum_mul_lt s (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g) (pow_pos hρ n).le hcd fun p hp => ?_
    obtain ⟨h1, h2⟩ := hs p hp
    rw [← h1]
    exact term_lt p.1 p.2 h2
  refine ⟨hcd, ?_, fun n => ?_, fun n hn => ?_⟩
  · have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hmain : ‖coeff i f * coeff j g‖ * ρ ^ (i + j) = c * d := by
      rw [norm_mul_mul_pow_add_eq_mul_weighted, hi, hj]
    have hrest := sum_lt (i + j) ((Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j)) (by
      rintro ⟨a, b⟩ hp
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
      show a + b = i + j ∧ (a < i ∨ b < j)
      omega)
    have hlt2 : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g‖ <
        ‖coeff i f * coeff j g‖ :=
      lt_of_mul_lt_mul_right (by rw [hmain]; exact hrest) (pow_pos hρ (i + j)).le
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt2.ne', max_eq_left hlt2.le, hmain]
  · rw [coeff_mul]
    refine norm_sum_mul_le_of_forall_norm_mul_le _ (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g) (pow_pos hρ n) hcd.le
      fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp, norm_mul_mul_pow_add_eq_mul_weighted]
    exact mul_le_mul (hle p.1) (hle' p.2) (hnn _ _) hc.le
  · rw [coeff_mul]
    apply sum_lt
    rintro ⟨a, b⟩ hp
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    show a + b = n ∧ (a < i ∨ b < j)
    omega

omit [IsUltrametricDist K] in
/- English proof (translation)
Use `⟨one_pos, ?_, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero n)⟩` and prove the remaining obligations. Rewrite using `[coeff_one, if_pos rfl, norm_one, pow_zero, mul_one]`. Rewrite using `[coeff_one] split_ifs with hn`. Rewrite using `[hn, norm_one, pow_zero, mul_one]`. Rewrite using `[norm_zero, zero_mul]`.

Conclude with `zero_le_one`.
-/
theorem domTerm_one (ρ : ℝ) : DomTerm ρ (1 : K⟦X⟧) 0 1 := by
  refine ⟨one_pos, ?_, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  · rw [coeff_one, if_pos rfl, norm_one, pow_zero, mul_one]
  · rw [coeff_one]
    split_ifs with hn
    · rw [hn, norm_one, pow_zero, mul_one]
    · rw [norm_zero, zero_mul]
      exact zero_le_one

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, mul_zero, pow_zero]`. Conclude with `domTerm_one ρ`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, pow_succ, mul_add_one]`. Conclude with `ih.mul hρ h`.
-/
theorem DomTerm.pow {ρ : ℝ} (hρ : 0 < ρ) {f : K⟦X⟧} {i : ℕ} {c : ℝ} (h : DomTerm ρ f i c) (n : ℕ) :
    DomTerm ρ (f ^ n) (i * n) (c ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, mul_zero, pow_zero]
    exact domTerm_one ρ
  | succ n ih =>
    rw [pow_succ, pow_succ, mul_add_one]
    exact ih.mul hρ h

omit [IsUltrametricDist K] in
/- English proof (translation)
Conclude with `⟨Nat.find h', hc, Nat.find_spec h', h, fun n hn => lt_of_le_of_ne (h n) (Nat.find_min h' hn)⟩`.
-/
theorem exists_domTerm_of_max {ρ : ℝ} {f : K⟦X⟧} {c : ℝ} (hc : 0 < c)
    (h : ∀ n, ‖coeff n f‖ * ρ ^ n ≤ c) (h' : ∃ n, ‖coeff n f‖ * ρ ^ n = c) :
    ∃ i, DomTerm ρ f i c := by
  classical
  exact ⟨Nat.find h', hc, Nat.find_spec h', h,
    fun n hn => lt_of_le_of_ne (h n) (Nat.find_min h' hn)⟩

omit [IsUltrametricDist K] in
/- English proof (translation)
Establish `hv : 0 < ‖coeff m f‖ * ρ ^ m` using `mul_pos (norm_pos_iff.mpr hm) (pow_pos hρ m)`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one hv hρ1`. Establish `htail : ∀ n, N ≤ n → ‖coeff n f‖ * ρ ^ n < ‖coeff m f‖ * ρ ^ m` using `fun n hn =>`. Combine the equalities or inequalities in the displayed calculation. Establish `hmN : m ∈ Finset.range N`.

Rewrite using `[Finset.mem_range]`. Assume the negation of the conclusion as `hmN`. Conclude with `lt_irrefl _ (htail m (not_lt.mp hmN))`. Take `⟨k, -, hk⟩` from `Finset.exists_max_image (Finset.range N) (fun n => ‖coeff n f‖ * ρ ^ n) ⟨m, hmN⟩`. Establish `hmk : ‖coeff m f‖ * ρ ^ m ≤ ‖coeff k f‖ * ρ ^ k` using `hk m hmN`.

Establish `hall : ∀ n, ‖coeff n f‖ * ρ ^ n ≤ ‖coeff k f‖ * ρ ^ k` using `fun n => by`. Distinguish the cases in `hn : n < N`. Conclude with `hk n (Finset.mem_range.mpr hn)`. Conclude with `(htail n (not_lt.mp hn)).le.trans hmk`. Take `⟨i, hi⟩` from `exists_domTerm_of_max (lt_of_lt_of_le hv hmk) hall ⟨k, rfl⟩`.

Conclude with `⟨i, _, hi⟩`.
-/
theorem exists_domTerm_of_lt_one {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {f : K⟦X⟧}
    (h : ∀ n, ‖coeff n f‖ ≤ 1) {m : ℕ} (hm : coeff m f ≠ 0) : ∃ i c, DomTerm ρ f i c := by
  classical
  have hv : 0 < ‖coeff m f‖ * ρ ^ m := mul_pos (norm_pos_iff.mpr hm) (pow_pos hρ m)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hv hρ1
  have htail : ∀ n, N ≤ n → ‖coeff n f‖ * ρ ^ n < ‖coeff m f‖ * ρ ^ m := fun n hn =>
    calc ‖coeff n f‖ * ρ ^ n ≤ ρ ^ n := mul_le_of_le_one_left (pow_pos hρ n).le (h n)
      _ ≤ ρ ^ N := pow_le_pow_of_le_one hρ.le hρ1.le hn
      _ < ‖coeff m f‖ * ρ ^ m := hN
  have hmN : m ∈ Finset.range N := by
    rw [Finset.mem_range]
    by_contra hmN
    exact lt_irrefl _ (htail m (not_lt.mp hmN))
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image (Finset.range N) (fun n => ‖coeff n f‖ * ρ ^ n) ⟨m, hmN⟩
  have hmk : ‖coeff m f‖ * ρ ^ m ≤ ‖coeff k f‖ * ρ ^ k := hk m hmN
  have hall : ∀ n, ‖coeff n f‖ * ρ ^ n ≤ ‖coeff k f‖ * ρ ^ k := fun n => by
    by_cases hn : n < N
    · exact hk n (Finset.mem_range.mpr hn)
    · exact (htail n (not_lt.mp hn)).le.trans hmk
  obtain ⟨i, hi⟩ := exists_domTerm_of_max (lt_of_lt_of_le hv hmk) hall ⟨k, rfl⟩
  exact ⟨i, _, hi⟩

omit [IsUltrametricDist K] in
/- English proof (translation)
Take `⟨n, hn⟩` from `h'`. Use `exists_domTerm_of_max one_pos (fun m => ?_) ⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[one_pow, mul_one]`. Conclude with `h m`. Rewrite using `[one_pow, mul_one, hn]`.
-/
theorem exists_domTerm_one {f : K⟦X⟧} (h : ∀ n, ‖coeff n f‖ ≤ 1) (h' : ∃ n, ‖coeff n f‖ = 1) :
    ∃ i, DomTerm 1 f i 1 := by
  obtain ⟨n, hn⟩ := h'
  refine exists_domTerm_of_max one_pos (fun m => ?_) ⟨n, ?_⟩
  · rw [one_pow, mul_one]
    exact h m
  · rw [one_pow, mul_one, hn]

/- English proof (translation)
Apply `exists_domTerm_one hf` to reduce the goal to its premises. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `hlt : ∀ n, ‖coeff n f‖ < 1` using `fun n => lt_of_le_of_ne (hf n) (hno n)`. Take `⟨-, hj, -, -⟩` from `h`.

Rewrite `hj` using `[one_pow, mul_one]`. Establish `hsm : ‖coeff j (f * g)‖ * 1 < 1`. Rewrite using `[coeff_mul]`. Use `norm_sum_mul_lt _ (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g) zero_le_one one_pos fun p _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hsm` using `[mul_one, hj]`. Conclude with `lt_irrefl 1 hsm`.
-/
theorem exists_domTerm_of_mul {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1)
    (hg : ∀ n, ‖coeff n g‖ ≤ 1) {j : ℕ} (h : DomTerm 1 (f * g) j 1) : ∃ i, DomTerm 1 f i 1 := by
  apply exists_domTerm_one hf
  by_contra hno
  push Not at hno
  have hlt : ∀ n, ‖coeff n f‖ < 1 := fun n => lt_of_le_of_ne (hf n) (hno n)
  obtain ⟨-, hj, -, -⟩ := h
  rw [one_pow, mul_one] at hj
  have hsm : ‖coeff j (f * g)‖ * 1 < 1 := by
    rw [coeff_mul]
    refine norm_sum_mul_lt _ (fun p : ℕ × ℕ => coeff p.1 f * coeff p.2 g) zero_le_one one_pos fun p _ => ?_
    rw [norm_mul, mul_one]
    calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖ ≤ ‖coeff p.1 f‖ * 1 :=
          mul_le_mul_of_nonneg_left (hg p.2) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt p.1
  rw [mul_one, hj] at hsm
  exact lt_irrefl 1 hsm

omit [IsUltrametricDist K] in
/- English proof (translation)
Unfold `E`. Rewrite using `[map_add, coeff_X_pow, ← map_natCast (C (R := K)) l, coeff_C]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`.
-/
theorem coeff_E (l e n : ℕ) (he : 0 < e) :
    coeff n (E K l e) = if n = e then 1 else if n = 0 then (l : K) else 0 := by
  unfold E
  rw [map_add, coeff_X_pow, ← map_natCast (C (R := K)) l, coeff_C]
  split_ifs <;> first | omega | simp

omit [IsUltrametricDist K] in
/- English proof (translation)
Use `⟨one_pos, ?_, fun n => ?_, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_E (K := K) l e e he, if_pos rfl, norm_one, one_pow, mul_one]`. Rewrite using `[coeff_E (K := K) l e n he, one_pow, mul_one] split_ifs`. Rewrite using `[norm_one]`. Conclude with `hl.le`.

Rewrite using `[norm_zero]`. Conclude with `zero_le_one`. Rewrite using `[coeff_E (K := K) l e n he, one_pow, mul_one, if_neg hn.ne] split_ifs`. Conclude with `hl`. Rewrite using `[norm_zero]`.

Conclude with `zero_lt_one`.
-/
theorem domTerm_E_one {l e : ℕ} (he : 0 < e) (hl : ‖(l : K)‖ < 1) : DomTerm 1 (E K l e) e 1 := by
  refine ⟨one_pos, ?_, fun n => ?_, fun n hn => ?_⟩
  · rw [coeff_E (K := K) l e e he, if_pos rfl, norm_one, one_pow, mul_one]
  · rw [coeff_E (K := K) l e n he, one_pow, mul_one]
    split_ifs
    · rw [norm_one]
    · exact hl.le
    · rw [norm_zero]
      exact zero_le_one
  · rw [coeff_E (K := K) l e n he, one_pow, mul_one, if_neg hn.ne]
    split_ifs
    · exact hl
    · rw [norm_zero]
      exact zero_lt_one

omit [IsUltrametricDist K] in
/- English proof (translation)
Use `⟨pow_pos hr e, ?_, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero n)⟩` and prove the remaining obligations. Rewrite using `[coeff_E (K := K) l e 0 he, if_neg he.ne, if_pos rfl, pow_zero, mul_one, hre]`. Rewrite using `[coeff_E (K := K) l e n he] split_ifs with h1 h2`. Rewrite using `[h1, norm_one, one_mul]`. Conclude with `le_of_eq (by rw [h2, pow_zero, mul_one, hre])`.

Rewrite using `[norm_zero, zero_mul]`. Conclude with `(pow_pos hr e).le`.
-/
theorem domTerm_E_root {l e : ℕ} (he : 0 < e) {r : ℝ} (hr : 0 < r) (hre : r ^ e = ‖(l : K)‖) :
    DomTerm r (E K l e) 0 (r ^ e) := by
  refine ⟨pow_pos hr e, ?_, fun n => ?_, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  · rw [coeff_E (K := K) l e 0 he, if_neg he.ne, if_pos rfl, pow_zero, mul_one, hre]
  · rw [coeff_E (K := K) l e n he]
    split_ifs with h1 h2
    · rw [h1, norm_one, one_mul]
    · exact le_of_eq (by rw [h2, pow_zero, mul_one, hre])
    · rw [norm_zero, zero_mul]
      exact (pow_pos hr e).le

omit [IsUltrametricDist K] in
/- English proof (translation)
Take `⟨-, hi, hle, hlt⟩` from `h`. Establish `hl0 : 0 < l` using `(Fact.out : l.Prime).pos`. Establish `hco : ∀ n, coeff n (GlobalTheory.BK.frob K l f) = if l ∣ n then coeff (n / l) f else 0` using `fun n => by`. Rewrite using `[GlobalTheory.BK.frob, coeff_expand]`. Use `⟨one_pos, ?_, fun n => ?_, fun n hn => ?_⟩` and prove the remaining obligations.

Rewrite using `[hco, if_pos (dvd_mul_right l i), Nat.mul_div_cancel_left i hl0, one_pow, mul_one]`. Rewrite `hi` using `[one_pow, mul_one]`. Conclude with `hi`. Rewrite using `[hco, one_pow, mul_one] split_ifs`. Establish `hx` using `hle (n / l)`.

Rewrite `hx` using `[one_pow, mul_one]`. Then use the resulting hypothesis. Rewrite using `[norm_zero]`. Conclude with `zero_le_one`. Rewrite using `[hco, one_pow, mul_one] split_ifs with hdv`. Take `⟨q, rfl⟩` from `hdv`.

Rewrite using `[Nat.mul_div_cancel_left q hl0]`. Establish `hq : q < i`. Assume the negation of the conclusion as `hq`. Use `push Not at hq`. Conclude with `absurd hn (not_lt.mpr (Nat.mul_le_mul le_rfl hq))`.

Establish `hx` using `hlt q hq`. Rewrite `hx` using `[one_pow, mul_one]`. Then use the resulting hypothesis. Rewrite using `[norm_zero]`. Conclude with `zero_lt_one`.
-/
theorem DomTerm.frob (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} {i : ℕ} (h : DomTerm 1 f i 1) :
    DomTerm 1 (frob K l f) (l * i) 1 := by
  obtain ⟨-, hi, hle, hlt⟩ := h
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  have hco : ∀ n, coeff n (GlobalTheory.BK.frob K l f) = if l ∣ n then coeff (n / l) f else 0 := fun n => by
    rw [GlobalTheory.BK.frob, coeff_expand]
  refine ⟨one_pos, ?_, fun n => ?_, fun n hn => ?_⟩
  · rw [hco, if_pos (dvd_mul_right l i), Nat.mul_div_cancel_left i hl0, one_pow, mul_one]
    rw [one_pow, mul_one] at hi
    exact hi
  · rw [hco, one_pow, mul_one]
    split_ifs
    · have hx := hle (n / l)
      rwa [one_pow, mul_one] at hx
    · rw [norm_zero]
      exact zero_le_one
  · rw [hco, one_pow, mul_one]
    split_ifs with hdv
    · obtain ⟨q, rfl⟩ := hdv
      rw [Nat.mul_div_cancel_left q hl0]
      have hq : q < i := by
        by_contra hq
        push Not at hq
        exact absurd hn (not_lt.mpr (Nat.mul_le_mul le_rfl hq))
      have hx := hlt q hq
      rwa [one_pow, mul_one] at hx
    · rw [norm_zero]
      exact zero_lt_one

/- English proof (translation)
Establish `hl1 : ‖(l : K)‖ < 1` using `hre ▸ pow_lt_one₀ hr.le hr1 he.ne'`. Establish `hE1 : DomTerm 1 (E K l e ^ n) (e * n) 1`. Establish `hx` using `(domTerm_E_one (K := K) he hl1).pow one_pos n`. Rewrite `hx` using `[one_pow]`. Then use the resulting hypothesis. Rewrite `hE1` using `[← h]`.

Take `⟨d', hd'⟩` from `exists_domTerm_of_mul (j := e * n) hk' hk (by rw [mul_comm k' k]; exact hE1)`. Establish `hdeg : d + d' = e * n` using `((hd.mul one_pos hd').unique hE1).1`. Establish `hkd : ‖coeff d k‖ = 1`. Establish `hx` using `hd.2.1`. Rewrite `hx` using `[one_pow, mul_one]`. Then use the resulting hypothesis.

Establish `hkd' : ‖coeff d' k'‖ = 1`. Establish `hx` using `hd'.2.1`. Rewrite `hx` using `[one_pow, mul_one]`. Then use the resulting hypothesis. Take `⟨i, c, hic⟩` from `exists_domTerm_of_lt_one hr hr1 hk (m := d) (fun h0 => by rw [h0, norm_zero] at hkd; exact zero_ne_one hkd)`. Take `⟨i', c', hic'⟩` from `exists_domTerm_of_lt_one hr hr1 hk' (m := d') (fun h0 => by rw [h0, norm_zero] at hkd'; exact zero_ne_one hkd')`.

Establish `hEr : DomTerm r (E K l e ^ n) (0 * n) ((r ^ e) ^ n)` using `(domTerm_E_root he hr hre).pow hr n`. Rewrite `hEr` using `[← h]`. Take `⟨hsum, hcc⟩` from `(hic.mul hr hic').unique hEr`. Establish `hi0 : i = 0` using `by omega`. Substitute `hi0` using the available equality.

Establish `hc : ‖constantCoeff k‖ = c`. Establish `hx` using `hic.2.1`. Rewrite `hx` using `[pow_zero, mul_one, coeff_zero_eq_constantCoeff_apply]`. Then use the resulting hypothesis. Rewrite using `[hc]`. Establish `hcd : r ^ d ≤ c`.

Establish `hx` using `hic.2.2.1 d`. Rewrite `hx` using `[hkd, one_mul]`. Then use the resulting hypothesis. Establish `hcd' : r ^ d' ≤ c'`. Establish `hx` using `hic'.2.2.1 d'`. Rewrite `hx` using `[hkd', one_mul]`. Then use the resulting hypothesis.

Establish `hprod : (r ^ e) ^ n = r ^ d * r ^ d'` using `by rw [← pow_mul, ← pow_add, hdeg]`. Assume the negation of the conclusion as `hne`. Establish `hlt : r ^ d < c` using `lt_of_le_of_ne hcd (Ne.symm hne)`. Establish `hx : r ^ d * r ^ d' < c * c'` using `mul_lt_mul hlt hcd' (pow_pos hr d') hic.1.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_constantCoeff_of_dvd {l e n d : ℕ} (he : 0 < e) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hre : r ^ e = ‖(l : K)‖) {k k' : K⟦X⟧} (hk : ∀ m, ‖coeff m k‖ ≤ 1)
    (hk' : ∀ m, ‖coeff m k'‖ ≤ 1) (h : k * k' = E K l e ^ n) (hd : DomTerm 1 k d 1) :
    ‖constantCoeff k‖ = r ^ d := by
  have hl1 : ‖(l : K)‖ < 1 := hre ▸ pow_lt_one₀ hr.le hr1 he.ne'
  have hE1 : DomTerm 1 (E K l e ^ n) (e * n) 1 := by
    have hx := (domTerm_E_one (K := K) he hl1).pow one_pos n
    rwa [one_pow] at hx
  rw [← h] at hE1
  obtain ⟨d', hd'⟩ := exists_domTerm_of_mul (j := e * n) hk' hk (by rw [mul_comm k' k]; exact hE1)
  have hdeg : d + d' = e * n := ((hd.mul one_pos hd').unique hE1).1
  have hkd : ‖coeff d k‖ = 1 := by
    have hx := hd.2.1
    rwa [one_pow, mul_one] at hx
  have hkd' : ‖coeff d' k'‖ = 1 := by
    have hx := hd'.2.1
    rwa [one_pow, mul_one] at hx
  obtain ⟨i, c, hic⟩ := exists_domTerm_of_lt_one hr hr1 hk (m := d)
    (fun h0 => by rw [h0, norm_zero] at hkd; exact zero_ne_one hkd)
  obtain ⟨i', c', hic'⟩ := exists_domTerm_of_lt_one hr hr1 hk' (m := d')
    (fun h0 => by rw [h0, norm_zero] at hkd'; exact zero_ne_one hkd')
  have hEr : DomTerm r (E K l e ^ n) (0 * n) ((r ^ e) ^ n) := (domTerm_E_root he hr hre).pow hr n
  rw [← h] at hEr
  obtain ⟨hsum, hcc⟩ := (hic.mul hr hic').unique hEr
  have hi0 : i = 0 := by omega
  subst hi0
  have hc : ‖constantCoeff k‖ = c := by
    have hx := hic.2.1
    rwa [pow_zero, mul_one, coeff_zero_eq_constantCoeff_apply] at hx
  rw [hc]
  have hcd : r ^ d ≤ c := by
    have hx := hic.2.2.1 d
    rwa [hkd, one_mul] at hx
  have hcd' : r ^ d' ≤ c' := by
    have hx := hic'.2.2.1 d'
    rwa [hkd', one_mul] at hx
  have hprod : (r ^ e) ^ n = r ^ d * r ^ d' := by rw [← pow_mul, ← pow_add, hdeg]
  by_contra hne
  have hlt : r ^ d < c := lt_of_le_of_ne hcd (Ne.symm hne)
  have hx : r ^ d * r ^ d' < c * c' := mul_lt_mul hlt hcd' (pow_pos hr d') hic.1.le
  linarith

omit [IsUltrametricDist K] in
/- English proof (translation)
Rewrite using `[frob, order_expand, h, nsmul_eq_mul, Nat.cast_mul]`.
-/
theorem order_frob (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} {n : ℕ} (h : f.order = n) :
    (frob K l f).order = (l * n : ℕ) := by
  rw [frob, order_expand, h, nsmul_eq_mul, Nat.cast_mul]

omit [IsUltrametricDist K] in
/- English proof (translation)
Rewrite using `[order_eq_nat]`. Use `⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩` and prove the remaining obligations. Rewrite using `[coeff_zero_eq_constantCoeff_apply]` and apply the resulting hypothesis.
-/
theorem order_eq_zero_of_ne {f : K⟦X⟧} (h : constantCoeff f ≠ 0) : f.order = (0 : ℕ) := by
  rw [order_eq_nat]
  refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rwa [coeff_zero_eq_constantCoeff_apply]

/- English proof (translation)
The claim follows from `Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)`.
-/
theorem sum_sub_one {a : ℕ} [NeZero a] (d : ZMod a → ℕ) : ∑ τ, d (τ - 1) = ∑ τ, d τ := Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)

/- English proof (translation)
Establish `hS : ∑ σ, d σ = 0`. Establish `h2 : 2 * ∑ σ, d σ ≤ l * ∑ σ, d σ` using `Nat.mul_le_mul hl le_rfl`. Rewrite `h2` using `[← h]`. Use linear arithmetic over natural numbers and integers. Conclude with `Finset.sum_eq_zero_iff.mp hS τ (Finset.mem_univ τ)`.
-/
theorem eq_zero_of_sum_eq_mul {a l : ℕ} [NeZero a] (hl : 1 < l) (d : ZMod a → ℕ)
    (h : ∑ τ, d τ = l * ∑ τ, d τ) (τ : ZMod a) : d τ = 0 := by
  have hS : ∑ σ, d σ = 0 := by
    have h2 : 2 * ∑ σ, d σ ≤ l * ∑ σ, d σ := Nat.mul_le_mul hl le_rfl
    rw [← h] at h2
    omega
  exact Finset.sum_eq_zero_iff.mp hS τ (Finset.mem_univ τ)

/- English proof (translation)
Establish `hlpos : 0 < ‖(l : K)‖` using `norm_pos_iff.mpr hl0`. Take `⟨r, hr, hr1, hre⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ^ e = ‖(l : K)‖` from `⟨‖(l : K)‖ ^ ((e : ℝ)⁻¹), Real.rpow_pos_of_pos hlpos _, Real.rpow_lt_one (norm_nonneg _) hl (inv_pos.mpr (Nat.cast_pos.mpr he)), Real.rpow_inv_natCast_pow (norm_nonneg _) he.ne'⟩`. Establish `hEpow : ∀ n, DomTerm 1 (E K l e ^ n) (e * n) 1` using `fun n => by`. Establish `hx` using `(domTerm_E_one (K := K) he hl).pow one_pos n`. Rewrite `hx` using `[one_pow]`. Then use the resulting hypothesis.

Use `choose δ hδ using fun σ => exists_domTerm_one (hΔ σ) (hΔ1 σ)`. Use `choose κ hκ using fun σ => exists_domTerm_of_mul (j := e * N) (hk σ) (hk' σ) (by rw [hkk σ]; exact hEpow N)`. Establish `hdeg : ∀ σ, δ σ + κ σ = e * M + l * δ (σ - 1)` using `fun σ => by`. Establish `h1` using `(hδ σ).mul one_pos (hκ σ)`. Establish `h2` using `(hEpow M).mul one_pos ((hδ (σ - 1)).frob l)`.

Rewrite `h1` using `[hcyc σ]`. Conclude with `(h1.unique h2).1`. Establish `hE0 : constantCoeff (E K l e) = (l : K)`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_E l e 0 he, if_neg he.ne, if_pos rfl]`. Establish `hEord : ∀ n, (E K l e ^ n).order = (0 : ℕ)` using `fun n => by`.

Apply `order_eq_zero_of_ne` to reduce the goal to its premises. Rewrite using `[map_pow, hE0]`. Conclude with `pow_ne_zero _ hl0`. Establish `hkord : ∀ σ, (k σ).order = (0 : ℕ)` using `fun σ => by`. Establish `h` using `order_mul (k σ) (k' σ)`.

Rewrite `h` using `[hkk σ, hEord N, Nat.cast_zero]`. Rewrite using `[Nat.cast_zero]`. Conclude with `(add_eq_zero.mp h.symm).1`. Establish `hΔne : ∀ σ, Δ σ ≠ 0` using `fun σ h0 => by`. Take `⟨n, hn⟩` from `hΔ1 σ`.

Rewrite `hn` using `[h0, map_zero, norm_zero]`. Conclude with `zero_ne_one hn`. Use `choose o ho using fun σ => ENat.ne_top_iff_exists.mp (mt order_eq_top.mp (hΔne σ))`. Establish `hord : ∀ σ, o σ = l * o (σ - 1)` using `fun σ => by`. Establish `h` using `congrArg order (hcyc σ)`.

Rewrite `h` using `[order_mul, order_mul, hkord σ, hEord M, ← ho σ, order_frob l (ho (σ - 1)).symm]`. Simplify using `only [Nat.cast_zero, add_zero, zero_add, Nat.cast_inj] at h`. Conclude with `h`. Establish `hsum_o : ∑ σ, o σ = l * ∑ σ, o σ`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc0 : ∀ σ, constantCoeff (Δ σ) ≠ 0` using `fun σ => by`. Establish `hx` using `ho σ`. Rewrite `hx` using `[eq_zero_of_sum_eq_mul (Fact.out : l.Prime).one_lt o hsum_o σ]`. Establish `h2` using `(order_eq_nat.mp hx.symm).1`. Rewrite `h2` using `[coeff_zero_eq_constantCoeff_apply]`. Then use the resulting hypothesis.

Establish `hF0 : ∀ F : K⟦X⟧, constantCoeff (frob K l F) = constantCoeff F` using `fun F => by`. Rewrite using `[frob, constantCoeff_expand]`. Establish `hkn : ∀ σ, ‖constantCoeff (k σ)‖ = r ^ κ σ` using `fun σ => norm_constantCoeff_of_dvd he hr hr1 hre (hk σ) (hk' σ) (hkk σ) (hκ σ)`. Establish `hcc : ∀ σ, ‖constantCoeff (Δ σ)‖ * r ^ κ σ = (r ^ e) ^ M * ‖constantCoeff (Δ (σ - 1))‖` using `fun σ => by`. Establish `h` using `congrArg (fun F => ‖constantCoeff F‖) (hcyc σ)`.

Simplify using `only [map_mul, map_pow, norm_mul, norm_pow, hE0, hF0] at h`. Rewrite using `[← hkn σ, hre]`. Conclude with `h`. Establish `hP : 0 < ∏ σ, ‖constantCoeff (Δ σ)‖` using `Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hc0 σ)`. Establish `hprod : (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (∑ σ, κ σ) = (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (e * M * a)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Use `_ = ∏ σ, ((r ^ e) ^ M * ‖constantCoeff (Δ (σ - 1))‖) := Finset.prod_congr rfl fun σ _ => hcc σ`. Use `_ = ((r ^ e) ^ M) ^ a * ∏ σ, ‖constantCoeff (Δ (σ - 1))‖ := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]`.

Use `_ = ((r ^ e) ^ M) ^ a * ∏ σ, ‖constantCoeff (Δ σ)‖ := by`. Rewrite using `[Fintype.prod_equiv (Equiv.subRight (1 : ZMod a)) (fun σ => ‖constantCoeff (Δ (σ - 1))‖) (fun σ => ‖constantCoeff (Δ σ)‖) (fun _ => rfl)]`. Use `_ = (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (e * M * a) := by ring`. Establish `hsumκ : ∑ σ, κ σ = e * M * a` using `pow_right_injective₀ hr hr1.ne (mul_left_cancel₀ hP.ne' hprod)`. Establish `hsumδ : ∑ σ, δ σ = l * ∑ σ, δ σ`.

Establish `h : ∑ σ, (δ σ + κ σ) = ∑ σ, (e * M + l * δ (σ - 1))` using `Finset.sum_congr rfl fun σ _ => hdeg σ`. Rewrite `h` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, ← Finset.mul_sum, sum_sub_one δ, hsumκ, mul_comm (e * M) a, add_comm (a * (e * M))]`. Conclude with `Nat.add_right_cancel h`. Establish `hδ0` using `eq_zero_of_sum_eq_mul (Fact.out : l.Prime).one_lt δ hsumδ τ`. Establish `hx` using `(hδ τ).2.1`.

Rewrite `hx` using `[hδ0, pow_zero, mul_one, coeff_zero_eq_constantCoeff_apply]`. Then use the resulting hypothesis.
-/
theorem norm_constantCoeff_eq_one_of_cycle (K : Type) [NormedField K] [IsUltrametricDist K]
    (l e a M N : ℕ) [Fact l.Prime] [NeZero a] (he : 0 < e) (hl0 : (l : K) ≠ 0)
    (hl : ‖(l : K)‖ < 1) (Δ k k' : ZMod a → K⟦X⟧) (hΔ : ∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1)
    (hΔ1 : ∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) (hk : ∀ τ n, ‖coeff n (k τ)‖ ≤ 1)
    (hk' : ∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) (hkk : ∀ τ, k τ * k' τ = E K l e ^ N)
    (hcyc : ∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) (τ : ZMod a) :
    ‖constantCoeff (Δ τ)‖ = 1 := by
  classical
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  obtain ⟨r, hr, hr1, hre⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ^ e = ‖(l : K)‖ :=
    ⟨‖(l : K)‖ ^ ((e : ℝ)⁻¹), Real.rpow_pos_of_pos hlpos _,
      Real.rpow_lt_one (norm_nonneg _) hl (inv_pos.mpr (Nat.cast_pos.mpr he)),
      Real.rpow_inv_natCast_pow (norm_nonneg _) he.ne'⟩

  have hEpow : ∀ n, DomTerm 1 (E K l e ^ n) (e * n) 1 := fun n => by
    have hx := (domTerm_E_one (K := K) he hl).pow one_pos n
    rwa [one_pow] at hx
  choose δ hδ using fun σ => exists_domTerm_one (hΔ σ) (hΔ1 σ)
  choose κ hκ using fun σ =>
    exists_domTerm_of_mul (j := e * N) (hk σ) (hk' σ) (by rw [hkk σ]; exact hEpow N)
  have hdeg : ∀ σ, δ σ + κ σ = e * M + l * δ (σ - 1) := fun σ => by
    have h1 := (hδ σ).mul one_pos (hκ σ)
    have h2 := (hEpow M).mul one_pos ((hδ (σ - 1)).frob l)
    rw [hcyc σ] at h1
    exact (h1.unique h2).1

  have hE0 : constantCoeff (E K l e) = (l : K) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_E l e 0 he, if_neg he.ne, if_pos rfl]
  have hEord : ∀ n, (E K l e ^ n).order = (0 : ℕ) := fun n => by
    apply order_eq_zero_of_ne
    rw [map_pow, hE0]
    exact pow_ne_zero _ hl0
  have hkord : ∀ σ, (k σ).order = (0 : ℕ) := fun σ => by
    have h := order_mul (k σ) (k' σ)
    rw [hkk σ, hEord N, Nat.cast_zero] at h
    rw [Nat.cast_zero]
    exact (add_eq_zero.mp h.symm).1
  have hΔne : ∀ σ, Δ σ ≠ 0 := fun σ h0 => by
    obtain ⟨n, hn⟩ := hΔ1 σ
    rw [h0, map_zero, norm_zero] at hn
    exact zero_ne_one hn
  choose o ho using fun σ => ENat.ne_top_iff_exists.mp (mt order_eq_top.mp (hΔne σ))
  have hord : ∀ σ, o σ = l * o (σ - 1) := fun σ => by
    have h := congrArg order (hcyc σ)
    rw [order_mul, order_mul, hkord σ, hEord M, ← ho σ, order_frob l (ho (σ - 1)).symm] at h
    simp only [Nat.cast_zero, add_zero, zero_add, Nat.cast_inj] at h
    exact h
  have hsum_o : ∑ σ, o σ = l * ∑ σ, o σ :=
    calc ∑ σ, o σ = ∑ σ, l * o (σ - 1) := Finset.sum_congr rfl fun σ _ => hord σ
      _ = ∑ σ, l * o σ := sum_sub_one (fun σ => l * o σ)
      _ = l * ∑ σ, o σ := (Finset.mul_sum _ _ _).symm
  have hc0 : ∀ σ, constantCoeff (Δ σ) ≠ 0 := fun σ => by
    have hx := ho σ
    rw [eq_zero_of_sum_eq_mul (Fact.out : l.Prime).one_lt o hsum_o σ] at hx
    have h2 := (order_eq_nat.mp hx.symm).1
    rwa [coeff_zero_eq_constantCoeff_apply] at h2

  have hF0 : ∀ F : K⟦X⟧, constantCoeff (frob K l F) = constantCoeff F := fun F => by
    rw [frob, constantCoeff_expand]
  have hkn : ∀ σ, ‖constantCoeff (k σ)‖ = r ^ κ σ := fun σ =>
    norm_constantCoeff_of_dvd he hr hr1 hre (hk σ) (hk' σ) (hkk σ) (hκ σ)
  have hcc : ∀ σ, ‖constantCoeff (Δ σ)‖ * r ^ κ σ =
      (r ^ e) ^ M * ‖constantCoeff (Δ (σ - 1))‖ := fun σ => by
    have h := congrArg (fun F => ‖constantCoeff F‖) (hcyc σ)
    simp only [map_mul, map_pow, norm_mul, norm_pow, hE0, hF0] at h
    rw [← hkn σ, hre]
    exact h
  have hP : 0 < ∏ σ, ‖constantCoeff (Δ σ)‖ :=
    Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hc0 σ)
  have hprod : (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (∑ σ, κ σ) =
      (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (e * M * a) :=
    calc (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (∑ σ, κ σ)
        = ∏ σ, (‖constantCoeff (Δ σ)‖ * r ^ κ σ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      _ = ∏ σ, ((r ^ e) ^ M * ‖constantCoeff (Δ (σ - 1))‖) :=
          Finset.prod_congr rfl fun σ _ => hcc σ
      _ = ((r ^ e) ^ M) ^ a * ∏ σ, ‖constantCoeff (Δ (σ - 1))‖ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
      _ = ((r ^ e) ^ M) ^ a * ∏ σ, ‖constantCoeff (Δ σ)‖ := by
          rw [Fintype.prod_equiv (Equiv.subRight (1 : ZMod a))
            (fun σ => ‖constantCoeff (Δ (σ - 1))‖) (fun σ => ‖constantCoeff (Δ σ)‖) (fun _ => rfl)]
      _ = (∏ σ, ‖constantCoeff (Δ σ)‖) * r ^ (e * M * a) := by ring
  have hsumκ : ∑ σ, κ σ = e * M * a :=
    pow_right_injective₀ hr hr1.ne (mul_left_cancel₀ hP.ne' hprod)

  have hsumδ : ∑ σ, δ σ = l * ∑ σ, δ σ := by
    have h : ∑ σ, (δ σ + κ σ) = ∑ σ, (e * M + l * δ (σ - 1)) :=
      Finset.sum_congr rfl fun σ _ => hdeg σ
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      ZMod.card, smul_eq_mul, ← Finset.mul_sum, sum_sub_one δ, hsumκ, mul_comm (e * M) a,
      add_comm (a * (e * M))] at h
    exact Nat.add_right_cancel h
  have hδ0 := eq_zero_of_sum_eq_mul (Fact.out : l.Prime).one_lt δ hsumδ τ
  have hx := (hδ τ).2.1
  rwa [hδ0, pow_zero, mul_one, coeff_zero_eq_constantCoeff_apply] at hx

end GlobalTheory.BK.Cycle
