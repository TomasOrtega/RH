import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.CmAlternatingForm

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace Cm2

open Cm1

/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, hpq⟩`. Express the relevant statement in the definitionally equal form `(p : ℂ) * (a : ℂ) + (q : ℂ) * cmTheta b d = _ at hpq`. Establish `hli` using `(cmPair a b d ha hd).indep`.

Rewrite `hli` using `[LinearIndependent.pair_iff]`. Take `⟨h1, h2⟩` from `hli (2 * (p : ℝ) - m) (2 * (q : ℝ) - n) (by`. Express the relevant statement in the definitionally equal form `((2 * (p : ℝ) - m : ℝ)) • (a : ℂ) + ((2 * (q : ℝ) - n : ℝ)) • cmTheta b d = 0`. Simplify using `only [Complex.real_smul]`. Use `push_cast`.

Take the linear combination `2 * hpq)`. Establish `hm : m = 2 * p`. Establish `: (m : ℝ) = 2 * p` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hn : n = 2 * q`.

Establish `: (n : ℝ) = 2 * q` using `by linarith`. Conclude with `this` after adjusting the coercions. Conclude with `⟨⟨p, by omega⟩, ⟨q, by omega⟩⟩`. Introduce and unpack `⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩`. Use `⟨r, s, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(r : ℂ) * (a : ℂ) + (s : ℂ) * cmTheta b d = _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma half_mem_iff (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (m n : ℤ) :
    ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) / 2 ∈ (cmPair a b d ha hd).lattice ↔ Even m ∧ Even n := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨p, q, hpq⟩
    change (p : ℂ) * (a : ℂ) + (q : ℂ) * cmTheta b d = _ at hpq
    have hli := (cmPair a b d ha hd).indep
    rw [LinearIndependent.pair_iff] at hli
    obtain ⟨h1, h2⟩ := hli (2 * (p : ℝ) - m) (2 * (q : ℝ) - n) (by
      change ((2 * (p : ℝ) - m : ℝ)) • (a : ℂ) + ((2 * (q : ℝ) - n : ℝ)) • cmTheta b d = 0
      simp only [Complex.real_smul]
      push_cast
      linear_combination 2 * hpq)
    have hm : m = 2 * p := by
      have : (m : ℝ) = 2 * p := by linarith
      exact_mod_cast this
    have hn : n = 2 * q := by
      have : (n : ℝ) = 2 * q := by linarith
      exact_mod_cast this
    exact ⟨⟨p, by omega⟩, ⟨q, by omega⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    refine ⟨r, s, ?_⟩
    change (r : ℂ) * (a : ℂ) + (s : ℂ) * cmTheta b d = _
    push_cast
    ring

/- English proof (translation)
Break down `Int.even_or_odd' b with ⟨k, hk | hk⟩` into its components or cases. It suffices to derive a contradiction. Establish `h' : 4 * ((a : ℤ) * c) = 4 * (k * k) + d`. Rewrite `h` using `[hk]`. Take the linear combination `h`.

Use linear arithmetic over natural numbers and integers. Establish `hkk : Even (k * (k + 1))` using `by first`. Consider the case `exact Int.even_mul_succ_self k`. Consider the case `(rcases Int.even_or_odd k with hk' | hk'`. Conclude with `hk'.mul_right _`.

Conclude with `hk'.add_one.mul_left _)`. Take `⟨j, hj⟩` from `hkk`. Establish `h' : 4 * ((a : ℤ) * c) = 4 * (k * (k + 1)) + 1 + d`. Rewrite `h` using `[hk]`. Take the linear combination `h`.

Establish `hac : Even ((a : ℤ) * c)` using `⟨(a : ℤ) * c / 2, by omega⟩`. Use `⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Break down `Int.even_mul.mp hac with h1 | h1` into its components or cases. It suffices to derive a contradiction. Take `⟨t, ht⟩` from `hodd`.

Take `⟨s, hs⟩` from `h1`. Use linear arithmetic over natural numbers and integers. Conclude with `h1`.
-/
lemma even_im_hermitian_sub (a : ℕ) (b c : ℤ) (d : ℕ) (h : 4 * (a : ℤ) * c = b ^ 2 + d) (hodd : Odd a) (hd8 : d % 8 = 7) :
    Odd b ∧ Even c := by
  rcases Int.even_or_odd' b with ⟨k, hk | hk⟩
  · exfalso
    have h' : 4 * ((a : ℤ) * c) = 4 * (k * k) + d := by
      rw [hk] at h
      linear_combination h
    omega
  · have hkk : Even (k * (k + 1)) := by
      first
        | exact Int.even_mul_succ_self k
        | (rcases Int.even_or_odd k with hk' | hk'
           · exact hk'.mul_right _
           · exact hk'.add_one.mul_left _)
    obtain ⟨j, hj⟩ := hkk
    have h' : 4 * ((a : ℤ) * c) = 4 * (k * (k + 1)) + 1 + d := by
      rw [hk] at h
      linear_combination h
    have hac : Even ((a : ℤ) * c) := ⟨(a : ℤ) * c / 2, by omega⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rcases Int.even_mul.mp hac with h1 | h1
    · exfalso
      obtain ⟨t, ht⟩ := hodd
      obtain ⟨s, hs⟩ := h1
      omega
    · exact h1

/- English proof (translation)
Establish `ha' : ¬ Even a` using `Int.not_even_iff_odd.mpr ha`. Establish `hb' : ¬ Even b` using `Int.not_even_iff_odd.mpr hb`. Rewrite using `[← Int.not_even_iff_odd]`. Use `first`. Consider the case `simp only [cmForm, Int.even_add, Int.even_mul, Int.even_pow' two_ne_zero]`.

Consider the case `simp only [cmForm, Int.even_add, Int.even_mul, Int.even_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]`. The claim follows by propositional logic.
-/
lemma form_even_iff (a b c m n : ℤ) (ha : Odd a) (hb : Odd b) (hc : Even c) :
    Even (cmForm a b c m n) ↔ (Even m ∨ Odd n) := by
  have ha' : ¬ Even a := Int.not_even_iff_odd.mpr ha
  have hb' : ¬ Even b := Int.not_even_iff_odd.mpr hb
  rw [← Int.not_even_iff_odd]
  first
    | simp only [cmForm, Int.even_add, Int.even_mul, Int.even_pow' two_ne_zero]
    | simp only [cmForm, Int.even_add, Int.even_mul, Int.even_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, and_true]
  tauto

/- English proof (translation)
Establish `e : (Real.pi : ℂ) * Complex.I * (((n : ℤ) : ℝ) : ℂ) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.exp_int_mul, Complex.exp_pi_mul_I]`. Use `split_ifs with h`.

Conclude with `h.neg_one_zpow`. Conclude with `(Int.not_even_iff_odd.mp h).neg_one_zpow`.
-/
lemma exp_pi_int (n : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (((n : ℤ) : ℝ) : ℂ)) = if Even n then 1 else -1 := by
  have e : (Real.pi : ℂ) * Complex.I * (((n : ℤ) : ℝ) : ℂ) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.mp h).neg_one_zpow

end Cm2

open Cm1 Cm2

/- English proof (translation)
Introduce `a b c d ha hd hac hodd hd8 m n z`. Establish `hmem : ∀ p q : ℤ, (p : ℂ) * (a : ℂ) + (q : ℂ) * cmTheta b d ∈ (cmPair a b d ha hd).lattice`. Introduce `p q`. Use `(half_mem_iff a b d ha hd (2 * p) (2 * q)).2 ⟨even_two_mul p, even_two_mul q⟩` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ha0 : (a : ℂ) ∈ (cmPair a b d ha hd).lattice` using `by simpa using hmem 1 0`. Establish `ha2 : (a : ℂ) / 2 ∉ (cmPair a b d ha hd).lattice`. Introduce `hh`.

Establish `h10` using `(half_mem_iff a b d ha hd 1 0).1 (by simpa using hh)`. Take `⟨r, hr⟩` from `h10.1`. Use linear arithmetic over natural numbers and integers. Establish `key` using `(h (cmPair a b d ha hd) (a : ℂ) ha0 ha2).2.2.2.2 _ (hmem m n) z`. Rewrite using `[key]`.

Use `congr 2`. Establish `hsc : semiChar (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) = if Even m ∧ Even n then 1 else -1`. Unfold `semiChar`. Simplify using `only [half_mem_iff a b d ha hd m n]`. Establish `hA : altE (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) (a : ℂ) = (n : ℝ)`.

Establish `h1` using `hE a b d ha hd m n 1 0`. Establish `e : ((1 : ℤ) : ℂ) * (a : ℂ) + ((0 : ℤ) : ℂ) * cmTheta b d = (a : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e]`.

Rewrite using `[h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hbo, hce⟩` from `even_im_hermitian_sub a b c d hac hodd hd8`. Establish `hao : Odd (a : ℤ)`.

Take `⟨t, ht⟩` from `hodd`. Conclude with `⟨t, by rw [ht]; push_cast; ring⟩`. Establish `hpar` using `form_even_iff a b c m n hao hbo hce`. Establish `hpow : ((-1 : ℂ)) ^ (cmForm a b c m n).natAbs = if Even (cmForm a b c m n) then 1 else -1` using `by split_ifs with hk`. Conclude with `(Int.natAbs_even.mpr hk).neg_one_pow`.

Conclude with `(Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hk)).neg_one_pow`. Rewrite using `[hsc, hA, exp_pi_int, hpow]`. Simplify using `only [hpar]`. Apply the tactic sequence `by_cases hm : Even m <;> by_cases hn : Even n <;> simp [hm, hn, ← Int.not_even_iff_odd]`.
-/
theorem cmTheta0_of (h : ThetaZeroBasic) (hE : CmAltE) : CmTheta0 := by
  intro a b c d ha hd hac hodd hd8 m n z
  have hmem : ∀ p q : ℤ, (p : ℂ) * (a : ℂ) + (q : ℂ) * cmTheta b d ∈ (cmPair a b d ha hd).lattice := by
    intro p q
    have := (half_mem_iff a b d ha hd (2 * p) (2 * q)).2 ⟨even_two_mul p, even_two_mul q⟩
    convert this using 1
    push_cast
    ring
  have ha0 : (a : ℂ) ∈ (cmPair a b d ha hd).lattice := by simpa using hmem 1 0
  have ha2 : (a : ℂ) / 2 ∉ (cmPair a b d ha hd).lattice := by
    intro hh
    have h10 := (half_mem_iff a b d ha hd 1 0).1 (by simpa using hh)
    obtain ⟨r, hr⟩ := h10.1
    omega
  have key := (h (cmPair a b d ha hd) (a : ℂ) ha0 ha2).2.2.2.2 _ (hmem m n) z
  rw [key]
  congr 2
  have hsc : semiChar (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = if Even m ∧ Even n then 1 else -1 := by
    unfold semiChar
    simp only [half_mem_iff a b d ha hd m n]
  have hA : altE (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) (a : ℂ) = (n : ℝ) := by
    have h1 := hE a b d ha hd m n 1 0
    have e : ((1 : ℤ) : ℂ) * (a : ℂ) + ((0 : ℤ) : ℂ) * cmTheta b d = (a : ℂ) := by
      push_cast
      ring
    rw [e] at h1
    rw [h1]
    push_cast
    ring
  obtain ⟨hbo, hce⟩ := even_im_hermitian_sub a b c d hac hodd hd8
  have hao : Odd (a : ℤ) := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t, by rw [ht]; push_cast; ring⟩
  have hpar := form_even_iff a b c m n hao hbo hce
  have hpow : ((-1 : ℂ)) ^ (cmForm a b c m n).natAbs = if Even (cmForm a b c m n) then 1 else -1 := by
    split_ifs with hk
    · exact (Int.natAbs_even.mpr hk).neg_one_pow
    · exact (Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hk)).neg_one_pow
  rw [hsc, hA, exp_pi_int, hpow]
  simp only [hpar]
  by_cases hm : Even m <;> by_cases hn : Even n <;> simp [hm, hn, ← Int.not_even_iff_odd]

/- English proof (translation)
The claim follows from `cmTheta0_of th0Basic cm_alternating_form`.
-/
theorem cm_even_theta : CmTheta0 := cmTheta0_of th0Basic cm_alternating_form

end Formalism.L2.Th1.F
