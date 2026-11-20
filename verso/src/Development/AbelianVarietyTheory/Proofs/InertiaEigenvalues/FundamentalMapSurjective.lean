import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitOfPowDvdSub

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FundOnto

section Abstract

variable {R O : Type} [CommRing R] [CommRing O] (p : ℕ)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub`. Consider the case `exact _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub`. Consider the case `(apply _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub ..)`.
-/
theorem exists_lim [IsAdicComplete (Ideal.span {(p : R)}) R] (f : ℕ → R)
    (h : ∀ n, (p : R) ^ n ∣ f (n + 1) - f n) : ∃ L, ∀ n, (p : R) ^ n ∣ L - f n := by
  first
  | exact @_root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub
  | exact _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub
  | (apply _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LimitOfDivisibility.exists_limit_of_pow_dvd_sub ..)

/- English proof (translation)
Use `IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : R)}) (M := R)) x fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `h n`.
-/
theorem eq_zero_of_dvd [IsAdicComplete (Ideal.span {(p : R)}) R] (x : R)
    (h : ∀ n, (p : R) ^ n ∣ x) : x = 0 := by
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : R)}) (M := R)) x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h n

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`.

Apply `tf` to reduce the goal to its premises. Rewrite `h` using `[pow_succ']`. Take the linear combination `h`.
-/
theorem pow_cancel (tf : ∀ x : R, (p : R) * x = 0 → x = 0) (n : ℕ) (x y : R)
    (h : (p : R) ^ n * x = (p : R) ^ n * y) : x = y := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    rw [← sub_eq_zero]
    apply tf
    rw [pow_succ'] at h
    linear_combination h

/- English proof (translation)
Take `⟨k, hk⟩` from `Polynomial.powAddExpansion (1 : R) ((p : R) ^ (m + 2) * w) p`. Conclude with `⟨k * w ^ 2, by rw [hk]; simp only [one_pow]; ring⟩`.
-/
theorem step (m : ℕ) (w : R) : ∃ s : R,
    (1 + (p : R) ^ (m + 2) * w) ^ p = 1 + (p : R) ^ (m + 3) * (w + (p : R) ^ (m + 1) * s) := by
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion (1 : R) ((p : R) ^ (m + 2) * w) p
  exact ⟨k * w ^ 2, by rw [hk]; simp only [one_pow]; ring⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨w, by simp, by simp⟩`. Consider the case `succ n ih`. Take `⟨W, h1, h2⟩` from `ih`. Take `⟨s, hs⟩` from `step p n W`.

Use `⟨_, by rw [pow_succ p n, pow_mul, h1, hs], ?_⟩` and prove the remaining obligations. Rewrite using `[add_sub_right_comm]`. Conclude with `dvd_add h2 ((dvd_pow_self _ (Nat.succ_ne_zero n)).mul_right _)`.
-/
theorem iter (w : R) (n : ℕ) : ∃ W : R,
    (1 + (p : R) ^ 2 * w) ^ p ^ n = 1 + (p : R) ^ (n + 2) * W ∧ (p : R) ∣ W - w := by
  induction n with
  | zero => exact ⟨w, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨W, h1, h2⟩ := ih
    obtain ⟨s, hs⟩ := step p n W
    refine ⟨_, by rw [pow_succ p n, pow_mul, h1, hs], ?_⟩
    rw [add_sub_right_comm]
    exact dvd_add h2 ((dvd_pow_self _ (Nat.succ_ne_zero n)).mul_right _)

/- English proof (translation)
Use `choose W hW _ using iter p w`. Establish `h1 : ∀ n, (p : R) ^ n ∣ W (n + 1) - W n`. Introduce `n`. Take `⟨s, hs⟩` from `step p n (W n)`. Rewrite `hs` using `[← hW, ← pow_mul, ← pow_succ, hW, add_right_inj]`.

Rewrite using `[pow_cancel p tf _ _ _ hs]`. Conclude with `⟨p * s, by ring⟩`. Establish `h2 : ∀ n, φ (W n) = p * W (n + 1)`. Introduce `n`. Apply `pow_cancel p tf (n + 2)` to reduce the goal to its premises.

Establish `h` using `congrArg φ (hW n)`. Rewrite `h` using `[map_pow, hu, ← pow_mul, ← pow_succ', hW, map_add, map_one, map_mul, map_pow, map_natCast]`. Take the linear combination `-h`. Take `⟨y, hy⟩` from `exists_lim p W h1`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_dvd p _ fun n => ?_` and prove the remaining obligations. Establish `a` using `map_dvd φ (hy n)`. Rewrite `a` using `[map_pow, map_natCast, map_sub, h2]`. Establish `b` using `((pow_dvd_pow _ (Nat.le_succ n)).trans (hy (n + 1))).mul_left (p : R)`.

Use `dvd_sub a b` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨V, hV, e, he⟩` from `iter p c 5`. Establish `h` using `congrArg Θ (hW 3)`.

Rewrite `h` using `[map_pow, hc, ← pow_mul, ← pow_add, hV, map_add, map_one, map_mul, map_pow, map_natCast]`. Establish `h3 : Θ (W 3) = (p : O) ^ 2 * V` using `pow_cancel p tfO 5 _ _ (by linear_combination -h)`. Establish `a` using `map_dvd Θ (hy 3)`. Rewrite `a` using `[map_pow, map_natCast, map_sub, h3]`. Establish `b : (p : O) ^ 3 ∣ (p : O) ^ 2 * V - (p : O) ^ 2 * c` using `⟨e, by rw [← mul_sub, he]; ring⟩`.

Use `dvd_add a b` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem exists_log [IsAdicComplete (Ideal.span {(p : R)}) R] (tf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (tfO : ∀ x : O, (p : O) * x = 0 → x = 0) (φ : R →+* R) (Θ : R →+* O) (w : R)
    (hu : φ (1 + (p : R) ^ 2 * w) = (1 + (p : R) ^ 2 * w) ^ p) (c : O)
    (hc : Θ (1 + (p : R) ^ 2 * w) = (1 + (p : O) ^ 2 * c) ^ p ^ 2) :
    ∃ y : R, φ y = p * y ∧ (p : O) ^ 3 ∣ Θ y - (p : O) ^ 2 * c := by
  choose W hW _ using iter p w
  have h1 : ∀ n, (p : R) ^ n ∣ W (n + 1) - W n := by
    intro n
    obtain ⟨s, hs⟩ := step p n (W n)
    rw [← hW, ← pow_mul, ← pow_succ, hW, add_right_inj] at hs
    rw [pow_cancel p tf _ _ _ hs]
    exact ⟨p * s, by ring⟩
  have h2 : ∀ n, φ (W n) = p * W (n + 1) := by
    intro n
    apply pow_cancel p tf (n + 2)
    have h := congrArg φ (hW n)
    rw [map_pow, hu, ← pow_mul, ← pow_succ', hW, map_add, map_one, map_mul, map_pow, map_natCast] at h
    linear_combination -h
  obtain ⟨y, hy⟩ := exists_lim p W h1
  refine ⟨y, ?_, ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_dvd p _ fun n => ?_
    have a := map_dvd φ (hy n)
    rw [map_pow, map_natCast, map_sub, h2] at a
    have b := ((pow_dvd_pow _ (Nat.le_succ n)).trans (hy (n + 1))).mul_left (p : R)
    have := dvd_sub a b
    convert this using 1
    ring
  · obtain ⟨V, hV, e, he⟩ := iter p c 5
    have h := congrArg Θ (hW 3)
    rw [map_pow, hc, ← pow_mul, ← pow_add, hV, map_add, map_one, map_mul, map_pow, map_natCast] at h
    have h3 : Θ (W 3) = (p : O) ^ 2 * V := pow_cancel p tfO 5 _ _ (by linear_combination -h)
    have a := map_dvd Θ (hy 3)
    rw [map_pow, map_natCast, map_sub, h3] at a
    have b : (p : O) ^ 3 ∣ (p : O) ^ 2 * V - (p : O) ^ 2 * c := ⟨e, by rw [← mul_sub, he]; ring⟩
    have := dvd_add a b
    rwa [sub_add_sub_cancel] at this

/- English proof (translation)
Use `choose Y hY d hd using h`. Set `cs : ℕ → O` to `fun n => (fun x => -d x)^[n] c`. Establish `hcs : ∀ n, cs (n + 1) = -d (cs n)` using `fun n => Function.iterate_succ_apply' _ _ _`. Set `S : ℕ → R` to `fun n => ∑ i ∈ Finset.range n, (p : R) ^ i * Y (cs i)`. Establish `hS : ∀ n, S (n + 1) = S n + (p : R) ^ n * Y (cs n)` using `fun n => Finset.sum_range_succ _ _`.

Establish `h1 : ∀ n, φ (S n) = p * S n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [S]`. Consider the case `succ n ih => rw [hS, map_add, ih, map_mul, map_pow, map_natCast, hY]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ n, Θ (S n) = (p : O) ^ 2 * c - (p : O) ^ (n + 2) * cs n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [S, cs]`.

Consider the case `succ n ih`. Rewrite using `[hS, map_add, ih, map_mul, map_pow, map_natCast, hcs]`. Take the linear combination `(p : O) ^ n * hd (cs n)`. Take `⟨y, hy⟩` from `exists_lim p S fun n => ⟨Y (cs n), by rw [hS]; ring⟩`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_dvd p _ fun n => ?_` and prove the remaining obligations. Establish `a` using `map_dvd φ (hy n)`. Rewrite `a` using `[map_pow, map_natCast, map_sub, h1]`. Use `dvd_sub a ((hy n).mul_left (p : R))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_dvd p _ fun n => ?_` and prove the remaining obligations. Establish `a` using `map_dvd Θ (hy n)`.

Rewrite `a` using `[map_pow, map_natCast, map_sub, h2]`. Establish `b : (p : O) ^ n ∣ (p : O) ^ (n + 2) * cs n` using `(pow_dvd_pow _ (Nat.le_add_right n 2)).mul_right _`. Use `dvd_sub a b` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_exact [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (φ : R →+* R) (Θ : R →+* O)
    (h : ∀ c : O, ∃ y : R, φ y = p * y ∧ (p : O) ^ 3 ∣ Θ y - (p : O) ^ 2 * c) (c : O) :
    ∃ y : R, φ y = p * y ∧ Θ y = (p : O) ^ 2 * c := by
  choose Y hY d hd using h
  let cs : ℕ → O := fun n => (fun x => -d x)^[n] c
  have hcs : ∀ n, cs (n + 1) = -d (cs n) := fun n => Function.iterate_succ_apply' _ _ _
  let S : ℕ → R := fun n => ∑ i ∈ Finset.range n, (p : R) ^ i * Y (cs i)
  have hS : ∀ n, S (n + 1) = S n + (p : R) ^ n * Y (cs n) := fun n => Finset.sum_range_succ _ _
  have h1 : ∀ n, φ (S n) = p * S n := by
    intro n
    induction n with
    | zero => simp [S]
    | succ n ih => rw [hS, map_add, ih, map_mul, map_pow, map_natCast, hY]; ring
  have h2 : ∀ n, Θ (S n) = (p : O) ^ 2 * c - (p : O) ^ (n + 2) * cs n := by
    intro n
    induction n with
    | zero => simp [S, cs]
    | succ n ih =>
      rw [hS, map_add, ih, map_mul, map_pow, map_natCast, hcs]
      linear_combination (p : O) ^ n * hd (cs n)
  obtain ⟨y, hy⟩ := exists_lim p S fun n => ⟨Y (cs n), by rw [hS]; ring⟩
  refine ⟨y, ?_, ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_dvd p _ fun n => ?_
    have a := map_dvd φ (hy n)
    rw [map_pow, map_natCast, map_sub, h1] at a
    have := dvd_sub a ((hy n).mul_left (p : R))
    convert this using 1
    ring
  · rw [← sub_eq_zero]
    refine eq_zero_of_dvd p _ fun n => ?_
    have a := map_dvd Θ (hy n)
    rw [map_pow, map_natCast, map_sub, h2] at a
    have b : (p : O) ^ n ∣ (p : O) ^ (n + 2) * cs n := (pow_dvd_pow _ (Nat.le_add_right n 2)).mul_right _
    have := dvd_sub a b
    convert this using 1
    ring

/- English proof (translation)
Rewrite using `[← map_natCast f, ← map_mul, h, map_one]`.
-/
theorem map_inv_nat (f : R →+* O) (v : R) (h : (p : R) * v = 1) : (p : O) * f v = 1 := by
  rw [← map_natCast f, ← map_mul, h, map_one]

end Abstract

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

variable (l : ℕ) [hl : Fact l.Prime]

/- English proof (translation)
Establish `hr : ∀ a : Per.OC l, ∃ b : Per.OC l, b ^ l = a`. Introduce `a`. Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl.out.pos`. Establish `h1 : ‖b‖ ^ l ≤ 1` using `by rw [← norm_pow, hb]; exact (GlobalTheory.RingBasics.mem_OC _).1 a.2`. Conclude with `⟨⟨b, (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h1)⟩, Subtype.ext hb⟩`.

Use `choose r hr using hr`. Take `⟨e, he⟩` from `zeta_exists_tilt (p := l) (O := Per.OC l) (fun n => r^[n] c) (fun n => by`. Rewrite using `[Function.iterate_succ_apply', hr])`. Conclude with `⟨e, he 0⟩`.
-/
theorem untilt_surjective (c : Per.OC l) : ∃ x : Per.Fl l, x.untilt = c := by
  have hr : ∀ a : Per.OC l, ∃ b : Per.OC l, b ^ l = a := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl.out.pos
    have h1 : ‖b‖ ^ l ≤ 1 := by rw [← norm_pow, hb]; exact (GlobalTheory.RingBasics.mem_OC _).1 a.2
    exact ⟨⟨b, (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h1)⟩,
      Subtype.ext hb⟩
  choose r hr using hr
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l) (fun n => r^[n] c) (fun n => by
    rw [Function.iterate_succ_apply', hr])
  exact ⟨e, he 0⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem theta_tm (x : Per.Fl l) : Per.θ l (Per.tm x) = x.untilt := by
  simp

/- English proof (translation)
Take `⟨dinv, hd⟩` from `(GlobalTheory.RingBasics.isUnit_nat l l.factorial l.factorial_ne_zero).exists_right_inv`. Establish `e : ((l.factorial : ℕ) : Per.AinfP l) * (dinv * algebraMap (Per.Ainf l) (Per.AinfP l) k ^ l) = algebraMap (Per.Ainf l) (Per.AinfP l) k ^ l` using `by rw [← mul_assoc, hd, one_mul]`. Establish `hdm : dinv * algebraMap (Per.Ainf l) (Per.AinfP l) k ^ l ∈ Per.Acris0 l` using `GlobalTheory.RingIface.dividedPower_mem_Acris0 l k l _ hk e`. Establish `e' : ((l.factorial : ℕ) : Per.Acris0 l) * ⟨_, hdm⟩ = algebraMap (Per.Ainf l) (Per.Acris0 l) k ^ l` using `Subtype.ext (by simpa using e)`. Establish `h` using `congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e'`.

Rewrite `h` using `[map_mul, map_natCast, map_pow]`. Establish `h0 : algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) k) = algebraMap (Per.Ainf l) (Per.Acris l) k` using `(GlobalTheory.RingIface.tower l k).symm`. Rewrite using `[← h0, ← h]`. Conclude with `(Nat.cast_dvd_cast (Nat.dvd_factorial hl.out.pos le_rfl)).mul_right _`.
-/
theorem dvd_pow_of_ker (k : Per.Ainf l) (hk : Per.θ l k = 0) :
    ((l : ℕ) : Per.Acris l) ∣ algebraMap (Per.Ainf l) (Per.Acris l) k ^ l := by
  obtain ⟨dinv, hd⟩ := (GlobalTheory.RingBasics.isUnit_nat l l.factorial l.factorial_ne_zero).exists_right_inv
  have e : ((l.factorial : ℕ) : Per.AinfP l) * (dinv * algebraMap (Per.Ainf l) (Per.AinfP l) k ^ l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) k ^ l := by rw [← mul_assoc, hd, one_mul]
  have hdm : dinv * algebraMap (Per.Ainf l) (Per.AinfP l) k ^ l ∈ Per.Acris0 l :=
    GlobalTheory.RingIface.dividedPower_mem_Acris0 l k l _ hk e
  have e' : ((l.factorial : ℕ) : Per.Acris0 l) * ⟨_, hdm⟩ = algebraMap (Per.Ainf l) (Per.Acris0 l) k ^ l :=
    Subtype.ext (by simpa using e)
  have h := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e'
  rw [map_mul, map_natCast, map_pow] at h
  have h0 : algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) k) =
    algebraMap (Per.Ainf l) (Per.Acris l) k := (GlobalTheory.RingIface.tower l k).symm
  rw [← h0, ← h]
  exact (Nat.cast_dvd_cast (Nat.dvd_factorial hl.out.pos le_rfl)).mul_right _

/- English proof (translation)
Take `⟨a, ha⟩` from `untilt_surjective l c`. Establish `hk` using `dvd_pow_of_ker l (Per.tm x - 1 - (l : Per.Ainf l) ^ 2 * Per.tm a) (by`. Rewrite using `[map_sub, map_sub, map_mul, map_pow, map_natCast, map_one, theta_tm, theta_tm, hx, ha]`. Use the proof step `ring)`. Rewrite `hk` using `[map_sub, map_sub, map_mul, map_pow, map_natCast, map_one]`.

Generalize the expression as in `algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm x) = X at hk ⊢`. Generalize the expression as in `algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm a) = A at hk`. Use `set k := X - 1 - ((l : ℕ) : Per.Acris l) ^ 2 * A with hkdef`. Establish `h1 : ((l : ℕ) : Per.Acris l) ∣ X - (1 + k)` using `⟨l * A, by rw [hkdef]; ring⟩`. Establish `h2` using `h1.trans (sub_dvd_pow_sub_pow _ _ l)`.

Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hl.out (1 : Per.Acris l) k`. Establish `h3 : ((l : ℕ) : Per.Acris l) ∣ X ^ l - 1`. Use `dvd_add (dvd_add h2 hk) (dvd_mul_right ((l : ℕ) : Per.Acris l) (k * r))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hr]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw⟩` from `dvd_sub_pow_of_dvd_sub h3 1`. Conclude with `⟨w, by rw [pow_two l, pow_mul]; rw [pow_one, one_pow] at hw; linear_combination hw⟩`.
-/
theorem tm_pow_sq (x : Per.Fl l) (c : Per.OC l) (hx : x.untilt = 1 + (l : Per.OC l) ^ 2 * c) :
    ∃ w : Per.Acris l, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm x) ^ l ^ 2 =
      1 + ((l : ℕ) : Per.Acris l) ^ 2 * w := by
  obtain ⟨a, ha⟩ := untilt_surjective l c
  have hk := dvd_pow_of_ker l (Per.tm x - 1 - (l : Per.Ainf l) ^ 2 * Per.tm a) (by
    rw [map_sub, map_sub, map_mul, map_pow, map_natCast, map_one, theta_tm, theta_tm, hx, ha]; ring)
  rw [map_sub, map_sub, map_mul, map_pow, map_natCast, map_one] at hk
  generalize algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm x) = X at hk ⊢
  generalize algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm a) = A at hk
  set k := X - 1 - ((l : ℕ) : Per.Acris l) ^ 2 * A with hkdef
  have h1 : ((l : ℕ) : Per.Acris l) ∣ X - (1 + k) := ⟨l * A, by rw [hkdef]; ring⟩
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ l)
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out (1 : Per.Acris l) k
  have h3 : ((l : ℕ) : Per.Acris l) ∣ X ^ l - 1 := by
    have := dvd_add (dvd_add h2 hk) (dvd_mul_right ((l : ℕ) : Per.Acris l) (k * r))
    convert this using 1
    rw [hr]
    ring
  obtain ⟨w, hw⟩ := dvd_sub_pow_of_dvd_sub h3 1
  exact ⟨w, by rw [pow_two l, pow_mul]; rw [pow_one, one_pow] at hw; linear_combination hw⟩

variable {l}

/- English proof (translation)
Rewrite using `[← (thetaD_props l).2.2.2.1 a, GlobalTheory.RingIface.tower]`. Conclude with `congrArg (Per.θD l) (C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) a))`.
-/
theorem theta_j_alg (C : Core l) (a : Per.Ainf l) :
    Per.θD l (C.j (algebraMap (Per.Ainf l) (Per.Acris l) a)) = (Per.θ l a : ℂ_[l]) := by
  rw [← (thetaD_props l).2.2.2.1 a, GlobalTheory.RingIface.tower]
  exact congrArg (Per.θD l) (C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) a))

/- English proof (translation)
Take `⟨N, hN⟩` from `C.j_cris.bdd 1`. Establish `hb : ∀ y : Per.Acris l, ‖(l : ℂ_[l])‖ ^ N * ‖Per.θD l (C.j y)‖ ≤ 1`. Introduce `y`. Take `⟨a, ha⟩` from `hN y`. Establish `h1 : Per.θD l (((l : ℕ) : Per.BdRp l) ^ N * C.j y) = Per.θD l (aDp l a)`.

Establish `h2 : Per.ev l 1 (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a)` using `GlobalTheory.RingIface.ev_alg l 1 _`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Use `((thetaD_props l).2.1 _).2 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 1 _).2 ?_)` and prove the remaining obligations. Rewrite using `[map_sub, ha, h2, sub_self]`. Rewrite `h1` using `[map_mul, map_pow, map_natCast, (thetaD_props l).2.2.2.1 a]`.

Rewrite using `[← norm_pow, ← norm_mul, h1]`. Conclude with `(GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2`. Assume the negation of the conclusion as `hx`. Establish `hp : 0 < ‖(l : ℂ_[l])‖ ^ N` using `pow_pos (norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero) N`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (‖(l : ℂ_[l])‖ ^ N)⁻¹ (not_le.1 hx)`.

Use `hb (x ^ n)` as an intermediate fact. Rewrite `this` using `[map_pow, map_pow, norm_pow]`. Rewrite `hn` using `[inv_lt_iff_one_lt_mul₀' hp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_theta_j_le (C : Core l) (x : Per.Acris l) : ‖Per.θD l (C.j x)‖ ≤ 1 := by
  obtain ⟨N, hN⟩ := C.j_cris.bdd 1
  have hb : ∀ y : Per.Acris l, ‖(l : ℂ_[l])‖ ^ N * ‖Per.θD l (C.j y)‖ ≤ 1 := by
    intro y
    obtain ⟨a, ha⟩ := hN y
    have h1 : Per.θD l (((l : ℕ) : Per.BdRp l) ^ N * C.j y) = Per.θD l (aDp l a) := by
      have h2 : Per.ev l 1 (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) :=
        GlobalTheory.RingIface.ev_alg l 1 _
      rw [← sub_eq_zero, ← map_sub]
      refine ((thetaD_props l).2.1 _).2 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 1 _).2 ?_)
      rw [map_sub, ha, h2, sub_self]
    rw [map_mul, map_pow, map_natCast, (thetaD_props l).2.2.2.1 a] at h1
    rw [← norm_pow, ← norm_mul, h1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  by_contra hx
  have hp : 0 < ‖(l : ℂ_[l])‖ ^ N := pow_pos (norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero) N
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖(l : ℂ_[l])‖ ^ N)⁻¹ (not_le.1 hx)
  have := hb (x ^ n)
  rw [map_pow, map_pow, norm_pow] at this
  rw [inv_lt_iff_one_lt_mul₀' hp] at hn
  linarith

/- English proof (translation)
Set `Θ : Per.Acris l →+* Per.OC l` to `((Per.θD l).comp C.j).codRestrict _ fun x => (GlobalTheory.RingBasics.mem_OC _).2 (norm_theta_j_le C x)`. Use `haveI := (acris_basic l).1`. Take `⟨y, h1, h2⟩` from `exists_exact l (phiA l) Θ (fun c => by`. Take `⟨x, hx⟩` from `untilt_surjective l (1 + (l : Per.OC l) ^ 2 * c)`. Take `⟨w, hw⟩` from `tm_pow_sq l x c hx`.

Use `exists_log l (acris_basic l).2.1 (fun z hz => ?_) (phiA l) Θ w ?_ c ?_` and prove the remaining obligations. Use `(mul_eq_zero.1 hz).resolve_left fun h => GlobalTheory.RingBasics.p_ne_zero (p := l) ?_` and prove the remaining obligations. Simplify using `using congrArg Subtype.val h`. Rewrite using `[← hw, map_pow, (GlobalTheory.CrisMaps.phiA_extends l).alg, ← pow_mul, mul_comm, pow_mul, ← map_pow _ _ l]`. Use `congr 2`.

Conclude with `(GlobalTheory.RingIface.phiA_teich l x).trans (map_pow _ _ _)`. Rewrite using `[← hw, map_pow, ← hx, ← theta_tm]`. Use `congr 1`. Conclude with `Subtype.ext (theta_j_alg C _)) c`. Use `⟨y, h1, ?_⟩` and prove the remaining obligations.

Establish `h3 : ((Θ y : Per.OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ 2 * c` using `by simpa using congrArg Subtype.val h2`. Conclude with `h3`.
-/
theorem exists_eigen_int (C : Core l) (c : Per.OC l) : ∃ y : Per.Acris l, phiA l y = l * y ∧
    Per.θD l (C.j y) = (l : ℂ_[l]) ^ 2 * c := by
  let Θ : Per.Acris l →+* Per.OC l := ((Per.θD l).comp C.j).codRestrict _ fun x =>
    (GlobalTheory.RingBasics.mem_OC _).2 (norm_theta_j_le C x)
  haveI := (acris_basic l).1
  obtain ⟨y, h1, h2⟩ := exists_exact l (phiA l) Θ (fun c => by
    obtain ⟨x, hx⟩ := untilt_surjective l (1 + (l : Per.OC l) ^ 2 * c)
    obtain ⟨w, hw⟩ := tm_pow_sq l x c hx
    refine exists_log l (acris_basic l).2.1 (fun z hz => ?_) (phiA l) Θ w ?_ c ?_
    · refine (mul_eq_zero.1 hz).resolve_left fun h => GlobalTheory.RingBasics.p_ne_zero (p := l) ?_
      simpa using congrArg Subtype.val h
    · rw [← hw, map_pow, (GlobalTheory.CrisMaps.phiA_extends l).alg, ← pow_mul, mul_comm, pow_mul, ← map_pow _ _ l]
      congr 2
      exact (GlobalTheory.RingIface.phiA_teich l x).trans (map_pow _ _ _)
    · rw [← hw, map_pow, ← hx, ← theta_tm]
      congr 1
      exact Subtype.ext (theta_j_alg C _)) c
  refine ⟨y, h1, ?_⟩
  have h3 : ((Θ y : Per.OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ 2 * c := by simpa using congrArg Subtype.val h2
  exact h3

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, ‖(l : ℂ_[l]) ^ k * c‖ ≤ 1 := by`. Establish `h` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const ‖c‖`. Rewrite `h` using `[zero_mul]`. Take `⟨k, hk⟩` from `(h.eventually (ge_mem_nhds zero_lt_one)).exists`. Conclude with `⟨k, by rwa [norm_mul, norm_pow]⟩`.

Take `⟨y, h1, h2⟩` from `exists_eigen_int C ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hk⟩`. Take `⟨v, hv⟩` from `(isUnit_l_Bcris l).exists_right_inv`. Take `⟨v', hv'⟩` from `(isUnit_l_BdRp l).exists_right_inv`. Establish `e1 : Per.φB l v = v`. Use `map_inv_nat l (Per.φB l) v hv` as an intermediate fact.

Take the linear combination `v * this - Per.φB l v * hv`. Establish `e2 : C.ι v = algebraMap (Per.BdRp l) (Per.BdR l) v'`. Establish `a` using `map_inv_nat l C.ι v hv`. Establish `b` using `map_inv_nat l (algebraMap (Per.BdRp l) (Per.BdR l)) v' hv'`. Take the linear combination `algebraMap (Per.BdRp l) (Per.BdR l) v' * a - C.ι v * b`.

Establish `e3 : (l : ℂ_[l]) * Per.θD l v' = 1`. Use `congrArg (Per.θD l) hv'` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_one]`. Then use the resulting hypothesis. Use `⟨v ^ (k + 2) * algebraMap _ _ y, v' ^ (k + 2) * C.j y, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, e1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 y, h1, map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_pow, e2, C.ι_j, map_mul, map_pow]`. Rewrite using `[map_mul, map_pow, h2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_eigen (C : Core l) (c : ℂ_[l]) : ∃ (a : Per.Bcris l) (a' : Per.BdRp l),
    Per.φB l a = l * a ∧ C.ι a = algebraMap (Per.BdRp l) (Per.BdR l) a' ∧ Per.θD l a' = c := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(l : ℂ_[l]) ^ k * c‖ ≤ 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))).mul_const ‖c‖
    rw [zero_mul] at h
    obtain ⟨k, hk⟩ := (h.eventually (ge_mem_nhds zero_lt_one)).exists
    exact ⟨k, by rwa [norm_mul, norm_pow]⟩
  obtain ⟨y, h1, h2⟩ := exists_eigen_int C ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 hk⟩
  obtain ⟨v, hv⟩ := (isUnit_l_Bcris l).exists_right_inv
  obtain ⟨v', hv'⟩ := (isUnit_l_BdRp l).exists_right_inv
  have e1 : Per.φB l v = v := by
    have := map_inv_nat l (Per.φB l) v hv
    linear_combination v * this - Per.φB l v * hv
  have e2 : C.ι v = algebraMap (Per.BdRp l) (Per.BdR l) v' := by
    have a := map_inv_nat l C.ι v hv
    have b := map_inv_nat l (algebraMap (Per.BdRp l) (Per.BdR l)) v' hv'
    linear_combination algebraMap (Per.BdRp l) (Per.BdR l) v' * a - C.ι v * b
  have e3 : (l : ℂ_[l]) * Per.θD l v' = 1 := by
    have := congrArg (Per.θD l) hv'
    rwa [map_mul, map_natCast, map_one] at this
  refine ⟨v ^ (k + 2) * algebraMap _ _ y, v' ^ (k + 2) * C.j y, ?_, ?_, ?_⟩
  · rw [map_mul, map_pow, e1, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 y, h1, map_mul, map_natCast]
    ring
  · rw [map_mul, map_pow, e2, C.ι_j, map_mul, map_pow]
  · rw [map_mul, map_pow, h2]
    calc _ = ((l : ℂ_[l]) * Per.θD l v') ^ (k + 2) * c := by ring
      _ = c := by rw [e3, one_pow, one_mul]

/- English proof (translation)
Introduce `l _ C`. Establish `he` using `core_isEps l C`. Take `⟨hu, ht1, ht2, -⟩` from `core_t_unit_fil l C`. Take `⟨hfil, -, -, -⟩` from `filtration_eq_xi_pow l C.ε he`. Take `⟨-, hker, hunit, -⟩` from `thetaD_props l`.

Take `⟨v, hv⟩` from `(hfil 1 _).1 ht1`. Rewrite `hv` using `[pow_one]`. Choose the witnesses or unpack the hypotheses as in `⟨v', hv'⟩ : ∃ v', v * v' = 1 := by`. Use `(hunit v fun h => ht2 ((hfil 2 _).2 ?_)).exists_right_inv` and prove the remaining obligations. Take `⟨z, hz⟩` from `(hfil 1 _).1 ((hker v).1 h)`.

Conclude with `⟨z, by rw [hv, hz]; ring⟩`. Take `⟨s, hs⟩` from `hu.exists_right_inv`. Establish `hT : algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) * C.ι s = 1`. Rewrite using `[← C.ι_j, ← map_mul, hs, map_one]`. Establish `hφ : (l : Per.Bcris l) * Per.φB l s = s`.

Use `congrArg (Per.φB l) hs` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2, TPhi.t_phi l C, map_mul, map_natCast]`. Take the linear combination `s * this - (l : Per.Bcris l) * Per.φB l s * hs`. Take `⟨o, o', ho1, ho2, ho3⟩` from `exists_eigen C 1`. Establish `key : ∀ (n : ℕ) (y : Per.BdRp l), ∃ b : Per.Bcris l, Per.φB l b = b ∧ C.ι b - algebraMap (Per.BdRp l) (Per.BdR l) y * C.ι s ^ n ∈ Per.FilD l 0`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `y`. Use `⟨0, map_zero _, ?_⟩` and prove the remaining obligations.

Establish `h0` using `GlobalTheory.RingIface.alg_mem_FilD_nat l (n := 0) (z := -y) ((hfil 0 _).2 (by`. Rewrite using `[pow_zero]`. Conclude with `one_dvd _))`. Rewrite `h0` using `[map_neg, Nat.cast_zero]`. Rewrite using `[map_zero, pow_zero, mul_one, zero_sub]` and apply the resulting hypothesis.

Consider the case `succ n ih`. Introduce `y`. Take `⟨a, a', ha1, ha2, ha3⟩` from `exists_eigen C (Per.θD l y)`. Take `⟨z, hz⟩` from `(hfil 1 _).1 ((hker (y - a' * o' ^ n)).1 (by`. Rewrite using `[map_sub, map_mul, map_pow, ha3, ho3, one_pow, mul_one, sub_self]))`.

Establish `hz' : y = a' * o' ^ n + C.j C.t * (v' * z)`. Rewrite using `[hv]`. Take the linear combination `hz - aDp l (xi C.ε) * z * hv'`. Take `⟨b, hb1, hb2⟩` from `ih (v' * z)`. Use `⟨b + a * o ^ n * s ^ (n + 1), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, hb1, map_mul, map_mul, map_pow, map_pow, ha1, ho1]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use `hb2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, ha2, ho2]`.

Use `conv_lhs => rw [hz']`. Rewrite using `[map_add, map_mul, map_pow, map_mul (algebraMap (Per.BdRp l) (Per.BdR l)) (C.j C.t)]`. Take the linear combination `(-(algebraMap (Per.BdRp l) (Per.BdR l) (v' * z) * C.ι s ^ n)) * hT`. Introduce `w`. Take `⟨n, y, hy⟩` from `(BdRField.bdR_isField l).2.2.2 C.ε he w`.

Take `⟨b, hb1, hb2⟩` from `key n (y * v ^ n)`. Use `⟨b, hb1, ?_⟩` and prove the remaining obligations. Use `hb2 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, ← hy, map_pow]`. Rewrite `hT` using `[hv, map_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem fundOnto : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.FundOnto := by
  intro l _ C
  have he := core_isEps l C
  obtain ⟨hu, ht1, ht2, -⟩ := core_t_unit_fil l C
  obtain ⟨hfil, -, -, -⟩ := filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -⟩ := thetaD_props l
  obtain ⟨v, hv⟩ := (hfil 1 _).1 ht1
  rw [pow_one] at hv
  obtain ⟨v', hv'⟩ : ∃ v', v * v' = 1 := by
    refine (hunit v fun h => ht2 ((hfil 2 _).2 ?_)).exists_right_inv
    obtain ⟨z, hz⟩ := (hfil 1 _).1 ((hker v).1 h)
    exact ⟨z, by rw [hv, hz]; ring⟩
  obtain ⟨s, hs⟩ := hu.exists_right_inv
  have hT : algebraMap (Per.BdRp l) (Per.BdR l) (C.j C.t) * C.ι s = 1 := by
    rw [← C.ι_j, ← map_mul, hs, map_one]
  have hφ : (l : Per.Bcris l) * Per.φB l s = s := by
    have := congrArg (Per.φB l) hs
    rw [map_mul, map_one, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2, TPhi.t_phi l C, map_mul,
      map_natCast] at this
    linear_combination s * this - (l : Per.Bcris l) * Per.φB l s * hs
  obtain ⟨o, o', ho1, ho2, ho3⟩ := exists_eigen C 1
  have key : ∀ (n : ℕ) (y : Per.BdRp l), ∃ b : Per.Bcris l, Per.φB l b = b ∧
      C.ι b - algebraMap (Per.BdRp l) (Per.BdR l) y * C.ι s ^ n ∈ Per.FilD l 0 := by
    intro n
    induction n with
    | zero =>
      intro y
      refine ⟨0, map_zero _, ?_⟩
      have h0 := GlobalTheory.RingIface.alg_mem_FilD_nat l (n := 0) (z := -y) ((hfil 0 _).2 (by
        rw [pow_zero]; exact one_dvd _))
      rw [map_neg, Nat.cast_zero] at h0
      rwa [map_zero, pow_zero, mul_one, zero_sub]
    | succ n ih =>
      intro y
      obtain ⟨a, a', ha1, ha2, ha3⟩ := exists_eigen C (Per.θD l y)
      obtain ⟨z, hz⟩ := (hfil 1 _).1 ((hker (y - a' * o' ^ n)).1 (by
        rw [map_sub, map_mul, map_pow, ha3, ho3, one_pow, mul_one, sub_self]))
      have hz' : y = a' * o' ^ n + C.j C.t * (v' * z) := by
        rw [hv]
        linear_combination hz - aDp l (xi C.ε) * z * hv'
      obtain ⟨b, hb1, hb2⟩ := ih (v' * z)
      refine ⟨b + a * o ^ n * s ^ (n + 1), ?_, ?_⟩
      · rw [map_add, hb1, map_mul, map_mul, map_pow, map_pow, ha1, ho1]
        congr 1
        calc _ = a * o ^ n * ((l : Per.Bcris l) * Per.φB l s) ^ (n + 1) := by ring
          _ = _ := by rw [hφ]
      · convert hb2 using 1
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ha2, ho2]
        conv_lhs => rw [hz']
        rw [map_add, map_mul, map_pow, map_mul (algebraMap (Per.BdRp l) (Per.BdR l)) (C.j C.t)]
        linear_combination (-(algebraMap (Per.BdRp l) (Per.BdR l) (v' * z) * C.ι s ^ n)) * hT
  intro w
  obtain ⟨n, y, hy⟩ := (BdRField.bdR_isField l).2.2.2 C.ε he w
  obtain ⟨b, hb1, hb2⟩ := key n (y * v ^ n)
  refine ⟨b, hb1, ?_⟩
  convert hb2 using 2
  rw [map_mul, ← hy, map_pow]
  rw [hv, map_mul] at hT
  calc w = w * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi C.ε)) *
        algebraMap (Per.BdRp l) (Per.BdR l) v * C.ι s) ^ n := by rw [hT, one_pow, mul_one]
    _ = _ := by ring

end GlobalTheory.MemLoc.FundOnto
