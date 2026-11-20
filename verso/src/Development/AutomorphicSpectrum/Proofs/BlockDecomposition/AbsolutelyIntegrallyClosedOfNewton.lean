import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.AicLimit

/- English proof (translation)
Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem mem_pow_smul_top_iff {S : Type} [CommRing S] (t y : S) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule S S) ↔ t ^ n ∣ y := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Establish `hnt : Nontrivial S`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Rewrite `hd` using `[Subsingleton.elim P 0, Polynomial.natDegree_zero]`. Conclude with `lt_irrefl 0 hd`.

Establish `hq : (Polynomial.X + Polynomial.C x).natDegree = 1` using `Polynomial.natDegree_X_add_C x`. Establish `hQm : (P.comp (Polynomial.X + Polynomial.C x)).Monic` using `hP.comp (Polynomial.monic_X_add_C x) (by rw [hq]; exact one_ne_zero)`. Establish `hQd : (P.comp (Polynomial.X + Polynomial.C x)).natDegree = P.natDegree`. Rewrite using `[Polynomial.natDegree_comp_eq_of_mul_ne_zero (by`. Rewrite using `[hP.leadingCoeff, (Polynomial.monic_X_add_C x).leadingCoeff, one_pow, one_mul]`.

Conclude with `one_ne_zero), hq, mul_one]`. Take `⟨z, hz1, hz2⟩` from `hS (P.comp (Polynomial.X + Polynomial.C x)) n hQm (by rw [hQd]; exact hd) (by simpa [Polynomial.eval_comp] using hx)`. Use `⟨z, ?_, ?_⟩` and prove the remaining obligations. Simplify `hz1` using `[Polynomial.eval_comp, add_comm]`. Rewrite `hz2` using `[hQd]`. Then use the resulting hypothesis.
-/
theorem step_at {S : Type} [CommRing S] {ϖ : S} (hS : Step ϖ) (P : Polynomial S) (hP : P.Monic)
    (hd : 0 < P.natDegree) (n : ℕ) (x : S) (hx : ϖ ^ n ∣ P.eval x) :
    ∃ z, ϖ ^ (n + 1) ∣ P.eval (x + z) ∧ ϖ ^ n ∣ z ^ P.natDegree := by
  have hnt : Nontrivial S := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
    exact lt_irrefl 0 hd
  have hq : (Polynomial.X + Polynomial.C x).natDegree = 1 := Polynomial.natDegree_X_add_C x
  have hQm : (P.comp (Polynomial.X + Polynomial.C x)).Monic :=
    hP.comp (Polynomial.monic_X_add_C x) (by rw [hq]; exact one_ne_zero)
  have hQd : (P.comp (Polynomial.X + Polynomial.C x)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero (by
      rw [hP.leadingCoeff, (Polynomial.monic_X_add_C x).leadingCoeff, one_pow, one_mul]
      exact one_ne_zero), hq, mul_one]
  obtain ⟨z, hz1, hz2⟩ := hS (P.comp (Polynomial.X + Polynomial.C x)) n hQm (by rw [hQd]; exact hd)
    (by simpa [Polynomial.eval_comp] using hx)
  refine ⟨z, ?_, ?_⟩
  · simpa [Polynomial.eval_comp, add_comm] using hz1
  · rwa [hQd] at hz2

/- English proof (translation)
Set `next : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} → {x : S // ϖ ^ (n + 1) ∣ P.eval x}` to `fun n x => ⟨x.1 + Classical.choose (step_at hS P hP hd n x.1 x.2), (Classical.choose_spec (step_at hS P hP hd n x.1 x.2)).1⟩`. Set `seq : ∀ n, {x : S // ϖ ^ n ∣ P.eval x}` to `fun n => Nat.rec (motive := fun n => {x : S // ϖ ^ n ∣ P.eval x}) ⟨0, by simp⟩ next n`. Use `⟨fun n => (seq n).1, fun n => (seq n).2, fun n => ?_⟩` and prove the remaining obligations. Establish `h` using `(Classical.choose_spec (step_at hS P hP hd n (seq n).1 (seq n).2)).2`. Establish `he : (seq (n + 1)).1 - (seq n).1 = Classical.choose (step_at hS P hP hd n (seq n).1 (seq n).2)` using `add_sub_cancel_left (seq n).1 _`.

Use `show ϖ ^ n ∣ ((seq (n + 1)).1 - (seq n).1) ^ P.natDegree`. Rewrite using `[he]`. Conclude with `h`.
-/
theorem exists_seq {S : Type} [CommRing S] {ϖ : S} (hS : Step ϖ) (P : Polynomial S) (hP : P.Monic)
    (hd : 0 < P.natDegree) :
    ∃ x : ℕ → S, (∀ n, ϖ ^ n ∣ P.eval (x n)) ∧ ∀ n, ϖ ^ n ∣ (x (n + 1) - x n) ^ P.natDegree := by
  let next : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} → {x : S // ϖ ^ (n + 1) ∣ P.eval x} := fun n x =>
    ⟨x.1 + Classical.choose (step_at hS P hP hd n x.1 x.2),
      (Classical.choose_spec (step_at hS P hP hd n x.1 x.2)).1⟩
  let seq : ∀ n, {x : S // ϖ ^ n ∣ P.eval x} := fun n =>
    Nat.rec (motive := fun n => {x : S // ϖ ^ n ∣ P.eval x}) ⟨0, by simp⟩ next n
  refine ⟨fun n => (seq n).1, fun n => (seq n).2, fun n => ?_⟩
  have h := (Classical.choose_spec (step_at hS P hP hd n (seq n).1 (seq n).2)).2
  have he : (seq (n + 1)).1 - (seq n).1 = Classical.choose (step_at hS P hP hd n (seq n).1 (seq n).2) :=
    add_sub_cancel_left (seq n).1 _
  show ϖ ^ n ∣ ((seq (n + 1)).1 - (seq n).1) ^ P.natDegree
  rw [he]
  exact h

/- English proof (translation)
Introduce `S _ ϖ _ hS hroot P hP hd0`. Take `⟨x, hx1, hx2⟩` from `exists_seq hS P hP hd0`. Take `⟨d, hdd⟩ : ∃ d, d = P.natDegree` from `⟨_, rfl⟩`. Rewrite `hx2`, `hd0` using `[← hdd]`. Establish `hΔ : ∀ n, ϖ ^ (n / d) ∣ x (n + 1) - x n` using `fun n => hroot _ (n / d) d hd0 ((pow_dvd_pow ϖ (Nat.div_mul_le_self n d)).trans (hx2 n))`.

Establish `hstep : ∀ k, ϖ ^ k ∣ x ((k + 1) * d) - x (k * d)`. Introduce `k`. Establish `hi : ∀ i, ϖ ^ k ∣ x (k * d + i) - x (k * d)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `h1 : ϖ ^ k ∣ x (k * d + i + 1) - x (k * d + i)` using `(pow_dvd_pow ϖ ((Nat.le_div_iff_mul_le hd0).2 (Nat.le_add_right _ _))).trans (hΔ (k * d + i))`. Rewrite using `[show k * d + (i + 1) = k * d + i + 1 from rfl, ← sub_add_sub_cancel (x (k * d + i + 1)) (x (k * d + i)) (x (k * d))]`. Conclude with `dvd_add h1 ih`.

Establish `h3` using `hi d`. Rewrite `h3` using `[show k * d + d = (k + 1) * d by ring]`. Then use the resulting hypothesis. Establish `hcauchy : ∀ m n, m ≤ n → ϖ ^ m ∣ x (n * d) - x (m * d)`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[← sub_add_sub_cancel (x ((n + 1) * d)) (x (n * d)) (x (m * d))]`. Conclude with `dvd_add ((pow_dvd_pow ϖ hmn).trans (hstep n)) ih`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := Ideal.span {ϖ}) inferInstance (f := fun k => x (k * d)) (fun {m n} hmn => by`.

Rewrite using `[SModEq.sub_mem, mem_pow_smul_top_iff]`. Conclude with `dvd_sub_comm.1 (hcauchy m n hmn))`. Use `⟨L, ?_⟩` and prove the remaining obligations. Use `show Polynomial.eval L P = 0`. Apply `IsHausdorff.haus (I := Ideal.span {ϖ}) inferInstance` to reduce the goal to its premises.

Introduce `k`. Rewrite using `[SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff]`. Establish `h1 : ϖ ^ k ∣ x (k * d) - L`. Establish `h0` using `hL k`. Rewrite `h0` using `[SModEq.sub_mem, mem_pow_smul_top_iff]`.

Conclude with `h0`. Establish `h2 : ϖ ^ k ∣ P.eval (x (k * d))` using `(pow_dvd_pow ϖ (Nat.le_mul_of_pos_right k hd0)).trans (hx1 (k * d))`. Establish `h4 : ϖ ^ k ∣ P.eval (x (k * d)) - P.eval L` using `h1.trans (Polynomial.sub_dvd_eval_sub _ _ _)`. Establish `h5 : P.eval L = P.eval (x (k * d)) - (P.eval (x (k * d)) - P.eval L)` using `by ring`. Rewrite using `[h5]`.

Conclude with `dvd_sub h2 h4`.
-/
theorem aic_of_step : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S],
    Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic S := by
  intro S _ ϖ _ hS hroot P hP hd0
  obtain ⟨x, hx1, hx2⟩ := exists_seq hS P hP hd0
  obtain ⟨d, hdd⟩ : ∃ d, d = P.natDegree := ⟨_, rfl⟩
  rw [← hdd] at hx2 hd0
  have hΔ : ∀ n, ϖ ^ (n / d) ∣ x (n + 1) - x n := fun n =>
    hroot _ (n / d) d hd0 ((pow_dvd_pow ϖ (Nat.div_mul_le_self n d)).trans (hx2 n))
  have hstep : ∀ k, ϖ ^ k ∣ x ((k + 1) * d) - x (k * d) := by
    intro k
    have hi : ∀ i, ϖ ^ k ∣ x (k * d + i) - x (k * d) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 : ϖ ^ k ∣ x (k * d + i + 1) - x (k * d + i) :=
          (pow_dvd_pow ϖ ((Nat.le_div_iff_mul_le hd0).2 (Nat.le_add_right _ _))).trans (hΔ (k * d + i))
        rw [show k * d + (i + 1) = k * d + i + 1 from rfl,
          ← sub_add_sub_cancel (x (k * d + i + 1)) (x (k * d + i)) (x (k * d))]
        exact dvd_add h1 ih
    have h3 := hi d
    rwa [show k * d + d = (k + 1) * d by ring] at h3
  have hcauchy : ∀ m n, m ≤ n → ϖ ^ m ∣ x (n * d) - x (m * d) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [← sub_add_sub_cancel (x ((n + 1) * d)) (x (n * d)) (x (m * d))]
      exact dvd_add ((pow_dvd_pow ϖ hmn).trans (hstep n)) ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {ϖ}) inferInstance
    (f := fun k => x (k * d)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_smul_top_iff]
      exact dvd_sub_comm.1 (hcauchy m n hmn))
  refine ⟨L, ?_⟩
  show Polynomial.eval L P = 0
  apply IsHausdorff.haus (I := Ideal.span {ϖ}) inferInstance
  intro k
  rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff]
  have h1 : ϖ ^ k ∣ x (k * d) - L := by
    have h0 := hL k
    rw [SModEq.sub_mem, mem_pow_smul_top_iff] at h0
    exact h0
  have h2 : ϖ ^ k ∣ P.eval (x (k * d)) :=
    (pow_dvd_pow ϖ (Nat.le_mul_of_pos_right k hd0)).trans (hx1 (k * d))
  have h4 : ϖ ^ k ∣ P.eval (x (k * d)) - P.eval L := h1.trans (Polynomial.sub_dvd_eval_sub _ _ _)
  have h5 : P.eval L = P.eval (x (k * d)) - (P.eval (x (k * d)) - P.eval L) := by ring
  rw [h5]
  exact dvd_sub h2 h4

end GlobalTheory.CompanionTheory.AicLimit
