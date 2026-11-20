import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSpanDividedPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisorStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Take `⟨e, m, hm, hk⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero k) l hp.one_lt.ne'`. Establish `hcop : IsCoprime (((l : ℤ)) : A.W) (((m : ℤ)) : A.W)` using `(Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).intCast`. Take `⟨u, v, huv⟩` from `hcop`. Move the coercions through the operations in `at huv`.

Use `A.completeW` as an intermediate fact. Establish `hj : (l : A.W) ∈ (⊥ : Ideal A.W).jacobson` using `IsAdicComplete.le_jacobson_bot (I := Ideal.span {(l : A.W)}) (Ideal.subset_span (Set.mem_singleton _))`. Establish `hu : IsUnit ((m : A.W) * v)`. Establish `h` using `Ideal.mem_jacobson_bot.1 hj (-u)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Take the linear combination `huv`. Take `⟨t, ht⟩` from `hu.exists_right_inv`. Use `⟨e, v * t, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Use `push_cast`.

Take the linear combination `(l : A.W) ^ e * ht`.
-/
private theorem exists_factorial_mul_eq_pow' (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, m, hm, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero k) l hp.one_lt.ne'
  have hcop : IsCoprime (((l : ℤ)) : A.W) (((m : ℤ)) : A.W) :=
    (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).intCast
  obtain ⟨u, v, huv⟩ := hcop
  push_cast at huv
  have := A.completeW
  have hj : (l : A.W) ∈ (⊥ : Ideal A.W).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {(l : A.W)}) (Ideal.subset_span (Set.mem_singleton _))
  have hu : IsUnit ((m : A.W) * v) := by
    have h := Ideal.mem_jacobson_bot.1 hj (-u)
    convert h using 1
    linear_combination huv
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  refine ⟨e, v * t, ?_⟩
  rw [hk]
  push_cast
  linear_combination (l : A.W) ^ e * ht

/- English proof (translation)
Take `⟨N, c, hc⟩` from `exists_factorial_mul_eq_pow' A k`. Establish `hu : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) (k.factorial : A.W))`. Establish `h1 : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) ((l : A.W) ^ N))`. Rewrite using `[map_pow]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit _).pow N`.

Rewrite `h1` using `[← hc, map_mul]`. Conclude with `isUnit_of_mul_isUnit_left h1`. Rewrite `hu` using `[map_natCast]`. Unfold `CrystallineSemistableComparison.PAlg.dxi0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `push_cast`. Unfold `CrystallineSemistableComparison.dpw`. Rewrite using `[← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]`.
-/
theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k := by
  obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow' A k
  have hu : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) (k.factorial : A.W)) := by
    have h1 : IsUnit (algebraMap A.W (Localization.Away (l : A.W)) ((l : A.W) ^ N)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit _).pow N
    rw [← hc, map_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  rw [map_natCast] at hu
  unfold CrystallineSemistableComparison.PAlg.dxi0
  apply Subtype.ext
  push_cast
  unfold CrystallineSemistableComparison.dpw
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

/- English proof (translation)
Establish `h1` using `factorial_mul_divided_power_xi A 1`. Simplify using `only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1`. Rewrite using `[← h1, divided_power_xi_mul, add_comm 1 r, Nat.choose_one_right]`.
-/
theorem xi_mul_divided_power (r : ℕ) :
    algebraMap A.W A.Acr0 A.xi * A.dxi0 r = ((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1) := by
  have h1 := factorial_mul_divided_power_xi A 1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1
  rw [← h1, divided_power_xi_mul, add_comm 1 r, Nat.choose_one_right]

/- English proof (translation)
Take `⟨c, hc⟩` from `ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) (Nat.factorial_ne_zero k) (le_refl _)`. Use `⟨k.factorial.factorization l, A.sW c, ?_⟩` and prove the remaining obligations. Use `congrArg A.sW hc` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_factorial_mul_eq_pow (k : ℕ) :
    ∃ (N : ℕ) (c : A.W), (k.factorial : A.W) * c = (l : A.W) ^ N := by
  obtain ⟨c, hc⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l)
    (Nat.factorial_ne_zero k) (le_refl _)
  refine ⟨k.factorial.factorization l, A.sW c, ?_⟩
  have := congrArg A.sW hc
  simpa using this

/- English proof (translation)
Rewrite `hz` using `[mem_crystalline_filtration_iff_span]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk, rfl⟩` from `hx`. Take `⟨N, c, hc⟩` from `exists_factorial_mul_eq_pow A k`.

Use `⟨N, A.xi ^ (k - r) * c, ?_⟩` and prove the remaining obligations. Establish `h` using `factorial_mul_divided_power_xi A k`. Combine the equalities or inequalities in the displayed calculation. Use `_ = algebraMap A.W A.Acr0 c * ((k.factorial : A.Acr0) * A.dxi0 k) := by`. Rewrite using `[← hc, map_mul, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = algebraMap A.W A.Acr0 (A.xi ^ r * (A.xi ^ (k - r) * c)) := by`. Rewrite using `[h, ← map_pow, ← map_mul]`. Use `congr 1`. Rewrite using `[← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨N1, w1, h1⟩` from `hx`. Take `⟨N2, w2, h2⟩` from `hy`.

Use `⟨N1 + N2, (l : A.W) ^ N2 * w1 + (l : A.W) ^ N1 * w2, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by`. Rewrite using `[h1, h2]`. Simplify using `only [map_mul, map_add, map_pow, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a x _ hx`. Take `⟨N, w, h⟩` from `hx`. Use `⟨N, a * w, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`.

Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by`. Rewrite using `[h, ← map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem filtration_element_power_multiple_xi (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨N, c, hc⟩ := exists_factorial_mul_eq_pow A k
    refine ⟨N, A.xi ^ (k - r) * c, ?_⟩
    have h := factorial_mul_divided_power_xi A k
    calc (l : A.Acr0) ^ N * A.dxi0 k = algebraMap A.W A.Acr0 ((l : A.W) ^ N) * A.dxi0 k := by simp
    _ = algebraMap A.W A.Acr0 c * ((k.factorial : A.Acr0) * A.dxi0 k) := by
        rw [← hc, map_mul, map_natCast]; ring
    _ = algebraMap A.W A.Acr0 (A.xi ^ r * (A.xi ^ (k - r) * c)) := by
        rw [h, ← map_pow, ← map_mul]
        congr 1
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]
        ring
  | zero => exact ⟨0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N1, w1, h1⟩ := hx
    obtain ⟨N2, w2, h2⟩ := hy
    refine ⟨N1 + N2, (l : A.W) ^ N2 * w1 + (l : A.W) ^ N1 * w2, ?_⟩
    calc (l : A.Acr0) ^ (N1 + N2) * (x + y)
        = (l : A.Acr0) ^ N2 * ((l : A.Acr0) ^ N1 * x) + (l : A.Acr0) ^ N1 * ((l : A.Acr0) ^ N2 * y) := by ring
    _ = _ := by
        rw [h1, h2]
        simp only [map_mul, map_add, map_pow, map_natCast]
        ring
  | smul a x _ hx =>
    obtain ⟨N, w, h⟩ := hx
    refine ⟨N, a * w, ?_⟩
    rw [Algebra.smul_def]
    calc (l : A.Acr0) ^ N * (algebraMap A.W A.Acr0 a * x)
        = algebraMap A.W A.Acr0 a * ((l : A.Acr0) ^ N * x) := by ring
    _ = _ := by
        rw [h, ← map_mul]
        congr 1
        ring

/- English proof (translation)
Rewrite `hz` using `[mem_crystalline_filtration_iff_span]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk, rfl⟩` from `hx`. Break down `hk.eq_or_lt with h | h` into its components or cases.

Substitute `h` using the available equality. Conclude with `⟨1, by simp⟩`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_mul, sub_zero]`. Conclude with `(mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨k, Nat.succ_le_of_lt h, rfl⟩)`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w1, h1⟩` from `hx`. Take `⟨w2, h2⟩` from `hy`. Use `⟨w1 + w2, ?_⟩` and prove the remaining obligations.

Establish `e : x + y - algebraMap A.W A.Acr0 (w1 + w2) * A.dxi0 r = (x - algebraMap A.W A.Acr0 w1 * A.dxi0 r) + (y - algebraMap A.W A.Acr0 w2 * A.dxi0 r)`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ h1 h2`.

Consider the case `smul a x _ hx`. Take `⟨w, h⟩` from `hx`. Use `⟨a * w, ?_⟩` and prove the remaining obligations. Establish `e : a • x - algebraMap A.W A.Acr0 (a * w) * A.dxi0 r = algebraMap A.W A.Acr0 a * (x - algebraMap A.W A.Acr0 w * A.dxi0 r)`. Rewrite using `[Algebra.smul_def, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ h`.
-/
theorem filtration_element_mod_next_level (r : ℕ) {z : A.Acr0} (hz : z ∈ A.Fil0 r) :
    ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) := by
  rw [mem_crystalline_filtration_iff_span] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rcases hk.eq_or_lt with h | h
    · subst h
      exact ⟨1, by simp⟩
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_mul, sub_zero]
      exact (mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨k, Nat.succ_le_of_lt h, rfl⟩)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w1, h1⟩ := hx
    obtain ⟨w2, h2⟩ := hy
    refine ⟨w1 + w2, ?_⟩
    have e : x + y - algebraMap A.W A.Acr0 (w1 + w2) * A.dxi0 r =
        (x - algebraMap A.W A.Acr0 w1 * A.dxi0 r) + (y - algebraMap A.W A.Acr0 w2 * A.dxi0 r) := by
      rw [map_add]; ring
    rw [e]
    exact Ideal.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨w, h⟩ := hx
    refine ⟨a * w, ?_⟩
    have e : a • x - algebraMap A.W A.Acr0 (a * w) * A.dxi0 r =
        algebraMap A.W A.Acr0 a * (x - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ h

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap A.W A.Acr0)`. Introduce `x y h`. Apply `A.algebraMap_WL_injective` to reduce the goal to its premises. Conclude with `congrArg Subtype.val h`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨N, v, hv⟩` from `filtration_element_power_multiple_xi A (r + 1) h`. Establish `hr` using `factorial_mul_divided_power_xi A r`. Establish `e1 : algebraMap A.W A.Acr0 ((l : A.W) ^ N * w * A.xi ^ r) = algebraMap A.W A.Acr0 (A.xi * ((r.factorial : A.W) * v) * A.xi ^ r)`. Establish `e2` using `congrArg (fun t => (r.factorial : A.Acr0) * t) hv`.

Simplify using `only [map_mul, map_pow, map_natCast] at e2 ⊢`. Take the linear combination `e2 - (l : A.Acr0) ^ N * algebraMap A.W A.Acr0 w * hr`. Establish `e3 : (l : A.W) ^ N * w = A.xi * ((r.factorial : A.W) * v)` using `(mul_cancel_right_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.1 r)).1 (hinj e1)`. Establish `e4 : (r.factorial : A.W) * v ∈ Ideal.span {(l : A.W) ^ N}`. Apply `(GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.2 N` to reduce the goal to its premises.

Rewrite using `[← e3]`. Conclude with `Ideal.mem_span_singleton.2 ⟨w, rfl⟩`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton.1 e4`. Rewrite `e3` using `[hy]`. Establish `e5 : w = A.xi * y`.

Apply `(mul_cancel_left_mem_nonZeroDivisors (pow_mem A.l_mem_nzd N)).1` to reduce the goal to its premises. Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Ideal.mem_span_singleton.2 ⟨y, e5⟩`. Introduce `h`.

Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton.1 h`. Establish `h2` using `xi_mul_divided_power A r`. Establish `e : algebraMap A.W A.Acr0 (A.xi * y) * A.dxi0 r = algebraMap A.W A.Acr0 y * (((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1))`. Rewrite using `[← h2, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ((mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨r + 1, le_rfl, rfl⟩)))`.
-/
theorem divided_power_multiple_next_level_iff (r : ℕ) (w : A.W) :
    algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi} := by
  have hinj : Function.Injective (algebraMap A.W A.Acr0) := by
    intro x y h
    apply A.algebraMap_WL_injective
    exact congrArg Subtype.val h
  constructor
  · intro h
    obtain ⟨N, v, hv⟩ := filtration_element_power_multiple_xi A (r + 1) h
    have hr := factorial_mul_divided_power_xi A r
    have e1 : algebraMap A.W A.Acr0 ((l : A.W) ^ N * w * A.xi ^ r) =
        algebraMap A.W A.Acr0 (A.xi * ((r.factorial : A.W) * v) * A.xi ^ r) := by
      have e2 := congrArg (fun t => (r.factorial : A.Acr0) * t) hv
      simp only [map_mul, map_pow, map_natCast] at e2 ⊢
      linear_combination e2 - (l : A.Acr0) ^ N * algebraMap A.W A.Acr0 w * hr
    have e3 : (l : A.W) ^ N * w = A.xi * ((r.factorial : A.W) * v) :=
      (mul_cancel_right_mem_nonZeroDivisors (pow_mem (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.1 r)).1 (hinj e1)
    have e4 : (r.factorial : A.W) * v ∈ Ideal.span {(l : A.W) ^ N} := by
      apply (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).2.2 N
      rw [← e3]
      exact Ideal.mem_span_singleton.2 ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 e4
    rw [hy] at e3
    have e5 : w = A.xi * y := by
      apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem A.l_mem_nzd N)).1
      rw [e3]
      ring
    exact Ideal.mem_span_singleton.2 ⟨y, e5⟩
  · intro h
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 h
    have h2 := xi_mul_divided_power A r
    have e : algebraMap A.W A.Acr0 (A.xi * y) * A.dxi0 r =
        algebraMap A.W A.Acr0 y * (((r + 1 : ℕ) : A.Acr0) * A.dxi0 (r + 1)) := by
      rw [← h2, map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
      ((mem_crystalline_filtration_iff_span A (r + 1) _).2 (Submodule.subset_span ⟨r + 1, le_rfl, rfl⟩)))

/- English proof (translation)
Introduce `l hl A r`. Conclude with `⟨fun z hz => filtration_element_mod_next_level A r hz, fun w => divided_power_multiple_next_level_iff A r w, fun z hz => filtration_element_power_multiple_xi A r hz⟩`.
-/
theorem crystalline_filtration_graded_pieces : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ),
    (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧
    (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧
    ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W),
      (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  intro l hl A r
  exact ⟨fun z hz => filtration_element_mod_next_level A r hz, fun w => divided_power_multiple_next_level_iff A r w,
    fun z hz => filtration_element_power_multiple_xi A r hz⟩

end GlobalTheory.CompanionTheory.PerfFil
