import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Conv

section General

variable {A : Type*} [CommRing A]

/- English proof (translation)
Rewrite using `[pow_succ']`. Use `Ideal.mul_mem_mul hc ?_` and prove the remaining obligations. Establish `h : φ y ∈ (I ^ n).map φ` using `Ideal.mem_map_of_mem φ hy`. Rewrite `h` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hφ n h`.
-/
theorem step_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A} (hc : c ∈ I) (n : ℕ)
    {y : A} (hy : y ∈ I ^ n) : c * φ y ∈ I ^ (n + 1) := by
  rw [pow_succ']
  refine Ideal.mul_mem_mul hc ?_
  have h : φ y ∈ (I ^ n).map φ := Ideal.mem_map_of_mem φ hy
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hφ n h

/- English proof (translation)
Set `f : ℕ → A` to `fun n => (fun z => q + c * φ z)^[n] 0`. Establish `hf : ∀ n, f (n + 1) = q + c * φ (f n)` using `fun n => Function.iterate_succ_apply' _ _ _`. Establish `h1 : ∀ n, f n - f (n + 1) ∈ I ^ n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Use `step_mem I φ hφ hc n ih` as an intermediate fact. Rewrite using `[hf (n + 1)]`. Use `nth_rewrite 1 [hf n]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m`. Introduce `m n hmn`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.

Take `⟨L, hL⟩` from `hI.toIsPrecomplete.prec' f (by`. Introduce `m n hmn`. Simplify using `only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]`. Conclude with `h2 m n hmn)`. Simplify using `only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL`.

Use `⟨L, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `hI.toIsHausdorff.haus' _ fun n => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul, Ideal.mul_top, SModEq.zero]`. Use `Ideal.pow_le_pow_right (Nat.le_succ n) ?_` and prove the remaining obligations.

Use `sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hf, map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem solve (I : Ideal A) [hI : IsAdicComplete I A] (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A}
    (hc : c ∈ I) (q : A) : ∃ y, y - c * φ y = q := by
  let f : ℕ → A := fun n => (fun z => q + c * φ z)^[n] 0
  have hf : ∀ n, f (n + 1) = q + c * φ (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, f n - f (n + 1) ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step_mem I φ hφ hc n ih
      rw [hf (n + 1)]
      nth_rewrite 1 [hf n]
      convert this using 1
      rw [map_sub]; ring
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' f (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact h2 m n hmn)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine hI.toIsHausdorff.haus' _ fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have := sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))
  convert this using 1
  rw [hf, map_sub]; ring

/- English proof (translation)
Establish `h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1)`. Rewrite using `[Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Use `add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)` and prove the remaining obligations.

Take `⟨d, hd⟩ : e - 1 ∣ e ^ i - 1` from `by simpa using sub_dvd_pow_sub_pow e 1 i`. Rewrite using `[hd]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))`.
-/
theorem geom_mem (p : ℕ) (e : A) :
    ∑ i ∈ Finset.range p, e ^ i ∈ Ideal.span {(p : A), e - 1} := by
  have h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h]
  refine add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)
  obtain ⟨d, hd⟩ : e - 1 ∣ e ^ i - 1 := by simpa using sub_dvd_pow_sub_pow e 1 i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/- English proof (translation)
Rewrite using `[Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨x, rfl | rfl, rfl⟩`. Rewrite using `[map_natCast]; exact Ideal.subset_span (by simp)`. Rewrite using `[h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`.
-/
theorem map_le (p : ℕ) (φ : A →+* A) {m c : A} (h : φ m = c * m) :
    (Ideal.span {(p : A), m}).map φ ≤ Ideal.span {(p : A), m} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · rw [map_natCast]; exact Ideal.subset_span (by simp)
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, by simp, by simp⟩`. Consider the case `succ k ih`. Take `⟨d, hd, e⟩` from `ih`. Use `⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[Function.iterate_succ_apply', e, map_mul, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iterate_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {m c : A} (hc : c ∈ I)
    (h : φ m = c * m) (k : ℕ) : ∃ d ∈ I ^ k, φ^[k] m = d * m := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, e⟩ := ih
    refine ⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩
    rw [Function.iterate_succ_apply', e, map_mul, h]; ring

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

/- English proof (translation)
Establish `h : WittVector.frobenius (WittVector.teichmuller l AI.ε) = WittVector.teichmuller l AI.ε ^ l`. Rewrite using `[WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]`. Rewrite using `[LocAinf.μ, map_sub, map_one, h, geom_sum_mul]`.
-/
theorem frob_mu : WittVector.frobenius AI.μ =
    (∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i) * AI.μ := by
  have h : WittVector.frobenius (WittVector.teichmuller l AI.ε) =
      WittVector.teichmuller l AI.ε ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [LocAinf.μ, map_sub, map_one, h, geom_sum_mul]

/- English proof (translation)
Introduce `h`. Take `⟨θ, hθ⟩` from `exists_isTheta l P AI`. Establish `h0 : θ AI.μ = 0` using `(hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩`. Use `h.map θ` as an intermediate fact. Rewrite `this` using `[h0]`.

Conclude with `not_isUnit_zero this`.
-/
theorem mu_not_isUnit : ¬ IsUnit AI.μ := by
  intro h
  obtain ⟨θ, hθ⟩ := exists_isTheta l P AI
  have h0 : θ AI.μ = 0 := (hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := h.map θ
  rw [h0] at this
  exact not_isUnit_zero this

/- English proof (translation)
Introduce `l _ P AI`. Establish `hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈ Ideal.span {((l : ℕ) : Ainf l), AI.μ}` using `geom_mem l _`. Establish `hφ` using `map_le l _ (frob_mu AI)`. Use `⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩` and prove the remaining obligations. Use `haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1`.

Take `⟨y, hy⟩` from `solve _ _ hφ hc q`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, frob_mu, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨d, hd, e⟩` from `iterate_mem _ _ hφ hc (frob_mu AI) k`.

Rewrite using `[e]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Establish `h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ}`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `x (rfl | rfl)`.

Conclude with `Ideal.subset_span (by simp)`. Rewrite using `[AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Establish `h2` using `Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)`. Rewrite `h2` using `[Ideal.span_insert]`. Rewrite using `[Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]`.

Conclude with `Ideal.sup_pow_add_le_pow_sup_pow h2`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  intro l _ P AI
  have hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈
      Ideal.span {((l : ℕ) : Ainf l), AI.μ} := geom_mem l _
  have hφ := map_le l _ (frob_mu AI)
  refine ⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩
  · haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1
    obtain ⟨y, hy⟩ := solve _ _ hφ hc q
    refine ⟨y, ?_⟩
    rw [map_mul, frob_mu, ← hy]; ring
  · obtain ⟨d, hd, e⟩ := iterate_mem _ _ hφ hc (frob_mu AI) k
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have h2 := Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)
    rw [Ideal.span_insert] at h2
    rw [Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow h2

end GlobalTheory.ExpImage.Conv
