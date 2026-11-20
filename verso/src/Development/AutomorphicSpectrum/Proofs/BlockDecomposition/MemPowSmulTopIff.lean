import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinementStatement

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Completion

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`.
-/
theorem mem_pow_smul_top_iff {T : Type} [CommRing T] (t y : T) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule T T) ↔ y ∈ Ideal.span {t ^ n} := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

/- English proof (translation)
Introduce `B _ T _ π g hc hπ hA hV P hP hd`. Establish `step` using `GlobalTheory.T.hensel_polynomial_refinement B T π g hc hπ hA hV P hP hd`. Use `set d := P.natDegree with hdd`. Use `set t := g π with ht`. Set `S : ℕ → Type` to `fun M => {a : B // P.eval (g a) ∈ Ideal.span {t ^ (d * M)}}`.

Establish `s0 : P.eval (g 0) ∈ Ideal.span {t ^ (d * 0)}` using `by simp`. Set `seq : (M : ℕ) → S M` to `fun M => Nat.rec (motive := S) ⟨0, s0⟩ (fun M a => ⟨(step M a.1 a.2).choose, (step M a.1 a.2).choose_spec.2⟩) M`. Establish `hstep : ∀ M, (seq (M + 1)).1 - (seq M).1 ∈ Ideal.span {π ^ M}` using `fun M => (step M (seq M).1 (seq M).2).choose_spec.1`. Set `a : ℕ → T` to `fun M => g (seq M).1`. Establish `hg : ∀ M, a (M + 1) - a M ∈ Ideal.span {t ^ M}`.

Introduce `M`. Take `⟨c, hc'⟩` from `Ideal.mem_span_singleton'.1 (hstep M)`. Use `Ideal.mem_span_singleton'.2 ⟨g c, ?_⟩` and prove the remaining obligations. Simplify using `only [a, ht, ← map_pow, ← map_mul, hc', map_sub]`. Establish `hpow : ∀ {m n : ℕ}, m ≤ n → Ideal.span {t ^ n} ≤ Ideal.span {t ^ m}`.

Introduce `m n hmn`. Rewrite using `[Ideal.span_singleton_le_span_singleton]`. Conclude with `pow_dvd_pow t hmn`. Establish `hcau : ∀ {m n : ℕ}, m ≤ n → a n - a m ∈ Ideal.span {t ^ m}`. Introduce `m n hmn`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `Ideal.add_mem _ ih (hpow hmn (hg n))` as an intermediate fact. Simplify using `using this`.

Establish `hpre` using `hc.compl.toIsPrecomplete`. Take `⟨x, hx⟩` from `hpre.prec' a (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, mem_pow_smul_top_iff]`. Use `Ideal.neg_mem_iff _ |>.2 (hcau hmn)` as an intermediate fact. Simplify using `using this)`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hz : ∀ n, P.eval x ∈ Ideal.span {t ^ n}`. Introduce `n`. Establish `h1 : a n - x ∈ Ideal.span {t ^ n}`. Use `hx n` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, mem_pow_smul_top_iff]`. Then use the resulting hypothesis. Establish `h2 : P.eval (a n) ∈ Ideal.span {t ^ n}` using `hpow (Nat.le_mul_of_pos_left n hd) (seq n).2`. Establish `h3 : a n - x ∣ P.eval (a n) - P.eval x` using `Polynomial.sub_dvd_eval_sub _ _ _`. Establish `h4 : P.eval (a n) - P.eval x ∈ Ideal.span {t ^ n}` using `Ideal.mem_of_dvd _ h3 h1`. Use `Ideal.sub_mem _ h2 h4` as an intermediate fact.

Simplify using `using this`. Use `hc.compl.toIsHausdorff.haus' (P.eval x) (fun n => by` as an intermediate fact. Rewrite using `[SModEq.zero, mem_pow_smul_top_iff]`. Conclude with `hz n)`. Conclude with `this`.
-/
theorem aic_of_isCompl : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := by
  intro B _ T _ π g hc hπ hA hV P hP hd
  have step := GlobalTheory.T.hensel_polynomial_refinement B T π g hc hπ hA hV P hP hd
  set d := P.natDegree with hdd
  set t := g π with ht

  let S : ℕ → Type := fun M => {a : B // P.eval (g a) ∈ Ideal.span {t ^ (d * M)}}
  have s0 : P.eval (g 0) ∈ Ideal.span {t ^ (d * 0)} := by simp
  let seq : (M : ℕ) → S M := fun M =>
    Nat.rec (motive := S) ⟨0, s0⟩ (fun M a => ⟨(step M a.1 a.2).choose, (step M a.1 a.2).choose_spec.2⟩) M
  have hstep : ∀ M, (seq (M + 1)).1 - (seq M).1 ∈ Ideal.span {π ^ M} := fun M =>
    (step M (seq M).1 (seq M).2).choose_spec.1
  let a : ℕ → T := fun M => g (seq M).1
  have hg : ∀ M, a (M + 1) - a M ∈ Ideal.span {t ^ M} := by
    intro M
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (hstep M)
    refine Ideal.mem_span_singleton'.2 ⟨g c, ?_⟩
    simp only [a, ht, ← map_pow, ← map_mul, hc', map_sub]
  have hpow : ∀ {m n : ℕ}, m ≤ n → Ideal.span {t ^ n} ≤ Ideal.span {t ^ m} := by
    intro m n hmn
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow t hmn
  have hcau : ∀ {m n : ℕ}, m ≤ n → a n - a m ∈ Ideal.span {t ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := Ideal.add_mem _ ih (hpow hmn (hg n))
      simpa using this
  have hpre := hc.compl.toIsPrecomplete
  obtain ⟨x, hx⟩ := hpre.prec' a (fun {m n} hmn => by
    rw [SModEq.sub_mem, mem_pow_smul_top_iff]
    have := Ideal.neg_mem_iff _ |>.2 (hcau hmn)
    simpa using this)
  refine ⟨x, ?_⟩
  have hz : ∀ n, P.eval x ∈ Ideal.span {t ^ n} := by
    intro n
    have h1 : a n - x ∈ Ideal.span {t ^ n} := by
      have := hx n
      rwa [SModEq.sub_mem, mem_pow_smul_top_iff] at this
    have h2 : P.eval (a n) ∈ Ideal.span {t ^ n} :=
      hpow (Nat.le_mul_of_pos_left n hd) (seq n).2
    have h3 : a n - x ∣ P.eval (a n) - P.eval x := Polynomial.sub_dvd_eval_sub _ _ _
    have h4 : P.eval (a n) - P.eval x ∈ Ideal.span {t ^ n} := Ideal.mem_of_dvd _ h3 h1
    have := Ideal.sub_mem _ h2 h4
    simpa using this
  have := hc.compl.toIsHausdorff.haus' (P.eval x) (fun n => by
    rw [SModEq.zero, mem_pow_smul_top_iff]
    exact hz n)
  exact this

end GlobalTheory.CompanionTheory.Completion
