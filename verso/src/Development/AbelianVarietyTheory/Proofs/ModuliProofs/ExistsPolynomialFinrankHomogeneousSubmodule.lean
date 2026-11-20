import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates

namespace GlobalTheory

/- English proof (translation)
Use `Fintype.ofFinite σ` as an intermediate fact. Establish `h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0`. Rewrite using `[_root_.GlobalTheory.natCard_degree_eq]`. Use `Fintype.card_pos (α := σ)` as an intermediate fact. Conclude with `(Nat.choose_pos (by omega)).ne'`.

Conclude with `Nat.finite_of_card_ne_zero h`.
-/
private lemma finite_setOf_finsupp_degree_eq (σ : Type) [Finite σ] [Nonempty σ] (e : ℕ) :
    Finite ↑{d : σ →₀ ℕ | d.degree = e} := by
  have := Fintype.ofFinite σ
  have h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0 := by
    rw [_root_.GlobalTheory.natCard_degree_eq]
    have := Fintype.card_pos (α := σ)
    exact (Nat.choose_pos (by omega)).ne'
  exact Nat.finite_of_card_ne_zero h

/- English proof (translation)
Use `finite_setOf_finsupp_degree_eq σ e` as an intermediate fact. Use `Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}` as an intermediate fact. Rewrite using `[MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) {d : σ →₀ ℕ | d.degree = e}).finrank_eq, ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression.
-/
private lemma finrank_homogeneousSubmodule_eq_choose (σ : Type) [Fintype σ] [Nonempty σ] (K : Type)
    [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K e) =
      (e + Fintype.card σ - 1).choose e := by
  have := finite_setOf_finsupp_degree_eq σ e
  have := Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = e}).finrank_eq,
    ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  rfl

/- English proof (translation)
Rewrite using `[Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]`. Establish `h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ)` using `by push_cast; ring`. Rewrite using `[h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]`. Establish `: ((m - 1).factorial : ℚ) ≠ 0` using `by positivity`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma cast_choose_eq_eval_descPochhammer (m e : ℕ) (hm : 1 ≤ m) :
    (((e + m - 1).choose e : ℕ) : ℚ) = (Polynomial.C (1 / ((m - 1).factorial : ℚ)) *
      (descPochhammer ℚ (m - 1)).comp (Polynomial.X + Polynomial.C ((m - 1 : ℕ) : ℚ))).eval
        (e : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ) := by push_cast; ring
  rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]
  have : ((m - 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/- English proof (translation)
Introduce `σ _ _`. Use `Fintype.ofFinite σ` as an intermediate fact. Use `⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) * (descPochhammer ℚ (Fintype.card σ - 1)).comp (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩` and prove the remaining obligations. Rewrite using `[finrank_homogeneousSubmodule_eq_choose σ K e]`. Conclude with `cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos`.
-/
theorem _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule :
    ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ),
      ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) =
        Q.eval (e : ℚ) := by
  intro σ _ _
  have := Fintype.ofFinite σ
  refine ⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) *
    (descPochhammer ℚ (Fintype.card σ - 1)).comp
      (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩
  rw [finrank_homogeneousSubmodule_eq_choose σ K e]
  exact cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos

end GlobalTheory
