import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirElement

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho.NormIneq

variable {n : ℕ}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CasimirElement.main σ`.
-/
theorem casC_eq_sum (σ : Fin n → ℂ) :
    casC σ = ∑ a, σ a ^ 2 + ∑ a, σ a * ((n : ℂ) - 1 - 2 * ((a : ℕ) : ℂ)) :=
  _root_.UpperTheory.Reformulated.B.CasimirElement.main σ

/- English proof (translation)
Simplify using `only [wt, Finsupp.sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [rootAt, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem sum_wt_mul (m : Fin n × Fin n →₀ ℕ) (f : Fin n → ℤ) :
    ∑ k, wt m k * f k = m.sum fun a c => (c : ℤ) * (f a.1 - f a.2) := by
  simp only [wt, Finsupp.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [rootAt, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro i j hij; exact h i j (by simpa using hij)`. Consider the case `succ d ih`. Introduce `i j hij`.

Establish `hk : (i : ℕ) + d + 1 < n` using `by have := j.2; omega`. Establish `h1` using `ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl`. Establish `h2` using `h ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)`. Conclude with `h2.trans h1`.
-/
theorem lt_of_step {f : Fin n → ℤ} (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i) :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = i + d + 1 → f j < f i := by
  intro d
  induction d with
  | zero => intro i j hij; exact h i j (by simpa using hij)
  | succ d ih =>
    intro i j hij
    have hk : (i : ℕ) + d + 1 < n := by have := j.2; omega
    have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
    have h2 := h ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
    exact h2.trans h1

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf⟩ : ∃ f : Fin n → ℤ, ∀ k, f k = 2 * ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) + wt m k` from `⟨_, fun _ => rfl⟩`. Establish `hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i`. Introduce `i j hij`. Take `⟨p, hp⟩` from `hp i j hij`.

Establish `hp0 : (0 : ℤ) ≤ (p : ℤ)` using `by positivity`. Establish `hij' : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1` using `by exact_mod_cast hij`. Rewrite using `[hf, hf, hij']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hneg : ∑ k, wt m k * f k < 0`.

Rewrite using `[sum_wt_mul]`. Use `Finset.sum_neg (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hne)` and prove the remaining obligations. Establish `hlow : (a.2 : ℕ) < a.1` using `hm a ha`. Take `⟨d, hd⟩ : ∃ d : ℕ, (a.1 : ℕ) = a.2 + d + 1` from `⟨(a.1 : ℕ) - a.2 - 1, by omega⟩`. Establish `hlt` using `lt_of_step hstep d a.2 a.1 hd`.

Establish `hpos : (0 : ℤ) < (m a : ℤ)`. Conclude with `Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)` after adjusting the coercions. Conclude with `mul_neg_of_pos_of_neg hpos (by linarith)`. Establish `key : ((∑ k, wt m k * f k : ℤ) : ℂ) = casC (fun k => rhoVec n k + (wt m k : ℂ)) - casC (rhoVec n)`. Rewrite using `[casC_eq_sum, casC_eq_sum, add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hf]`. Use `push_cast`. Simplify using `only [rhoVec]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hc, sub_self]`. Establish `: ∑ k, wt m k * f k = 0` using `by exact_mod_cast key`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_zero_of_casC_eq {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (hm : LowExp m)
    (hp : ∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ))
    (hc : casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n)) : m = 0 := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℤ, ∀ k, f k = 2 * ((n : ℤ) - 1 - 2 * ((k : ℕ) : ℤ)) + wt m k :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ i j : Fin n, (j : ℕ) = i + 1 → f j < f i := by
    intro i j hij
    obtain ⟨p, hp⟩ := hp i j hij
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    have hij' : ((j : ℕ) : ℤ) = ((i : ℕ) : ℤ) + 1 := by exact_mod_cast hij
    rw [hf, hf, hij']
    linarith
  have hneg : ∑ k, wt m k * f k < 0 := by
    rw [sum_wt_mul]
    refine Finset.sum_neg (fun a ha => ?_) (Finsupp.support_nonempty_iff.2 hne)
    have hlow : (a.2 : ℕ) < a.1 := hm a ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (a.1 : ℕ) = a.2 + d + 1 := ⟨(a.1 : ℕ) - a.2 - 1, by omega⟩
    have hlt := lt_of_step hstep d a.2 a.1 hd
    have hpos : (0 : ℤ) < (m a : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 ha)
    exact mul_neg_of_pos_of_neg hpos (by linarith)
  have key : ((∑ k, wt m k * f k : ℤ) : ℂ) =
      casC (fun k => rhoVec n k + (wt m k : ℂ)) - casC (rhoVec n) := by
    rw [casC_eq_sum, casC_eq_sum, add_sub_add_comm, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf]
    push_cast
    simp only [rhoVec]
    ring
  rw [hc, sub_self] at key
  have : ∑ k, wt m k * f k = 0 := by exact_mod_cast key
  omega

end GlobalTheory.CompanionTheory.PresRho.NormIneq
