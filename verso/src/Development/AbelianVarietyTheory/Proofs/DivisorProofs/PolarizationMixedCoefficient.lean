import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.DetCoef

/- English proof (translation)
Establish `h` using `(Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.map_add_univ (t • N) Θ`. Rewrite using `[add_comm Θ]`. Use `h.trans (Finset.sum_congr rfl fun S _ => ?_)` and prove the remaining obligations. Establish `h2` using `(Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.map_piecewise_smul (fun _ => t) (S.piecewise N Θ) S`. Rewrite `h2` using `[Finset.prod_const, smul_eq_mul]`.

Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i ∈ S`. Simplify using `[Finset.piecewise, hi]`.

Both sides reduce to the same expression. Simplify using `[Finset.piecewise, hi]`.
-/
theorem det_add_smul_eq_sum {n : Type} [Fintype n] [DecidableEq n] (Θ N : Matrix n n ℂ) (t : ℂ) :
    (Θ + t • N).det = ∑ S : Finset n, t ^ S.card * Matrix.det (Matrix.of (S.piecewise N Θ)) := by
  have h := (Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.map_add_univ (t • N) Θ
  rw [add_comm Θ]
  refine h.trans (Finset.sum_congr rfl fun S _ => ?_)
  have h2 := (Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.map_piecewise_smul
    (fun _ => t) (S.piecewise N Θ) S
  rw [Finset.prod_const, smul_eq_mul] at h2
  refine Eq.trans ?_ h2
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [Finset.piecewise, hi]; rfl
  · simp [Finset.piecewise, hi]

/- English proof (translation)
Rewrite using `[Matrix.trace_mul_comm, Matrix.trace]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem trace_adjugate_mul {n : Type} [Fintype n] [DecidableEq n] (Θ N : Matrix n n ℂ) :
    (N.adjugate * Θ).trace = ∑ k, (N.updateRow k (Θ k)).det := by
  rw [Matrix.trace_mul_comm, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Use `symm`. Use `Finset.sum_bij (fun k _ => Finset.univ.erase k) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `k _`. Simplify using `[Finset.card_erase_of_mem]`.

Introduce `a _ b _ h`. Assume the negation of the conclusion as `hab`. Establish `: a ∈ Finset.univ.erase b` using `by simp [hab]`. Rewrite `this` using `[← h]`. Simplify using `at this`.

Introduce `S hS`. Establish `hS' : S.card = e` using `by simpa using hS`. Establish `h1 : Sᶜ.card = 1` using `by rw [Finset.card_compl, hS']; simp`. Take `⟨k, hk⟩` from `Finset.card_eq_one.1 h1`. Use `⟨k, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[← compl_compl S, hk, Finset.compl_singleton]`. Introduce `_ _`. Both sides reduce to the same expression.
-/
theorem sum_card_eq {e : ℕ} {M : Type} [AddCommMonoid M] (d : Finset (Fin (e + 1)) → M) :
    ∑ S : Finset (Fin (e + 1)), (if S.card = e then d S else 0) = ∑ k, d (Finset.univ.erase k) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun k _ => Finset.univ.erase k) ?_ ?_ ?_ ?_
  · intro k _
    simp [Finset.card_erase_of_mem]
  · intro a _ b _ h
    by_contra hab
    have : a ∈ Finset.univ.erase b := by simp [hab]
    rw [← h] at this
    simp at this
  · intro S hS
    have hS' : S.card = e := by simpa using hS
    have h1 : Sᶜ.card = 1 := by rw [Finset.card_compl, hS']; simp
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 h1
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [← compl_compl S, hk, Finset.compl_singleton]
  · intro _ _; rfl

/- English proof (translation)
Introduce `R _ _ Λ a b f e Θ N s h`. Set `c : ℕ → ℝ` to `fun m => ((f + e).choose m : ℝ) * Λ (a ^ (f + e - m) * b ^ m)`. Set `d : Finset (Fin (e + 1)) → ℝ` to `fun S => s * (Matrix.det (Matrix.of (S.piecewise N Θ))).re`. Establish `hP : (∑ m ∈ Finset.range (f + e + 1), Polynomial.monomial m (c m)) = ∑ S : Finset (Fin (e + 1)), Polynomial.monomial S.card (d S)`. Apply `Polynomial.funext` to reduce the goal to its premises.

Introduce `t`. Establish `ht` using `h t`. Rewrite `ht` using `[det_add_smul_eq_sum, add_comm a, add_pow, map_sum, Complex.re_sum, Finset.mul_sum]`. Simplify using `only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]`. Use `Eq.trans ?_ (ht.trans ?_)` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `: (t • b) ^ m * a ^ (f + e - m) * ((f + e).choose m : R) = (((f + e).choose m : ℝ) * t ^ m) • (a ^ (f + e - m) * b ^ m)`. Rewrite using `[smul_pow, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, smul_mul_assoc, mul_comm (b ^ m), mul_comm]`. Rewrite using `[this, map_smul, smul_eq_mul]`. Simplify using `only [c]`.

Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun S _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Simplify using `only [d]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc` using `congrArg (fun p => Polynomial.coeff p e) hP`. Simplify using `only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial] at hc`. Rewrite `hc` using `[sum_card_eq, Finset.sum_ite_eq' , if_pos (by simp)]`. Simplify using `only [c, Nat.add_sub_cancel] at hc`. Rewrite using `[hc, trace_adjugate_mul, Complex.re_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [d]`. Use `congr 3`. Use extensionality with `i j`. Distinguish the cases in `hi : i = k`.

Substitute `hi` using the available equality. Simplify using `[Finset.piecewise]`. Simplify using `[Finset.piecewise, hi]`.
-/
theorem coeff_compare :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (Λ : R →ₗ[ℝ] ℝ) (a b : R) (f e : ℕ) (Θ N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : ℝ), (∀ t : ℝ, Λ ((a + t • b) ^ (f + e)) = s * (Θ + (t : ℂ) • N).det.re) → ((f + e).choose e : ℝ) * Λ (a ^ f * b ^ e) = s * (N.adjugate * Θ).trace.re := by
  intro R _ _ Λ a b f e Θ N s h
  let c : ℕ → ℝ := fun m => ((f + e).choose m : ℝ) * Λ (a ^ (f + e - m) * b ^ m)
  let d : Finset (Fin (e + 1)) → ℝ := fun S => s * (Matrix.det (Matrix.of (S.piecewise N Θ))).re
  have hP : (∑ m ∈ Finset.range (f + e + 1), Polynomial.monomial m (c m)) =
      ∑ S : Finset (Fin (e + 1)), Polynomial.monomial S.card (d S) := by
    apply Polynomial.funext
    intro t
    have ht := h t
    rw [det_add_smul_eq_sum, add_comm a, add_pow, map_sum, Complex.re_sum, Finset.mul_sum] at ht
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    refine Eq.trans ?_ (ht.trans ?_)
    · refine Finset.sum_congr rfl fun m _ => ?_
      have : (t • b) ^ m * a ^ (f + e - m) * ((f + e).choose m : R) =
          (((f + e).choose m : ℝ) * t ^ m) • (a ^ (f + e - m) * b ^ m) := by
        rw [smul_pow, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, smul_mul_assoc, mul_comm (b ^ m), mul_comm]
      rw [this, map_smul, smul_eq_mul]
      simp only [c]; ring
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
      simp only [d]; ring
  have hc := congrArg (fun p => Polynomial.coeff p e) hP
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial] at hc
  rw [sum_card_eq, Finset.sum_ite_eq' , if_pos (by simp)] at hc
  simp only [c, Nat.add_sub_cancel] at hc
  rw [hc, trace_adjugate_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [d]
  congr 3
  ext i j
  by_cases hi : i = k
  · subst hi; simp [Finset.piecewise]
  · simp [Finset.piecewise, hi]

end GlobalTheory.DetCoef
