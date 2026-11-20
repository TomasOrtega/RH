import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockNormBound

/- English proof (translation)
Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Rewrite using `[inner_sum, Finset.sum_eq_single a, inner_self_eq_norm_sq]`. Introduce `b _ hb`. Conclude with `h a b (Ne.symm hb)`.

Introduce `h'`. Conclude with `absurd ha h'`.
-/
theorem norm_sum_sq_of_orth {κ H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset κ) (v : κ → H) (h : ∀ a b, a ≠ b → inner ℂ (v a) (v b) = 0) :
    ‖∑ a ∈ s, v a‖ ^ 2 = ∑ a ∈ s, ‖v a‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [inner_sum, Finset.sum_eq_single a, inner_self_eq_norm_sq]
  · intro b _ hb; exact h a b (Ne.symm hb)
  · intro h'; exact absurd ha h'

def mfact {σ : Type} (α : σ →₀ ℕ) : ℝ := α.prod (fun _ k => (k.factorial : ℝ))

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => by positivity`.
-/
theorem mfact_nonneg {σ : Type} (α : σ →₀ ℕ) : 0 ≤ mfact α :=
  Finset.prod_nonneg fun _ _ => by positivity

/- English proof (translation)
Unfold `mfact`. Rewrite using `[← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i _ (by simp), ← Finsupp.mul_prod_erase' α i _ (by simp)]`. Establish `: Finsupp.erase i (α + Finsupp.single i 1) = Finsupp.erase i α`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`.

Simplify using `[hj]`. Simplify using `[Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]`. Rewrite using `[this]`. Simplify using `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mfact_add {σ : Type} [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    mfact (α + Finsupp.single i 1) = ((α i : ℝ) + 1) * mfact α := by
  unfold mfact
  rw [← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i _ (by simp),
    ← Finsupp.mul_prod_erase' α i _ (by simp)]
  have : Finsupp.erase i (α + Finsupp.single i 1) = Finsupp.erase i α := by
    ext j; by_cases hj : j = i
    · simp [hj]
    · simp [Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]
  rw [this]
  simp [Nat.factorial_succ]
  ring

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

/- English proof (translation)
Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), h α α, if_pos rfl]`. Establish `: α.prod (fun _ k => (k.factorial : ℂ)) = ((mfact α : ℝ) : ℂ)`. Simplify using `[mfact, Finsupp.prod]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem norm_mono (h : IsFockIP ι) (α : σ →₀ ℕ) : ‖ι (monomial α 1)‖ ^ 2 = mfact α := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h α α, if_pos rfl]
  have : α.prod (fun _ k => (k.factorial : ℂ)) = ((mfact α : ℝ) : ℂ) := by
    simp [mfact, Finsupp.prod]
  rw [this]; simp

/- English proof (translation)
Establish `e : ∀ a, ι (monomial (g a) (c a)) = c a • ι (monomial (g a) 1)`. Introduce `a`. Rewrite using `[← map_smul, smul_monomial]`. Simplify using the standard rewrite rules. Rewrite using `[map_sum, norm_sum_sq_of_orth]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[e, norm_smul, mul_pow, norm_mono h]`. Introduce `a b hab`. Rewrite using `[e, e]`. Distinguish the cases in `ha : c a = 0`.

Simplify using `[ha]`. Distinguish the cases in `hb : c b = 0`. Simplify using `[hb]`. Rewrite using `[inner_smul_left, inner_smul_right, h, if_neg (hg a b hab ha hb)]`. Simplify using the standard rewrite rules.
-/
theorem norm_comb (h : IsFockIP ι) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℂ)
    (g : (σ →₀ ℕ) → (σ →₀ ℕ)) (hg : ∀ a b, a ≠ b → c a ≠ 0 → c b ≠ 0 → g a ≠ g b) :
    ‖ι (∑ a ∈ s, monomial (g a) (c a))‖ ^ 2 = ∑ a ∈ s, ‖c a‖ ^ 2 * mfact (g a) := by
  have e : ∀ a, ι (monomial (g a) (c a)) = c a • ι (monomial (g a) 1) := by
    intro a; rw [← map_smul, smul_monomial]; simp
  rw [map_sum, norm_sum_sq_of_orth]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [e, norm_smul, mul_pow, norm_mono h]
  · intro a b hab
    rw [e, e]
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    rw [inner_smul_left, inner_smul_right, h, if_neg (hg a b hab ha hb)]; simp

/- English proof (translation)
Establish `hd : ∀ a ∈ P.support, (a i : ℝ) ≤ d`. Introduce `a ha`. Establish `h1 : a i ≤ P.degreeOf i` using `monomial_le_degreeOf i ha`. Conclude with `h1.trans ((degreeOf_le_totalDegree P i).trans hP)` after adjusting the coercions. Establish `h0 : ‖ι P‖ ^ 2 = ∑ a ∈ P.support, ‖coeff a P‖ ^ 2 * mfact a` using `by conv_lhs => rw [P.as_sum]`.

Conclude with `norm_comb h _ _ id (fun a b hab _ _ => hab)`. Establish `h1 : X i * P = ∑ a ∈ P.support, monomial (a + Finsupp.single i 1) (coeff a P)` using `by conv_lhs => rw [P.as_sum]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[X, monomial_mul, add_comm, one_mul]`.

Establish `h2 : pderiv i P = ∑ a ∈ P.support, monomial (a - Finsupp.single i 1) (coeff a P * a i)` using `by conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_monomial]`. Establish `hsub : ∀ a : σ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a`.

Introduce `a ha`. Conclude with `tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha))`. Prove the components needed by the constructor for the conclusion. Rewrite using `[h1, norm_comb h _ _ _ (fun a b hab _ _ hh => hab (add_right_cancel hh)), h0, Finset.mul_sum]`. Use `Finset.sum_le_sum fun a ha => ?_` and prove the remaining obligations.

Rewrite using `[mfact_add]`. Use `hd a ha` as an intermediate fact. Establish `h3 : 0 ≤ ‖coeff a P‖ ^ 2 * mfact a` using `mul_nonneg (by positivity) (mfact_nonneg a)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[h2, norm_comb h, h0, Finset.mul_sum]`.

Use `Finset.sum_le_sum fun a ha => ?_` and prove the remaining obligations. Establish `h3 : 0 ≤ ‖coeff a P‖ ^ 2 * mfact a` using `mul_nonneg (by positivity) (mfact_nonneg a)`. Distinguish the cases in `hz : a i = 0`. Simplify using `only [hz, Nat.cast_zero, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]`. Conclude with `mul_nonneg (by positivity) h3`.

Establish `h4` using `mfact_add (a - Finsupp.single i 1) i`. Rewrite `h4` using `[hsub a hz]`. Establish `h5 : (((a - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℝ) + 1 = a i`. Use `congrArg (fun f : σ →₀ ℕ => f i) (hsub a hz)` as an intermediate fact. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same] at this`.

Conclude with `this` after adjusting the coercions. Rewrite `h4` using `[h5]`. Rewrite using `[norm_mul, Complex.norm_natCast]`. Combine the equalities or inequalities in the displayed calculation. Introduce `a b hab ha hb hh`.

Establish `ha' : a i ≠ 0` using `fun z => ha (by simp [z])`. Establish `hb' : b i ≠ 0` using `fun z => hb (by simp [z])`. Apply `hab` to reduce the goal to its premises. Rewrite using `[← hsub a ha', hh, hsub b hb']`.
-/
theorem fock_norm_bounds (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (h : IsFockIP ι) (i : σ) (d : ℕ)
    (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧
      ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  have hd : ∀ a ∈ P.support, (a i : ℝ) ≤ d := by
    intro a ha
    have h1 : a i ≤ P.degreeOf i := monomial_le_degreeOf i ha
    exact_mod_cast h1.trans ((degreeOf_le_totalDegree P i).trans hP)
  have h0 : ‖ι P‖ ^ 2 = ∑ a ∈ P.support, ‖coeff a P‖ ^ 2 * mfact a := by
    conv_lhs => rw [P.as_sum]
    exact norm_comb h _ _ id (fun a b hab _ _ => hab)
  have h1 : X i * P = ∑ a ∈ P.support, monomial (a + Finsupp.single i 1) (coeff a P) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X, monomial_mul, add_comm, one_mul]
  have h2 : pderiv i P = ∑ a ∈ P.support, monomial (a - Finsupp.single i 1) (coeff a P * a i) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_monomial]
  have hsub : ∀ a : σ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a := by
    intro a ha
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha))
  constructor
  · rw [h1, norm_comb h _ _ _ (fun a b hab _ _ hh => hab (add_right_cancel hh)), h0,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [mfact_add]
    have := hd a ha
    have h3 : 0 ≤ ‖coeff a P‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
    nlinarith
  · rw [h2, norm_comb h, h0, Finset.mul_sum]
    · refine Finset.sum_le_sum fun a ha => ?_
      have h3 : 0 ≤ ‖coeff a P‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
      by_cases hz : a i = 0
      · simp only [hz, Nat.cast_zero, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (by positivity) h3
      have h4 := mfact_add (a - Finsupp.single i 1) i
      rw [hsub a hz] at h4
      have h5 : (((a - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℝ) + 1 = a i := by
        have := congrArg (fun f : σ →₀ ℕ => f i) (hsub a hz)
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        exact_mod_cast this
      rw [h5] at h4
      rw [norm_mul, Complex.norm_natCast]
      calc (‖coeff a P‖ * a i) ^ 2 * mfact (a - Finsupp.single i 1)
          = a i * (‖coeff a P‖ ^ 2 * mfact a) := by rw [h4]; ring
        _ ≤ d * (‖coeff a P‖ ^ 2 * mfact a) := mul_le_mul_of_nonneg_right (hd a ha) h3
    · intro a b hab ha hb hh
      have ha' : a i ≠ 0 := fun z => ha (by simp [z])
      have hb' : b i ≠ 0 := fun z => hb (by simp [z])
      apply hab
      rw [← hsub a ha', hh, hsub b hb']

end GlobalTheory.FockNormBound
