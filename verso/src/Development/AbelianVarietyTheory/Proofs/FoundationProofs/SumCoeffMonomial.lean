import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowthStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.MinorBound

/- English proof (translation)
Establish `h : Function.Injective (fun s : {s : Fin a → Fin d // StrictMono s} => (Set.range s.1 : Set (Fin d)))`. Introduce `s t hst`. Conclude with `Subtype.ext ((s.2.range_inj t.2).1 hst)`. Use `Fintype.card_le_of_injective _ h` as an intermediate fact. Simplify using `using this`.
-/
theorem card_strictMono_le (a d : ℕ) [Fintype {s : Fin a → Fin d // StrictMono s}] :
    Fintype.card {s : Fin a → Fin d // StrictMono s} ≤ 2 ^ d := by
  have h : Function.Injective
      (fun s : {s : Fin a → Fin d // StrictMono s} => (Set.range s.1 : Set (Fin d))) := by
    intro s t hst
    exact Subtype.ext ((s.2.range_inj t.2).1 hst)
  have := Fintype.card_le_of_injective _ h
  simpa using this

/- English proof (translation)
Set `L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ` to `(MvPolynomial.basisMonomials σ ℂ).constr ℂ w`. Establish `h1 : ∀ α c, L (MvPolynomial.monomial α c) = c * w α`. Introduce `α c`. Establish `: MvPolynomial.monomial α c = c • (MvPolynomial.basisMonomials σ ℂ) α`. Simplify using `[MvPolynomial.smul_monomial]`.

Rewrite using `[this, map_smul, Module.Basis.constr_basis, smul_eq_mul]`. Use `⟨L, h1, fun P => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [P.as_sum, map_sum]`. Simplify using `only [h1]`.
-/
theorem sum_coeff_monomial {σ : Type} (w : (σ →₀ ℕ) → ℂ) :
    ∃ L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, (∀ α c, L (MvPolynomial.monomial α c) = c * w α) ∧
      ∀ P, L P = ∑ α ∈ P.support, MvPolynomial.coeff α P * w α := by
  let L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ w
  have h1 : ∀ α c, L (MvPolynomial.monomial α c) = c * w α := by
    intro α c
    have : MvPolynomial.monomial α c = c • (MvPolynomial.basisMonomials σ ℂ) α := by
      simp [MvPolynomial.smul_monomial]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  refine ⟨L, h1, fun P => ?_⟩
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [h1]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPolynomial.monomial_mul]`.
-/
theorem prod_monomial {σ ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (c : ι → ℂ) :
    ∏ i ∈ s, MvPolynomial.monomial (α i) (c i) =
      MvPolynomial.monomial (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPolynomial.monomial_mul]

noncomputable def expo (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : Mono D a d :=
  ∑ τ, ∑ j, ∑ i, Finsupp.single (τ, (T τ j).1 (p τ j i), i) 1

/- English proof (translation)
Unfold `minorPol`. Establish `hdet : ∀ τ (j : Fin (n τ)), (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det = ∑ σ : Equiv.Perm (Fin a), MvPolynomial.monomial (∑ i, Finsupp.single ((τ, (T τ j).1 (σ i), i) : GL3Theta.Idx D a d) 1) (((Equiv.Perm.sign …`. Introduce `τ j`. Rewrite using `[Matrix.det_apply']`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.of_apply, MvPolynomial.X]`. Rewrite using `[prod_monomial, ← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ), MvPolynomial.C_mul_monomial]`. Simplify using the standard rewrite rules. Simplify using `only [hdet]`. Simplify using `only [Finset.prod_univ_sum, Fintype.piFinset_univ]`.

Use `Finset.sum_congr (by convert rfl) fun p _ => ?_` and prove the remaining obligations. Simplify using `only [prod_monomial, expo]`.
-/
theorem minorPol_eq (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    minorPol D T = ∑ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
      MvPolynomial.monomial (expo D T p) (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)) := by
  unfold minorPol
  have hdet : ∀ τ (j : Fin (n τ)), (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det =
      ∑ σ : Equiv.Perm (Fin a), MvPolynomial.monomial
        (∑ i, Finsupp.single ((τ, (T τ j).1 (σ i), i) : GL3Theta.Idx D a d) 1)
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) := by
    intro τ j
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, MvPolynomial.X]
    rw [prod_monomial, ← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ),
      MvPolynomial.C_mul_monomial]
    simp
  simp only [hdet]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by convert rfl) fun p _ => ?_
  simp only [prod_monomial, expo]

/- English proof (translation)
Take `⟨τ0, r, c⟩` from `k`. Simplify using `only [expo, Finsupp.coe_finset_sum, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_single τ0]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single c]`. Apply the tactic sequence `rw [Finsupp.single_apply]; split_ifs <;> simp`. Introduce `i _ hi`. Rewrite using `[Finsupp.single_apply, if_neg]`. Simplify using `[hi]`.

Simplify using the standard rewrite rules. Use `_ = n τ0 := by simp`. Introduce `τ _ hτ`. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`.

Simplify using `[hτ]`. Simplify using the standard rewrite rules.
-/
theorem expo_le (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) (k : D.what₂.Tau × Fin d × Fin a) :
    expo D T p k ≤ n k.1 := by
  obtain ⟨τ0, r, c⟩ := k
  simp only [expo, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single τ0]
  · calc _ ≤ ∑ _j : Fin (n τ0), 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_eq_single c]
          · rw [Finsupp.single_apply]; split_ifs <;> simp
          · intro i _ hi
            rw [Finsupp.single_apply, if_neg]
            simp [hi]
          · simp
      _ = n τ0 := by simp
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp [hτ]
  · simp

/- English proof (translation)
Establish `: ((expo D T p).sum fun _ m => m) = Finsupp.degree (expo D T p)` using `rfl`. Rewrite using `[this]`. Simplify using `only [expo, map_sum, Finsupp.degree_single]`. Simplify using `[Finset.mul_sum, mul_comm]`.
-/
theorem expo_sum (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) :
    ((expo D T p).sum fun _ m => m) = a * ∑ τ, n τ := by
  have : ((expo D T p).sum fun _ m => m) = Finsupp.degree (expo D T p) := rfl
  rw [this]
  simp only [expo, map_sum, Finsupp.degree_single]
  simp [Finset.mul_sum, mul_comm]

/- English proof (translation)
Introduce `D a d n G S A B hA hB hS hn hG hbd`. Prove the components needed by the constructor for the conclusion. Simplify using `only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[pow_mul, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Finset.prod_le_prod' fun τ _ => Nat.pow_le_pow_left (card_strictMono_le a d) _`.

Introduce `T`. Take `⟨L, hL1, hL2⟩` from `sum_coeff_monomial (fun α : Mono D a d => (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α)`. Establish `h0 : GL3Theta.applyAt0 D (minorPol D T) G = L (minorPol D T)`. Rewrite using `[hL2]`. Simplify using `only [GL3Theta.applyAt0, mul_assoc]`.

Use `set M := S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ) with hM`. Establish `hM0 : 0 ≤ M`. Establish `: (0:ℝ) < B` using `by linarith`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression.

Establish `hterm : ∀ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)), ‖L (MvPolynomial.monomial (expo D T p) (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)))‖ ≤ Real.sqrt M`. Introduce `p`. Rewrite using `[hL1, norm_mul]`. Establish `hs : ‖(∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ))‖ = 1`. Rewrite using `[norm_prod]`.

Use `Finset.prod_eq_one fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_prod]`. Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (p τ j)) with h | h <;> simp [h]`. Rewrite using `[hs, one_mul]`.

Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use `GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth D a d G S A B hA hB hS hG hbd (expo D T p) (fun k => le_trans (by exact_mod_cast expo_le D T p k) (hn k.1))` as an intermediate fact. Rewrite `this` using `[expo_sum]`. Then use the resulting hypothesis. Establish `hcard : (Fintype.card (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : ℝ) = (a.factorial : ℝ) ^ (∑ τ, n τ)`. Simplify using `[Fintype.card_pi, Fintype.card_perm, Finset.prod_pow_eq_pow_sum]`.

Establish `hle : ‖L (minorPol D T)‖ ≤ (a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M`. Rewrite using `[minorPol_eq, map_sum]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum fun p _ => hterm p).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`.

Rewrite using `[h0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem minor_bound : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → (∀ τ, (n τ : ℝ) ≤ 2 * B) → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → (Fintype.card (Tup D a d n) ≤ 2 ^ (d * ∑ τ, n τ)) ∧ ∀ T : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D T) G‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ)) := by
  intro D a d n G S A B hA hB hS hn hG hbd
  constructor
  · simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun τ _ => Nat.pow_le_pow_left (card_strictMono_le a d) _
  · intro T
    obtain ⟨L, hL1, hL2⟩ := sum_coeff_monomial
      (fun α : Mono D a d => (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α)
    have h0 : GL3Theta.applyAt0 D (minorPol D T) G = L (minorPol D T) := by
      rw [hL2]; simp only [GL3Theta.applyAt0, mul_assoc]
    set M := S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ) with hM
    have hM0 : 0 ≤ M := by
      have : (0:ℝ) < B := by linarith
      have := Real.pi_pos
      positivity
    have hterm : ∀ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
        ‖L (MvPolynomial.monomial (expo D T p)
          (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)))‖ ≤ Real.sqrt M := by
      intro p
      rw [hL1, norm_mul]
      have hs : ‖(∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rw [norm_prod]
        refine Finset.prod_eq_one fun τ _ => ?_
        rw [norm_prod]
        refine Finset.prod_eq_one fun j _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign (p τ j)) with h | h <;> simp [h]
      rw [hs, one_mul]
      apply Real.le_sqrt_of_sq_le
      have := GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth D a d G S A B hA hB hS hG hbd (expo D T p) (fun k =>
        le_trans (by exact_mod_cast expo_le D T p k) (hn k.1))
      rwa [expo_sum] at this
    have hcard : (Fintype.card (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : ℝ) =
        (a.factorial : ℝ) ^ (∑ τ, n τ) := by
      simp [Fintype.card_pi, Fintype.card_perm, Finset.prod_pow_eq_pow_sum]
    have hle : ‖L (minorPol D T)‖ ≤ (a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M := by
      rw [minorPol_eq, map_sum]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [h0]
    calc _ ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt hM0]

end GlobalTheory.MinorBound
