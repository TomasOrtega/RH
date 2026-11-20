import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym

open MvPolynomial Finset

variable {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ}

def letterCount (w : Fin n → σ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => (univ.filter fun r => w r = p).card

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem letterCount_apply (w : Fin n → σ) (p : σ) :
    letterCount w p = (univ.filter fun r => w r = p).card := rfl

/- English proof (translation)
Rewrite using `[MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Finset.prod_fiberwise univ w]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_congr rfl (g := fun _ => (X p : MvPolynomial σ ℝ)) (fun j hj => by rw [(Finset.mem_filter.1 hj).2])]`. Simplify using `[letterCount_apply]`.
-/
theorem prod_X_eq_monomial (w : Fin n → σ) :
    (∏ j, (X (w j) : MvPolynomial σ ℝ)) = monomial (letterCount w) 1 := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    ← Finset.prod_fiberwise univ w]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => (X p : MvPolynomial σ ℝ))
    (fun j hj => by rw [(Finset.mem_filter.1 hj).2])]
  simp [letterCount_apply]

/- English proof (translation)
Use extensionality with `p`. Rewrite using `[letterCount_apply, letterCount_apply]`. Conclude with `Finset.card_equiv π (fun r => by simp)`.
-/
theorem letterCount_comp (w : Fin n → σ) (π : Equiv.Perm (Fin n)) :
    letterCount (w ∘ π) = letterCount w := by
  ext p
  rw [letterCount_apply, letterCount_apply]
  exact Finset.card_equiv π (fun r => by simp)

/- English proof (translation)
Establish `e : ∀ p, {r // w r = p} ≃ {r // w₀ r = p}` using `fun p => Fintype.equivOfCardEq (by`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Conclude with `DFunLike.congr_fun h p)`. Conclude with `⟨Equiv.ofFiberEquiv e, funext fun r => Equiv.ofFiberEquiv_map e r⟩`.
-/
theorem exists_perm_of_letterCount_eq (w w₀ : Fin n → σ) (h : letterCount w = letterCount w₀) :
    ∃ π : Equiv.Perm (Fin n), w₀ ∘ π = w := by
  have e : ∀ p, {r // w r = p} ≃ {r // w₀ r = p} := fun p => Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact DFunLike.congr_fun h p)
  exact ⟨Equiv.ofFiberEquiv e, funext fun r => Equiv.ofFiberEquiv_map e r⟩

/- English proof (translation)
Establish `hst : Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} = ∏ p, (letterCount w₀ p).factorial`. Rewrite using `[DomMulAct.stabilizer_card]`. Conclude with `Finset.prod_congr rfl fun p _ => by rw [Fintype.card_subtype, letterCount_apply]`. Establish `hcard : (univ : Finset (Equiv.Perm (Fin n))).card = n.factorial`. Simplify using `[Finset.card_univ, Fintype.card_perm]`.

Establish `hfib : ∀ w ∈ univ.filter (fun w : Fin n → σ => letterCount w = letterCount w₀), (univ.filter fun π : Equiv.Perm (Fin n) => w₀ ∘ π = w).card = Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀}`. Introduce `w hw`. Take `⟨π₀, rfl⟩` from `exists_perm_of_letterCount_eq w w₀ (Finset.mem_filter.1 hw).2`. Rewrite using `[← Fintype.card_subtype]`. Use `Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulRight π₀⁻¹) fun g => ?_)` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `r`. Use `congrFun h (π₀⁻¹ r)` as an intermediate fact. Simplify using `using this`.

Introduce `h`. Use function extensionality and compare the values at `r`. Use `congrFun h (π₀ r)` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hst, ← hcard, Finset.card_eq_sum_card_fiberwise (s := univ) (f := fun π : Equiv.Perm (Fin n) => w₀ ∘ π) (t := univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀) (fun π _ => by simp [letterCount_comp]), Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]`.
-/
theorem card_letterCount_mul (w₀ : Fin n → σ) :
    (univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card *
      ∏ p, (letterCount w₀ p).factorial = n.factorial := by
  have hst : Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} =
      ∏ p, (letterCount w₀ p).factorial := by
    rw [DomMulAct.stabilizer_card]
    exact Finset.prod_congr rfl fun p _ => by rw [Fintype.card_subtype, letterCount_apply]
  have hcard : (univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    simp [Finset.card_univ, Fintype.card_perm]
  have hfib : ∀ w ∈ univ.filter (fun w : Fin n → σ => letterCount w = letterCount w₀),
      (univ.filter fun π : Equiv.Perm (Fin n) => w₀ ∘ π = w).card =
        Fintype.card {g : Equiv.Perm (Fin n) // w₀ ∘ g = w₀} := by
    intro w hw
    obtain ⟨π₀, rfl⟩ := exists_perm_of_letterCount_eq w w₀ (Finset.mem_filter.1 hw).2
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulRight π₀⁻¹) fun g => ?_)
    constructor
    · intro h
      funext r
      have := congrFun h (π₀⁻¹ r)
      simpa using this
    · intro h
      funext r
      have := congrFun h (π₀ r)
      simpa using this
  rw [← hst, ← hcard, Finset.card_eq_sum_card_fiberwise (s := univ)
    (f := fun π : Equiv.Perm (Fin n) => w₀ ∘ π)
    (t := univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀)
    (fun π _ => by simp [letterCount_comp]), Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/- English proof (translation)
Take `rfl : m = letterCount w₀` from `Finsupp.ext fun p => by rw [hm, letterCount_apply]`. Establish `hc : coeff (letterCount w₀) (PB.formPoly n a) = ((univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card : ℝ) * a w₀`. Unfold `PB.formPoly`. Rewrite using `[coeff_sum, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[prod_X_eq_monomial, coeff_C_mul, coeff_monomial]`. Distinguish the cases in `h : letterCount w = letterCount w₀`. Take `⟨π, rfl⟩` from `exists_perm_of_letterCount_eq w w₀ h`. Simplify using `[letterCount_comp, hsym]`. Simplify using `[h]`.

Rewrite using `[hc, ← card_letterCount_mul w₀]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_formPoly_mul (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (hsym : ∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) (w₀ : Fin n → σ) (m : σ →₀ ℕ)
    (hm : ∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) :
    coeff m (PB.formPoly n a) * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ := by
  obtain rfl : m = letterCount w₀ := Finsupp.ext fun p => by rw [hm, letterCount_apply]
  have hc : coeff (letterCount w₀) (PB.formPoly n a) =
      ((univ.filter fun w : Fin n → σ => letterCount w = letterCount w₀).card : ℝ) * a w₀ := by
    unfold PB.formPoly
    rw [coeff_sum, ← nsmul_eq_mul, ← Finset.sum_const, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [prod_X_eq_monomial, coeff_C_mul, coeff_monomial]
    by_cases h : letterCount w = letterCount w₀
    · obtain ⟨π, rfl⟩ := exists_perm_of_letterCount_eq w w₀ h
      simp [letterCount_comp, hsym]
    · simp [h]
  rw [hc, ← card_letterCount_mul w₀]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym
