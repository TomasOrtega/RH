import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmCoeffProdLinearStatement

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `k E _ _ _ P m A hA10 hdet q c s t hc hst hq`. Set `α : Fin m → E` to `fun j => s j * A 0 0 + t j * A 0 1`. Set `β : Fin m → E` to `fun j => t j * A 1 1`. Establish `hfac : ∀ j, C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X) = C (α j) + C (β j) * X`. Introduce `j`.

Simplify using `only [α, β, C_add, C_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hvec : (symMat m A).mulVec q = fun a : Fin (m + 1) => c * (∏ j, (C (α j) + C (β j) * X)).coeff a`. Rewrite using `[symMat_mulVec, hq]`. Use function extensionality and compare the values at `a`.

Simplify using `only [hfac, coeff_C_mul]`. Establish `hsup : ∀ (n : ℕ) (x : Fin n → E), nrm P (fun a => c * x a) = P.1 c * nrm P x`. Introduce `n x`. Establish `h` using `Finset.comp_sup_eq_sup_comp (s := Finset.univ) (f := fun a => P.1 (x a)) (fun y => P.1 c * y) (fun a b => by`. Break down `le_total a b with h | h` into its components or cases.

Rewrite using `[sup_eq_right.2 h, sup_eq_right.2 (mul_le_mul' le_rfl h)]`. Rewrite using `[sup_eq_left.2 h, sup_eq_left.2 (mul_le_mul' le_rfl h)]) (by simp)`. Simplify using `only [nrm, map_mul]`. Conclude with `h.symm`. Establish `hfin2 : ∀ f : Fin 2 → WithZero (Multiplicative ℤ), Finset.univ.sup f = max (f 0) (f 1)`.

Introduce `f`. Use `le_antisymm (Finset.sup_le fun i _ => ?_) (max_le (Finset.le_sup (Finset.mem_univ 0)) (Finset.le_sup (Finset.mem_univ 1)))` and prove the remaining obligations. Use `fin_cases i`. Conclude with `le_max_left _ _`. Conclude with `le_max_right _ _`.

Establish `hw : ∀ j, nrm P (A.mulVec ![s j, t j]) = max (P.1 (α j)) (P.1 (β j))`. Introduce `j`. Rewrite using `[nrm, hfin2]`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hA10, zero_mul, zero_add, α, β]`. Rewrite using `[mul_comm (A 0 0), mul_comm (A 0 1), mul_comm (A 1 1)]`.

Establish `hnz : ∀ j, nrm P (A.mulVec ![s j, t j]) ≠ 0`. Introduce `j h0`. Establish `hne : A.mulVec ![s j, t j] ≠ 0` using `fun h => hst j (Matrix.eq_zero_of_mulVec_eq_zero hdet h)`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hne`. Establish `h1 : P.1 (A.mulVec ![s j, t j] i) ≤ nrm P (A.mulVec ![s j, t j])` using `Finset.le_sup (f := fun i => P.1 (A.mulVec ![s j, t j] i)) (Finset.mem_univ i)`.

Rewrite `h1` using `[h0]`. Conclude with `(Valuation.ne_zero_iff _).2 hi (le_antisymm h1 zero_le')`. Establish `hPc : P.1 c ≠ 0` using `(Valuation.ne_zero_iff _).2 hc`. Establish `hlogprod : ∀ S : Finset (Fin m), WithZero.log (∏ j ∈ S, nrm P (A.mulVec ![s j, t j])) = ∑ j ∈ S, WithZero.log (nrm P (A.mulVec ![s j, t j]))`. Introduce `S`.

Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, WithZero.log_mul (hnz a) (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), ih]`. Establish `hmain : nrm P ((symMat m A).mulVec q) = P.1 c * ∏ j, nrm P (A.mulVec ![s j, t j])`.

Rewrite using `[hvec, hsup, GlobalTheory.T.nrm_coeff_prod_linear' k E P m α β]`. Simplify using `only [hw]`. Rewrite using `[ordVec, hmain, WithZero.log_mul hPc (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), hlogprod, ord]`. Simplify using `only [ordVec, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordVec_symMat_mulVec_triangular : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E),
    c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) →
    ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) =
      C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) →
    ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  intro k E _ _ _ P m A hA10 hdet q c s t hc hst hq
  classical
  let α : Fin m → E := fun j => s j * A 0 0 + t j * A 0 1
  let β : Fin m → E := fun j => t j * A 1 1
  have hfac : ∀ j, C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X) = C (α j) + C (β j) * X := by
    intro j
    simp only [α, β, C_add, C_mul]
    ring
  have hvec : (symMat m A).mulVec q = fun a : Fin (m + 1) => c * (∏ j, (C (α j) + C (β j) * X)).coeff a := by
    rw [symMat_mulVec, hq]
    funext a
    simp only [hfac, coeff_C_mul]
  have hsup : ∀ (n : ℕ) (x : Fin n → E), nrm P (fun a => c * x a) = P.1 c * nrm P x := by
    intro n x
    have h := Finset.comp_sup_eq_sup_comp (s := Finset.univ) (f := fun a => P.1 (x a)) (fun y => P.1 c * y)
      (fun a b => by
        rcases le_total a b with h | h
        · rw [sup_eq_right.2 h, sup_eq_right.2 (mul_le_mul' le_rfl h)]
        · rw [sup_eq_left.2 h, sup_eq_left.2 (mul_le_mul' le_rfl h)]) (by simp)
    simp only [nrm, map_mul]
    exact h.symm
  have hfin2 : ∀ f : Fin 2 → WithZero (Multiplicative ℤ), Finset.univ.sup f = max (f 0) (f 1) := by
    intro f
    refine le_antisymm (Finset.sup_le fun i _ => ?_) (max_le (Finset.le_sup (Finset.mem_univ 0))
      (Finset.le_sup (Finset.mem_univ 1)))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hw : ∀ j, nrm P (A.mulVec ![s j, t j]) = max (P.1 (α j)) (P.1 (β j)) := by
    intro j
    rw [nrm, hfin2]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hA10, zero_mul, zero_add, α, β]
    rw [mul_comm (A 0 0), mul_comm (A 0 1), mul_comm (A 1 1)]
  have hnz : ∀ j, nrm P (A.mulVec ![s j, t j]) ≠ 0 := by
    intro j h0
    have hne : A.mulVec ![s j, t j] ≠ 0 := fun h => hst j (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have h1 : P.1 (A.mulVec ![s j, t j] i) ≤ nrm P (A.mulVec ![s j, t j]) :=
      Finset.le_sup (f := fun i => P.1 (A.mulVec ![s j, t j] i)) (Finset.mem_univ i)
    rw [h0] at h1
    exact (Valuation.ne_zero_iff _).2 hi (le_antisymm h1 zero_le')
  have hPc : P.1 c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hlogprod : ∀ S : Finset (Fin m), WithZero.log (∏ j ∈ S, nrm P (A.mulVec ![s j, t j])) =
      ∑ j ∈ S, WithZero.log (nrm P (A.mulVec ![s j, t j])) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        WithZero.log_mul (hnz a) (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), ih]
  have hmain : nrm P ((symMat m A).mulVec q) = P.1 c * ∏ j, nrm P (A.mulVec ![s j, t j]) := by
    rw [hvec, hsup, GlobalTheory.T.nrm_coeff_prod_linear' k E P m α β]
    simp only [hw]
  rw [ordVec, hmain, WithZero.log_mul hPc (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), hlogprod, ord]
  simp only [ordVec, Finset.sum_neg_distrib]
  ring

end GlobalTheory.Nef
