import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CompactHarm

open MvPolynomial

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p k hp`. Establish `h : ∀ a b : σ, pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0`.

Introduce `a b`. Rewrite using `[pderiv_X]`. Distinguish the cases in `hk : k = b`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hk]`. Simplify using `only [Derivation.leibniz, map_add, smul_eq_mul, hp, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pd_comm {σ : Type*} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
      intro a b
      rw [pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, h]
    ring

/- English proof (translation)
Rewrite using `[Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `h : u = x`. Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same, mul_one, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Pi.single_apply, h, if_false, mul_zero, add_zero, zero_add]`.
-/
theorem pd_X_mul {σ : Type*} [DecidableEq σ] (x u : σ) (Q : MvPolynomial σ ℂ) :
    pderiv x (X u * Q) = (if u = x then Q else 0) + X u * pderiv x Q := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : u = x
  · subst h; simp only [Pi.single_eq_same, mul_one, if_true]; ring
  · simp only [Pi.single_apply, h, if_false, mul_zero, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[pd_X_mul, map_add, pd_X_mul]`. Apply the tactic sequence `split_ifs <;> (try simp only [map_zero]) <;> ring`.
-/
theorem dd_X_mul {σ : Type*} [DecidableEq σ] (x y u : σ) (R : MvPolynomial σ ℂ) :
    pderiv x (pderiv y (X u * R)) = (if u = y then pderiv x R else 0) + (if u = x then pderiv y R else 0) +
      X u * pderiv x (pderiv y R) := by
  rw [pd_X_mul, map_add, pd_X_mul]
  split_ifs <;> (try simp only [map_zero]) <;> ring

/- English proof (translation)
Simplify using `only [map_sum, dd_X_mul]`. Simplify using `only [Finset.sum_add_distrib]`. Rewrite using `[hA1, hA2, zero_add, zero_add, Finset.sum_comm]`. Establish `: ∀ k, ∑ j, X (u k) * pderiv (x j) (pderiv (y j) (pderiv (w k) P)) = 0`. Introduce `k`.

Rewrite using `[← Finset.mul_sum]`. Simplify using `only [pd_comm (y _) (w k), pd_comm (x _) (w k)]`. Rewrite using `[← map_sum, hxy, map_zero, mul_zero]`. Simplify using `[this]`.
-/
theorem gen {σ : Type*} [DecidableEq σ] {n : ℕ} (x y u w : Fin n → σ) (P : MvPolynomial σ ℂ)
    (hxy : ∑ j, pderiv (x j) (pderiv (y j) P) = 0)
    (hA1 : ∑ j, ∑ k, (if u k = y j then pderiv (x j) (pderiv (w k) P) else 0) = 0)
    (hA2 : ∑ j, ∑ k, (if u k = x j then pderiv (y j) (pderiv (w k) P) else 0) = 0) :
    ∑ j, pderiv (x j) (pderiv (y j) (∑ k, X (u k) * pderiv (w k) P)) = 0 := by
  simp only [map_sum, dd_X_mul]
  simp only [Finset.sum_add_distrib]
  rw [hA1, hA2, zero_add, zero_add, Finset.sum_comm]
  have : ∀ k, ∑ j, X (u k) * pderiv (x j) (pderiv (y j) (pderiv (w k) P)) = 0 := by
    intro k
    rw [← Finset.mul_sum]
    simp only [pd_comm (y _) (w k), pd_comm (x _) (w k)]
    rw [← map_sum, hxy, map_zero, mul_zero]
  simp [this]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

/- English proof (translation)
Unfold `fockT`. Rewrite using `[Finset.sum_eq_single i, Finset.sum_eq_single l]`. Simplify using `only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]`. Use `congr 1`. Use `split_ifs with h`.

Simplify using `only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_smul]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Simplify using `[Matrix.single_apply, Ne.symm hk]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Rewrite using `[Finset.sum_eq_zero]`.

Introduce `l' _`. Simplify using `[Matrix.single_apply, Ne.symm hk]`. Simplify using the standard rewrite rules.
-/
theorem fockT_single {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      ∑ j, (raiO τ (fun _ : Fin n => true) ε' i j * lowO τ (fun _ : Fin n => true) ε' l j) Q +
        (if i = l then ((n : ℂ) / 2) • Q else 0) := by
  classical
  unfold fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_smul]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    intro l' _
    simp [Matrix.single_apply, Ne.symm hk]
  · simp

/- English proof (translation)
Establish `hil : i ≠ l` using `fun e => by rw [e, hl] at hi; exact Bool.noConfusion hi`. Rewrite using `[fockT_single, if_neg hil, add_zero, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[raiO, lowO, sgn, hi, hl]`.
-/
theorem low_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (i l : Fin m) (hi : ε' i = false)
    (hl : ε' l = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single i l (1 : ℂ)) Q =
      -∑ j, pderiv (τ, i, j) (pderiv (τ, l, j) Q) := by
  have hil : i ≠ l := fun e => by rw [e, hl] at hi; exact Bool.noConfusion hi
  rw [fockT_single, if_neg hil, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, hi, hl]

/- English proof (translation)
Rewrite using `[fockT_single]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[raiO, lowO, sgn, ha, hb]`.
-/
theorem up_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = true)
    (hb : ε' b = true) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      ∑ j, X (τ, a, j) * pderiv (τ, b, j) Q + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

/- English proof (translation)
Rewrite using `[fockT_single, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[raiO, lowO, sgn, ha, hb]`.
-/
theorem dn_eq {D : D7} {m n : ℕ} (τ : D.what₂.Tau) (ε' : Fin m → Bool) (a b : Fin m) (ha : ε' a = false)
    (hb : ε' b = false) (Q : PolF D m n) :
    fockT τ (fun _ : Fin n => true) ε' (Matrix.single a b (1 : ℂ)) Q =
      -∑ j, pderiv (τ, a, j) (X (τ, b, j) * Q) + (if a = b then ((n : ℂ) / 2) • Q else 0) := by
  rw [fockT_single, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [raiO, lowO, sgn, ha, hb]

end GlobalTheory.CompactHarm

namespace GlobalTheory.CompactHarm

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

/- English proof (translation)
Introduce `D n m p P hP τ a b hab τ' i l hi hl`. Establish `hL : ∀ (σ : D.what₂.Tau) (i l : Fin m), p σ ≤ (i : ℕ) → (l : ℕ) < p σ → ∑ j, pderiv (σ, i, j) (pderiv (σ, l, j) P) = 0`. Introduce `σ i l hi hl`. Use `hP σ i l hi hl` as an intermediate fact. Rewrite `this` using `[low_eq σ _ i l (by simpa using hi) (by simpa using hl)]`.

Conclude with `neg_eq_zero.1 this`. Rewrite using `[low_eq τ' _ i l (by simpa using hi) (by simpa using hl), neg_eq_zero]`. Set `Lop : PolF D m n →ₗ[ℂ] PolF D m n` to `∑ j, (pderiv (τ', i, j)).toLinearMap ∘ₗ (pderiv (τ', l, j)).toLinearMap`. Establish `hLop : ∀ Q, Lop Q = ∑ j, pderiv (τ', i, j) (pderiv (τ', l, j) Q)`. Introduce `Q`.

Simplify using `[Lop, LinearMap.sum_apply]`. Establish `hP0 : Lop P = 0` using `by rw [hLop]; exact hL τ' i l hi hl`. Establish `hite : ∀ (c : Prop) [Decidable c] (z : ℂ), Lop (if c then z • P else 0) = 0`. Apply the tactic sequence `intro c _ z; split_ifs <;> simp [hP0]`. Rewrite using `[← hLop]`.

Distinguish the cases in `ha : (a : ℕ) < p τ`. Establish `hb : (b : ℕ) < p τ` using `hab.1 ha`. Rewrite using `[up_eq τ _ a b (by simpa using ha) (by simpa using hb), map_add, hite, add_zero, hLop]`. Use `gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, a, k)) (fun k => (τ, b, k)) P (hL τ' i l hi hl) ?_ ?_` and prove the remaining obligations. Distinguish the cases in `h : τ = τ' ∧ a = l`.

Take `⟨rfl, rfl⟩` from `h`. Simplify using `only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `hL τ i b hi hb`. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_` and prove the remaining obligations. Introduce `e`.

Simplify using `only [Prod.mk.injEq] at e`. Conclude with `h ⟨e.1, e.2.1⟩`. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_` and prove the remaining obligations. Introduce `e`. Simplify using `only [Prod.mk.injEq] at e`.

Take `⟨rfl, rfl, -⟩` from `e`. Use linear arithmetic over natural numbers and integers. Establish `hb : ¬ (b : ℕ) < p τ` using `fun h => ha (hab.2 h)`. Rewrite using `[dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]`. Establish `e : ∑ k, pderiv (τ, a, k) (X (τ, b, k) * P) = (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) + ∑ k, X (τ, b, k) * pderiv (τ, a, k) P`.

Simplify using `only [pd_X_mul, Finset.sum_add_distrib]`. Establish `hS1 : Lop (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) = 0`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [hP0]`.

Rewrite using `[e, map_add, map_neg, map_add, hS1, zero_add, hite, add_zero, neg_eq_zero, hLop]`. Use `gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, b, k)) (fun k => (τ, a, k)) P (hL τ' i l hi hl) ?_ ?_` and prove the remaining obligations. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_` and prove the remaining obligations. Introduce `e`. Simplify using `only [Prod.mk.injEq] at e`.

Take `⟨rfl, rfl, -⟩` from `e`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : τ = τ' ∧ b = i`. Take `⟨rfl, rfl⟩` from `h`. Simplify using `only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Simplify using `only [pd_comm (τ, l, _) (τ, a, _)]`. Conclude with `hL τ a l (not_lt.1 ha) hl`. Use `Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_` and prove the remaining obligations. Introduce `e`. Simplify using `only [Prod.mk.injEq] at e`.

Conclude with `h ⟨e.1, e.2.1⟩`.
-/
theorem fockT_compact_harm : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (P : PolF D m n), (∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (P) = 0) → ∀ (τ : D.what₂.Tau) (a b : Fin m), ((a : ℕ) < p τ ↔ (b : ℕ) < p τ) → ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single a b (1 : ℂ)) P) = 0 := by
  classical
  intro D n m p P hP τ a b hab τ' i l hi hl
  have hL : ∀ (σ : D.what₂.Tau) (i l : Fin m), p σ ≤ (i : ℕ) → (l : ℕ) < p σ →
      ∑ j, pderiv (σ, i, j) (pderiv (σ, l, j) P) = 0 := by
    intro σ i l hi hl
    have := hP σ i l hi hl
    rw [low_eq σ _ i l (by simpa using hi) (by simpa using hl)] at this
    exact neg_eq_zero.1 this
  rw [low_eq τ' _ i l (by simpa using hi) (by simpa using hl), neg_eq_zero]
  let Lop : PolF D m n →ₗ[ℂ] PolF D m n :=
    ∑ j, (pderiv (τ', i, j)).toLinearMap ∘ₗ (pderiv (τ', l, j)).toLinearMap
  have hLop : ∀ Q, Lop Q = ∑ j, pderiv (τ', i, j) (pderiv (τ', l, j) Q) := by
    intro Q; simp [Lop, LinearMap.sum_apply]
  have hP0 : Lop P = 0 := by rw [hLop]; exact hL τ' i l hi hl
  have hite : ∀ (c : Prop) [Decidable c] (z : ℂ), Lop (if c then z • P else 0) = 0 := by
    intro c _ z; split_ifs <;> simp [hP0]
  rw [← hLop]
  by_cases ha : (a : ℕ) < p τ
  · have hb : (b : ℕ) < p τ := hab.1 ha
    rw [up_eq τ _ a b (by simpa using ha) (by simpa using hb), map_add, hite, add_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, a, k)) (fun k => (τ, b, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · by_cases h : τ = τ' ∧ a = l
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hL τ i b hi hb
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
  · have hb : ¬ (b : ℕ) < p τ := fun h => ha (hab.2 h)
    rw [dn_eq τ _ a b (by simpa using ha) (by simpa using hb)]
    have e : ∑ k, pderiv (τ, a, k) (X (τ, b, k) * P) =
        (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) + ∑ k, X (τ, b, k) * pderiv (τ, a, k) P := by
      simp only [pd_X_mul, Finset.sum_add_distrib]
    have hS1 : Lop (∑ k, if ((τ, b, k) : FVar D m n) = (τ, a, k) then P else 0) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs <;> simp [hP0]
    rw [e, map_add, map_neg, map_add, hS1, zero_add, hite, add_zero, neg_eq_zero, hLop]
    refine gen (fun j => (τ', i, j)) (fun j => (τ', l, j)) (fun k => (τ, b, k)) (fun k => (τ, a, k)) P
      (hL τ' i l hi hl) ?_ ?_
    · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
      intro e; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; omega
    · by_cases h : τ = τ' ∧ b = i
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Prod.mk.injEq, true_and, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        simp only [pd_comm (τ, l, _) (τ, a, _)]
        exact hL τ a l (not_lt.1 ha) hl
      · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => if_neg ?_
        intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩

end GlobalTheory.CompactHarm
