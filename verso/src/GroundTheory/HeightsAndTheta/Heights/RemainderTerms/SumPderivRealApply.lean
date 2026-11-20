import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

namespace TwoCasesDerivatives

open MvPolynomial Finset

noncomputable section

variable (f j k : ℕ)

def sumPderivReal {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k)) :
    Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :=
  ∑ l ∈ s, pderiv (τ, g l)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [sumPderivReal]`. Consider the case `insert b s hb ih`. Rewrite using `[Finset.sum_insert hb, ← ih]`. Simplify using `[sumPderivReal, Finset.sum_insert hb]`.
-/
theorem sumPderivReal_apply {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    sumPderivReal f j k τ s g P = ∑ l ∈ s, pderiv (τ, g l) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumPderivReal]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← ih]
    simp [sumPderivReal, Finset.sum_insert hb]

/- English proof (translation)
Rewrite using `[sumPderivReal_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_X, Pi.single_apply]`. Simplify using `only [Prod.mk.injEq]`.
-/
theorem sumPderivReal_X {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (σ : Fin f) (i : Fin (j + k)) :
    sumPderivReal f j k τ s g (X (σ, i)) =
      ∑ l ∈ s, if σ = τ ∧ i = g l then (1 : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) else 0 := by
  classical
  rw [sumPderivReal_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_X, Pi.single_apply]
  simp only [Prod.mk.injEq]

/- English proof (translation)
Establish `hfib : D (IndefiniteRowSideFullHecke.RestTerms.fibClass f j k bot) = 0`. Unfold `IndefiniteRowSideFullHecke.RestTerms.fibClass`. Use `Flag.derivation_prod_eq_zero D _ _ (fun σ _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `cases bot <;> simp only [Bool.false_eq_true, if_false, if_true] <;>`. Rewrite using `[Derivation.leibniz, ← vandermondeOf_eq_vandermonde, ← vandermondeOf_eq_vandermonde, Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]), Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]), smul_zero, smul_zero, add_zero]`.

Establish `hmu : D (IndefiniteRowSideFullHecke.RestTerms.muClass f j k bot) = C (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ))`. Apply the tactic sequence `cases bot <;>`. Simplify using `[IndefiniteRowSideFullHecke.RestTerms.muClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, map_sum, ht, hb, Finset.mul_sum]`. Rewrite using `[IndefiniteRowSideFullHecke.RestTerms.restPoly, Derivation.leibniz, hfib, smul_zero, zero_add, Derivation.leibniz_pow, hmu, IndefiniteRowSideFullHecke.RestTerms.degPoly]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]`.

Simplify using `only [map_mul, map_natCast, map_add, map_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_restPoly (D : Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k))
    (bot : Bool) (α β : Fin f → ℝ)
    (ht : ∀ σ (a : Fin j), D (X (σ, Fin.castAdd k a)) = C (α σ))
    (hb : ∀ σ (b : Fin k), D (X (σ, Fin.natAdd j b)) = C (β σ)) :
    D (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) =
      C (((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) *
          (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ))) *
        IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot := by
  have hfib : D (IndefiniteRowSideFullHecke.RestTerms.fibClass f j k bot) = 0 := by
    unfold IndefiniteRowSideFullHecke.RestTerms.fibClass
    refine Flag.derivation_prod_eq_zero D _ _ (fun σ _ => ?_)
    cases bot <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [Derivation.leibniz, ← vandermondeOf_eq_vandermonde, ← vandermondeOf_eq_vandermonde,
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        smul_zero, smul_zero, add_zero]
  have hmu : D (IndefiniteRowSideFullHecke.RestTerms.muClass f j k bot) =
      C (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ)) := by
    cases bot <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.muClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, map_sum, ht, hb, Finset.mul_sum]
  rw [IndefiniteRowSideFullHecke.RestTerms.restPoly, Derivation.leibniz, hfib, smul_zero, zero_add,
    Derivation.leibniz_pow, hmu, IndefiniteRowSideFullHecke.RestTerms.degPoly]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast, map_add, map_one]
  push_cast
  ring

end

end TwoCasesDerivatives

open MvPolynomial Finset TwoCasesDerivatives

/- English proof (translation)
Introduce `f j k I τ`. Establish `hI : ∀ (c : ℝ) (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), I (C c * P) = c * I P`. Introduce `c P`. Rewrite using `[← smul_eq_C_mul, map_smul, smul_eq_mul]`. Establish `hsh : ∀ F, IndefiniteRowSideFullHecke.RestTerms.shiftAt f j k I τ F = I (sumPderivReal f j k τ univ (Fin.castAdd k) F)`.

Introduce `F`. Rewrite using `[sumPderivReal_apply]`. Both sides reduce to the same expression. Establish `hto : ∀ F, IndefiniteRowSideFullHecke.RestTerms.totalAt f j k I τ F = I (sumPderivReal f j k τ univ id F)`. Introduce `F`.

Rewrite using `[sumPderivReal_apply]`. Both sides reduce to the same expression. Establish `shT : ∀ σ (a : Fin j), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.castAdd k a)) = C (if σ = τ then 1 else 0)`. Introduce `σ a`. Rewrite using `[sumPderivReal_X]`.

Apply the tactic sequence `by_cases h : σ = τ <;> simp [h, Fin.castAdd_inj]`. Establish `shB : ∀ σ (b : Fin k), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.natAdd j b)) = C 0`. Introduce `σ b`. Rewrite using `[sumPderivReal_X]`. Use `(Finset.sum_eq_zero fun a _ => ?_).trans C_0.symm` and prove the remaining obligations.

Rewrite using `[if_neg]`. Introduce and unpack `⟨-, h⟩`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `toX : ∀ σ i, sumPderivReal f j k τ univ id (X (σ, i)) = C (if σ = τ then 1 else 0)`. Introduce `σ i`. Rewrite using `[sumPderivReal_X]`. Apply the tactic sequence `by_cases h : σ = τ <;> simp [h]`. Establish `hs : ∑ σ : Fin f, (if σ = τ then (1 : ℝ) else 0) = 1` using `by simp`.

Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsh, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB, hI]`. Simplify using the standard rewrite rules. Rewrite using `[hto, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0) (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI, if_pos rfl, hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsh, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB, hI, if_neg Bool.false_ne_true, hs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hto, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0) (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI, if_neg Bool.false_ne_true, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem TwoCases.intersectionNumber_baseChange : IndefiniteRowSideFullHecke.RestTerms.TwoCases.Statement := by
  classical
  intro f j k I τ
  have hI : ∀ (c : ℝ) (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), I (C c * P) = c * I P := by
    intro c P
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hsh : ∀ F, IndefiniteRowSideFullHecke.RestTerms.shiftAt f j k I τ F =
      I (sumPderivReal f j k τ univ (Fin.castAdd k) F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have hto : ∀ F, IndefiniteRowSideFullHecke.RestTerms.totalAt f j k I τ F = I (sumPderivReal f j k τ univ id F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have shT : ∀ σ (a : Fin j), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.castAdd k a)) =
      C (if σ = τ then 1 else 0) := by
    intro σ a
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h, Fin.castAdd_inj]
  have shB : ∀ σ (b : Fin k), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.natAdd j b)) =
      C 0 := by
    intro σ b
    rw [sumPderivReal_X]
    refine (Finset.sum_eq_zero fun a _ => ?_).trans C_0.symm
    rw [if_neg]
    rintro ⟨-, h⟩
    have := congrArg Fin.val h
    simp at this
    omega
  have toX : ∀ σ i, sumPderivReal f j k τ univ id (X (σ, i)) = C (if σ = τ then 1 else 0) := by
    intro σ i
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h]
  have hs : ∑ σ : Fin f, (if σ = τ then (1 : ℝ) else 0) = 1 := by simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hsh, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI]
    simp
  · rw [hto, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI, if_pos rfl,
      hs]
    ring
  · rw [hsh, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI, if_neg Bool.false_ne_true, hs]
    ring
  · rw [hto, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI,
      if_neg Bool.false_ne_true, hs]
    ring

end GroundTheory.Heights₂.Heights.RestTerms
