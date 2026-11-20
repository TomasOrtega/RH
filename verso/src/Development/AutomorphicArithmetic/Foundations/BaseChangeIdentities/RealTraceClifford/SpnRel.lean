import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Rewrite using `[← h1, ← h2]`. Use `noncomm_ring`.
-/
private theorem tri {A : Type} [Ring A] (x y z p q : A) (h1 : y * z + z * y = p)
    (h2 : x * z + z * x = q) : x * y * z - z * (x * y) = x * p - q * y := by
  rw [← h1, ← h2]
  noncomm_ring

/- English proof (translation)
Use `noncomm_ring`.
-/
private theorem leib {A : Type} [Ring A] (X u v : A) :
    X * (u * v) - u * v * X = (X * u - u * X) * v + u * (X * v - v * X) := by
  noncomm_ring

/- English proof (translation)
Establish `hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t` using `fun t r => (Algebra.commutes r t).symm`. Establish `hsum : spn c a b * c d e - c d e * spn c a b = ∑ f, (c a f * c f b * c d e - c d e * (c a f * c f b))`. Unfold `spn`. Rewrite using `[sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]`. Use `split_ifs`.

Rewrite using `[hs]`. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. Rewrite using `[hsum]`. Establish `hterm : ∀ f, c a f * c f b * c d e - c d e * (c a f * c f b) = c a f * (if b = d ∧ f = e then 1 else 0) - (if f = d ∧ a = e then 1 else 0) * c f b`.

Introduce `f`. Conclude with `tri _ _ _ _ _ (hc f b d e) (hc a f d e)`. Repeatedly rewrite using `[hterm]`. Rewrite using `[Finset.sum_sub_distrib]`. Use `congr 1`.

Distinguish the cases in `hbd : b = d`. Simplify using `[hbd]`. Simplify using `[hbd]`. Distinguish the cases in `hea : e = a`. Substitute `hea` using the available equality.

Simplify using the standard rewrite rules. Establish `: ∀ f : Fin n, ¬ (f = d ∧ a = e)` using `fun f h => hea h.2.symm`. Simplify using `[this, hea]`.
-/
private theorem spn_comm {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A)
    (hc : Clif c) (a b d e : Fin n) :
    spn c a b * c d e - c d e * spn c a b =
      (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have hsum : spn c a b * c d e - c d e * spn c a b =
      ∑ f, (c a f * c f b * c d e - c d e * (c a f * c f b)) := by
    unfold spn
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [hsum]
  have hterm : ∀ f, c a f * c f b * c d e - c d e * (c a f * c f b) =
      c a f * (if b = d ∧ f = e then 1 else 0) - (if f = d ∧ a = e then 1 else 0) * c f b := by
    intro f
    exact tri _ _ _ _ _ (hc f b d e) (hc a f d e)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases hbd : b = d
    · simp [hbd]
    · simp [hbd]
  · by_cases hea : e = a
    · subst hea
      simp
    · have : ∀ f : Fin n, ¬ (f = d ∧ a = e) := fun f h => hea h.2.symm
      simp [this, hea]

/- English proof (translation)
Introduce `n A _ _ c hc`. Use `⟨?_, fun a b d e => spn_comm c hc a b d e⟩` and prove the remaining obligations. Introduce `a b g h`. Establish `hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t` using `fun t r => (Algebra.commutes r t).symm`. Establish `expand : ∀ X : A, X * spn c g h - spn c g h * X = ∑ f, (X * (c g f * c f h) - c g f * c f h * X)`.

Introduce `X`. Unfold `spn`. Rewrite using `[mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]`. Use `split_ifs`. Rewrite using `[hs]`.

Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules. Rewrite using `[expand]`. Repeatedly rewrite using `[leib, spn_comm c hc]`. Simplify using `only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib]`.

Simplify using `only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]`. Unfold `spn`. Apply the tactic sequence `by_cases hbg : b = g <;> by_cases hha : h = a`. Substitute `hbg` using the available equality. Substitute `hha` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hbg, hha, Ne.symm hha]`. Simplify using `[hbg, hha, Ne.symm hbg]`. Normalize the expressions using the abelian group laws. Simplify using `[hbg, hha, Ne.symm hbg, Ne.symm hha]`.
-/
theorem UpperTheory.RealTr.spnRel :
    ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (c : Fin n → Fin n → A), Clif c → GlRel (spn c) ∧
      ∀ a b d e, spn c a b * c d e - c d e * spn c a b = (if b = d then c a e else 0) - (if e = a then c d b else 0) := by
  intro n A _ _ c hc
  refine ⟨?_, fun a b d e => spn_comm c hc a b d e⟩
  intro a b g h
  have hs : ∀ (t : A) (r : ℂ), t * algebraMap ℂ A r = algebraMap ℂ A r * t :=
    fun t r => (Algebra.commutes r t).symm
  have expand : ∀ X : A, X * spn c g h - spn c g h * X =
      ∑ f, (X * (c g f * c f h) - c g f * c f h * X) := by
    intro X
    unfold spn
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
    split_ifs
    · rw [hs]
      abel
    · simp
  rw [expand]
  simp_rw [leib, spn_comm c hc]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  unfold spn
  by_cases hbg : b = g <;> by_cases hha : h = a
  · subst hbg
    subst hha
    simp
  · simp [hbg, hha, Ne.symm hha]
  · simp [hbg, hha, Ne.symm hbg]
    abel
  · simp [hbg, hha, Ne.symm hbg, Ne.symm hha]
