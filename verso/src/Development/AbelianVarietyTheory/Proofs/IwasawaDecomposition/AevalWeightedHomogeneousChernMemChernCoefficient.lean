import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpanStatement

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

/- English proof (translation)
Unfold `TrSpan`. Conclude with `Submodule.subset_span ⟨[], by simp, by simp, by funext A; simp [trProd]⟩`.
-/
theorem one_mem_trSpan_zero {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    (1 : Mat m S → S) ∈ TrSpan m 0 S := by
  unfold TrSpan
  exact Submodule.subset_span ⟨[], by simp, by simp, by funext A; simp [trProd]⟩

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simpa using one_mem_trSpan_zero m S`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S (k * w) w _ _ ih hf`.
-/
theorem pow_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w : ℕ)
    (f : Mat m S → S) (hf : f ∈ TrSpan m w S) (e : ℕ) : f ^ e ∈ TrSpan m (e * w) S := by
  induction e with
  | zero => simpa using one_mem_trSpan_zero m S
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S (k * w) w _ _ ih hf

/- English proof (translation)
Use `revert hf`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using one_mem_trSpan_zero m S`. Introduce `a t ha ih hf`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S _ _ _ _ (hf a (Finset.mem_insert_self a t)) (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))`.
-/
theorem prod_mem_trSpan {ι κ : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (s : Finset κ)
    (w : κ → ℕ) (f : κ → Mat m S → S) (hf : ∀ x ∈ s, f x ∈ TrSpan m (w x) S) :
    ∏ x ∈ s, f x ∈ TrSpan m (∑ x ∈ s, w x) S := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using one_mem_trSpan_zero m S
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S _ _ _ _ (hf a (Finset.mem_insert_self a t))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

/- English proof (translation)
Unfold `TrSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `f ⟨l, hl, hs, rfl⟩`. Conclude with `GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan m n S l hl hs`.
-/
theorem trSpan_le_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    TrSpan m n S ≤ Reach m n S := by
  unfold TrSpan
  rw [Submodule.span_le]
  rintro f ⟨l, hl, hs, rfl⟩
  exact GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan m n S l hl hs

/- English proof (translation)
Use `trSpan_le_reach m n S ?_` and prove the remaining obligations. Establish `key : ∀ d ∈ R.support, (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d))) ∈ TrSpan m n S`. Introduce `d hd`. Establish `hdeg : Finsupp.weight Prod.snd d = n` using `hR (mem_support_iff.mp hd)`. Establish `hprod` using `prod_mem_trSpan m S d.support (fun x => d x * x.2) (fun x (A : Mat m S) => (Matrix.charpolyRev (-(A x.1))).coeff x.2 ^ d x) (fun x _ => pow_mem_trSpan m S x.2 _ (GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan m S x.1 x.2) (d x))`.

Establish `hw : ∑ x ∈ d.support, d x * x.2 = n`. Rewrite using `[← hdeg, Finsupp.weight_apply, Finsupp.sum]`. Simplify using `[smul_eq_mul]`. Rewrite `hprod` using `[hw]`. Use `Submodule.smul_mem _ (R.coeff d) hprod using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `A`. Simplify using `[aeval_monomial, Finsupp.prod, Finset.prod_apply, Algebra.smul_def]`. Establish `hsum : (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) = ∑ d ∈ R.support, fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d))`. Use function extensionality and compare the values at `A`. Use `conv_lhs => rw [R.as_sum]`.

Simplify using `only [map_sum, Finset.sum_apply]`. Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ key`.
-/
theorem aeval_chern_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (R : MvPolynomial (ι × ℕ) ℝ) (hR : R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n) :
    (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  refine trSpan_le_reach m n S ?_

  have key : ∀ d ∈ R.support, (fun A : Mat m S =>
      aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)))
        ∈ TrSpan m n S := by
    intro d hd
    have hdeg : Finsupp.weight Prod.snd d = n := hR (mem_support_iff.mp hd)
    have hprod := prod_mem_trSpan m S d.support (fun x => d x * x.2)
      (fun x (A : Mat m S) => (Matrix.charpolyRev (-(A x.1))).coeff x.2 ^ d x)
      (fun x _ => pow_mem_trSpan m S x.2 _ (GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan m S x.1 x.2) (d x))
    have hw : ∑ x ∈ d.support, d x * x.2 = n := by
      rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
      simp [smul_eq_mul]
    rw [hw] at hprod
    convert Submodule.smul_mem _ (R.coeff d) hprod using 1
    funext A
    simp [aeval_monomial, Finsupp.prod, Finset.prod_apply, Algebra.smul_def]
  have hsum : (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) =
      ∑ d ∈ R.support, fun A : Mat m S =>
        aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)) := by
    funext A
    conv_lhs => rw [R.as_sum]
    simp only [map_sum, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ key

end GlobalTheory.GoodMetric.ChernSpan
