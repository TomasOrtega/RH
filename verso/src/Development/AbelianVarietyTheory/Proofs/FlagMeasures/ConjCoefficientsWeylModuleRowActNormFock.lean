import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.ConjCoeff

/- English proof (translation)
Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Use `Submodule.subset_span ⟨v, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `smul a y _ hy`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem conj_mem_delSq {n : ℕ} (lam : DomWeight n) {p : MvPolynomial (Fin n × Fin n) ℂ}
    (hp : p ∈ delSq ℂ n lam) : MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (b : ℂ), Formalism.GradedWeylDivisibility.rowAct ℂ h (MvPolynomial.C b : MvPolynomial (Fin n × Fin n) ℂ) = MvPolynomial.C b` using `fun h b => (Formalism.GradedWeylDivisibility.rowAct ℂ h).commutes b`. Rewrite using `[h, MvPolynomial.map_C, h]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, MvPolynomial.map_X]`. Use `congr 1`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]`.
-/
theorem conj_rowAct {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (b : ℂ), Formalism.GradedWeylDivisibility.rowAct ℂ h (MvPolynomial.C b :
        MvPolynomial (Fin n × Fin n) ℂ) = MvPolynomial.C b := fun h b =>
      (Formalism.GradedWeylDivisibility.rowAct ℂ h).commutes b
    rw [h, MvPolynomial.map_C, h]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]

/- English proof (translation)
Establish `hs : (MvPolynomial.map (starRingEnd ℂ) p).support = p.support` using `MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective`. Unfold `Formalism.REAL.fockF`. Rewrite using `[hs]`. Establish `h1 : ∑ m ∈ p.support, MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) p) * star (MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) q)) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) = ∑ m ∈ p.support ∪ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) …`. Use `Finset.sum_subset_zero_on_sdiff Finset.subset_union_left ?_ ?_` and prove the remaining obligations.

Introduce `m hm`. Establish `: MvPolynomial.coeff m p = 0`. Simplify using `using (Finset.mem_sdiff.1 hm).2`. Simplify using `[this]`. Introduce `m _`.

Simplify using `only [MvPolynomial.coeff_map]`. Simplify using `[mul_comm]`. Establish `h2 : ∑ m ∈ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) = ∑ m ∈ p.support ∪ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)`. Use `Finset.sum_subset_zero_on_sdiff Finset.subset_union_right ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `m hm`.

Establish `: MvPolynomial.coeff m q = 0`. Simplify using `using (Finset.mem_sdiff.1 hm).2`. Simplify using `[this]`. Rewrite using `[h1, h2]`.
-/
theorem fockF_conj {σ : Type} (p q : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) =
      Formalism.REAL.fockF q p := by
  classical
  have hs : (MvPolynomial.map (starRingEnd ℂ) p).support = p.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  unfold Formalism.REAL.fockF
  rw [hs]
  have h1 : ∑ m ∈ p.support, MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) p) *
        star (MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) q)) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_left ?_ ?_
    · intro m hm
      have : MvPolynomial.coeff m p = 0 := by
        simpa using (Finset.mem_sdiff.1 hm).2
      simp [this]
    · intro m _
      simp only [MvPolynomial.coeff_map]
      simp [mul_comm]
  have h2 : ∑ m ∈ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
      ∑ m ∈ p.support ∪ q.support, MvPolynomial.coeff m q * star (MvPolynomial.coeff m p) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
    refine Finset.sum_subset_zero_on_sdiff Finset.subset_union_right ?_ (fun _ _ => rfl)
    intro m hm
    have : MvPolynomial.coeff m q = 0 := by
      simpa using (Finset.mem_sdiff.1 hm).2
    simp [this]
  rw [h1, h2]

/- English proof (translation)
Introduce `n lam`. Use `⟨fun p hp => conj_mem_delSq lam hp, conj_rowAct, fun p q => ?_⟩` and prove the remaining obligations. Rewrite using `[normFock, normFock, fockF_conj]`.
-/
theorem conj_coefficients : ∀ (n : ℕ) (lam : DomWeight n), (∀ p ∈ delSq ℂ n lam, MvPolynomial.map (starRingEnd ℂ) p ∈ delSq ℂ n lam) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ), MvPolynomial.map (starRingEnd ℂ) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) = Formalism.GradedWeylDivisibility.rowAct ℂ (g.map (starRingEnd ℂ)) (MvPolynomial.map (starRingEnd ℂ) p)) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) ℂ, normFock lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = normFock lam q p := by
  intro n lam
  refine ⟨fun p hp => conj_mem_delSq lam hp, conj_rowAct, fun p q => ?_⟩
  rw [normFock, normFock, fockF_conj]

end GlobalTheory.ConjCoeff
