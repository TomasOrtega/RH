import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.FockTen

/- English proof (translation)
Rewrite using `[Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]`. Unfold `Formalism.REAL.fockF`. Rewrite using `[Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [Formalism.L2.DIV.mfact]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m _ hm`. Establish `hf : f.coeff m = 0` using `by simpa [MvPolynomial.mem_support_iff] using hm`. Rewrite using `[hf, zero_mul, zero_mul]`.
-/
theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    have hf : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [hf, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[fockF_eq_fockL]`. Use `show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _`. Rewrite using `[Formalism.L2.DIV.fk_fock_prod]`. Conclude with `Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm`.
-/
theorem fockF_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (ten f) (ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [fockF_eq_fockL]
  show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _
  rw [Formalism.L2.DIV.fk_fock_prod]
  exact Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm

/- English proof (translation)
Introduce `h0`. Establish `h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1` using `bridge_normFock_extremal_holds n l`. Rewrite `h1` using `[normFock, h0, div_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem fockF_extremal_ne {n : ℕ} (l : DomWeight n) : Formalism.REAL.fockF (extremal ℂ n l) (extremal ℂ n l) ≠ 0 := by
  intro h0
  have h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1 := bridge_normFock_extremal_holds n l
  rw [normFock, h0, div_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
Introduce `ι _ n lam`. Establish `hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)`. Use `⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩` and prove the remaining obligations. Rewrite using `[nfAll, fockF_ten]`. Simplify using `only [normFock]`.

Rewrite using `[Finset.prod_div_distrib]`. Rewrite `hp` using `[nfAll, div_eq_zero_iff]`. Break down `hp with hp | hp` into its components or cases. Assume the negation of the conclusion as `hne`. Conclude with `(@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp`.

Conclude with `absurd hp hden`. Use `show (∏ τ, (M τ * y.1 τ).det ^ s τ) * MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_rename]`.

Both sides reduce to the same expression.
-/
theorem nfAll_ten : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  intro ι _ n lam
  have hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)
  refine ⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩
  · rw [nfAll, fockF_ten]
    simp only [normFock]
    rw [Finset.prod_div_distrib]
  · rw [nfAll, div_eq_zero_iff] at hp
    rcases hp with hp | hp
    · by_contra hne
      exact (@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp
    · exact absurd hp hden
  · show (∏ τ, (M τ * y.1 τ).det ^ s τ) *
        MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_rename]
    rfl

end GlobalTheory.FockTen
