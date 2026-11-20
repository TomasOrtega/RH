import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
open GlobalTheory.KJInf Formalism.L2.Forms Formalism.BasicNotions MvPolynomial

noncomputable section
namespace GlobalTheory.KJInf.ClsVal
variable {ι : Type} [Fintype ι] {a b : ℕ}

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Establish `hm : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) = c • monomial m 1`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Establish `h1 : Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) (monomial m c) = c • monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1))`.

Rewrite using `[hm, map_smul]`. Use `congr 1`. Unfold `Formalism.L2.Ker.jetLin`. Use `(basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ).constr_basis ℂ (fun m : ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) →₀ ℕ => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) : …` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h1, evalAt, smul_eval, eval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]`. Establish `h2 : (∏ i : ι × Fin b × Fin a, (X i : FP ι a b) ^ m (Sum.inr i)) = monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1`. Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]`. Both sides reduce to the same expression. Simplify using `only [Sum.elim_inl, Sum.elim_inr, h2, ← map_pow, ← map_prod, algebraMap_eq]`.

Rewrite using `[show ∀ (u v : ℂ) (q : FP ι a b), C u * (C v * q) = (u * v) • q from fun u v q => by rw [smul_eq_C_mul, C_mul, mul_assoc], map_smul, smul_eq_mul]`. Simplify using `only [Finsupp.comapDomain_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p q hp hq => rw [map_add, evalAt, map_add, ← evalAt, ← evalAt, hp, hq, map_add, map_add]`.
-/
theorem evalAt_jetLin (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) :
    evalAt y' (Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) Q) =
      Λ (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) = c • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have h1 : Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) (monomial m c) =
        c • monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) := by
      rw [hm, map_smul]
      congr 1
      unfold Formalism.L2.Ker.jetLin
      have := (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ).constr_basis ℂ
        (fun m : ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) →₀ ℕ => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      simpa using this
    rw [h1, evalAt, smul_eval, eval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    have h2 : (∏ i : ι × Fin b × Fin a, (X i : FP ι a b) ^ m (Sum.inr i)) =
        monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, h2, ← map_pow, ← map_prod, algebraMap_eq]
    rw [show ∀ (u v : ℂ) (q : FP ι a b), C u * (C v * q) = (u * v) • q from fun u v q => by rw [smul_eq_C_mul, C_mul, mul_assoc], map_smul, smul_eq_mul]
    simp only [Finsupp.comapDomain_apply]
    ring
  | add p q hp hq => rw [map_add, evalAt, map_add, ← evalAt, ← evalAt, hp, hq, map_add, map_add]

/- English proof (translation)
Rewrite using `[subY_eq_subD]`. Conclude with `evalAt_jetLin y' Λ _`.
-/
theorem evalAt_jetMap (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ) (k : ι → ℕ) (P : PY ι a) :
    evalAt y' (Formalism.L2.Ker.jetMap (fun m => Λ (monomial m 1)) k P) =
      Λ (subY hab y' (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ k τ)) := by
  rw [subY_eq_subD]
  exact evalAt_jetLin y' Λ _

/- English proof (translation)
Unfold `CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat`. Use `congr 1`. Use extensionality with `p`. Simplify using `only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]`. Both sides reduce to the same expression.
-/
theorem cSpan_eq_VV' {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

end GlobalTheory.KJInf.ClsVal
