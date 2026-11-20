import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

/- English proof (translation)
Introduce `V _ _ ι _ m d hm f₀ hc h0 i p`. Establish `hX : ∀ (j : ι) (q : MvPolynomial ι ℂ), polEval m hm f₀ (MvPolynomial.X j * q) = m j (polEval m hm f₀ q)`. Introduce `j q`. Simplify using `[polEval, Module.End.mul_apply]`. Establish `h1 : polEval m hm f₀ 1 = f₀` using `by simp [polEval]`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `hC : (MvPolynomial.C a : MvPolynomial ι ℂ) = a • (1 : MvPolynomial ι ℂ)`. Rewrite using `[MvPolynomial.smul_eq_C_mul, mul_one]`. Rewrite using `[MvPolynomial.pderiv_C, map_zero, hC, map_smul, h1, map_smul, h0, smul_zero]`.

Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X q j hq`. Establish `hv` using `LinearMap.congr_fun (hc i j) (polEval m hm f₀ q)`. Rewrite `hv` using `[LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add]`. Rewrite using `[mul_comm q, MvPolynomial.pderiv_mul, map_add, hX, hX, hq, hv]`.

Use `congr 1`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]`.

Simplify using `[hij]`.
-/
theorem polEval_pderiv :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  intro V _ _ ι _ m d hm f₀ hc h0 i p
  have hX : ∀ (j : ι) (q : MvPolynomial ι ℂ),
      polEval m hm f₀ (MvPolynomial.X j * q) = m j (polEval m hm f₀ q) := by
    intro j q
    simp [polEval, Module.End.mul_apply]
  have h1 : polEval m hm f₀ 1 = f₀ := by simp [polEval]
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : (MvPolynomial.C a : MvPolynomial ι ℂ) = a • (1 : MvPolynomial ι ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [MvPolynomial.pderiv_C, map_zero, hC, map_smul, h1, map_smul, h0, smul_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X q j hq =>
    have hv := LinearMap.congr_fun (hc i j) (polEval m hm f₀ q)
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at hv
    rw [mul_comm q, MvPolynomial.pderiv_mul, map_add, hX, hX, hq, hv]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
      simp [hij]

end GlobalTheory.CCRFock
