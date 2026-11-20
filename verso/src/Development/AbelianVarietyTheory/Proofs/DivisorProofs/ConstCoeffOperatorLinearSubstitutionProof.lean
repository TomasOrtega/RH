import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0EqSumOfSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LinChange

open MvPowerSeries GlobalTheory.FGDepth

section Rules

variable {K : Type} [Field K] {σ : Type}

/- English proof (translation)
Unfold `mfact`. Conclude with `Finsupp.prod_fintype _ _ (fun _ => by simp)`.
-/
private theorem mfact_eq_prod_factorial [Fintype σ] (α : σ →₀ ℕ) :
    (mfact α : K) = ∏ x, ((α x).factorial : K) := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

/- English proof (translation)
Rewrite using `[mfact_eq_prod_factorial, mfact_eq_prod_factorial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l), ← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]`. Establish `hrest : ∏ x ∈ Finset.univ.erase l, (((α + Finsupp.single l 1 : σ →₀ ℕ) x).factorial : K) = ∏ x ∈ Finset.univ.erase l, ((α x).factorial : K)`. Use `Finset.prod_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero]`. Rewrite using `[hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mfact_add_single [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : K) = mfact α * ((α l : K) + 1) := by
  rw [mfact_eq_prod_factorial, mfact_eq_prod_factorial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  have hrest : ∏ x ∈ Finset.univ.erase l, (((α + Finsupp.single l 1 : σ →₀ ℕ) x).factorial : K) =
      ∏ x ∈ Finset.univ.erase l, ((α x).factorial : K) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[derivAt0_eq_sum_of_subset (P + Q) g MvPolynomial.support_add, derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)), derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivAt0_add' (P Q : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g := by
  classical
  rw [derivAt0_eq_sum_of_subset (P + Q) g MvPolynomial.support_add,
    derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
    derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Rewrite using `[derivAt0_eq_sum_of_subset (b • P) g MvPolynomial.support_smul, derivAt0, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivAt0_smulP (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (b • P) g = b * derivAt0 P g := by
  classical
  rw [derivAt0_eq_sum_of_subset (b • P) g MvPolynomial.support_smul, derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `derivAt0`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivAt0_smulG (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 P (b • g) = b * derivAt0 P g := by
  unfold derivAt0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPowerSeries.coeff_smul]
  ring

/- English proof (translation)
Unfold `derivAt0`. Repeatedly rewrite using `[map_sum, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem derivAt0_sumG {κ : Type} (s : Finset κ) (P : MvPolynomial σ K) (f : κ → MvPowerSeries σ K) :
    derivAt0 P (∑ i ∈ s, f i) = ∑ i ∈ s, derivAt0 P (f i) := by
  unfold derivAt0
  simp_rw [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[MvPolynomial.C_apply, DepthAdd.derivAt0_monomial, DepthAdd.mfact_zero', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_one]`.
-/
theorem derivAt0_C' (a : K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.C a) g = a * constantCoeff g := by
  rw [MvPolynomial.C_apply, DepthAdd.derivAt0_monomial, DepthAdd.mfact_zero',
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_one]

/- English proof (translation)
Establish `hP : P * MvPolynomial.X l = ∑ α ∈ P.support, MvPolynomial.monomial (α + Finsupp.single l 1) (P.coeff α)` using `by conv_lhs => rw [P.as_sum]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[show (MvPolynomial.X l : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single l 1) 1 from rfl, MvPolynomial.monomial_mul, mul_one]`. Rewrite using `[hP, DepthAdd.derivAt0_sum]`.

Use `conv_rhs => unfold derivAt0`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[DepthAdd.derivAt0_monomial, MvPowerSeries.coeff_pderiv, mfact_add_single]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivAt0_mul_X [Fintype σ] (P : MvPolynomial σ K) (l : σ) (g : MvPowerSeries σ K) :
    derivAt0 (P * MvPolynomial.X l) g = derivAt0 P (pderiv K l g) := by
  classical
  have hP : P * MvPolynomial.X l =
      ∑ α ∈ P.support, MvPolynomial.monomial (α + Finsupp.single l 1) (P.coeff α) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (MvPolynomial.X l : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single l 1) 1 from rfl,
      MvPolynomial.monomial_mul, mul_one]
  rw [hP, DepthAdd.derivAt0_sum]
  conv_rhs => unfold derivAt0
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [DepthAdd.derivAt0_monomial, MvPowerSeries.coeff_pderiv, mfact_add_single]
  ring

/- English proof (translation)
Establish `hs : HasSubst A` using `hasSubst_of_constantCoeff_zero hA`. Establish `h` using `constantCoeff_subst_eq_zero hs hA (f := Ψ - C (constantCoeff Ψ)) (by simp)`. Rewrite `h` using `[subst_sub hs, subst_C, map_sub, constantCoeff_C, sub_eq_zero]`. Conclude with `h`.
-/
private theorem constantCoeff_subst_of_constantCoeff_zero' {K ι Λ : Type} [Field K] [Finite ι] (A : ι → MvPowerSeries Λ K)
    (hA : ∀ l, constantCoeff (A l) = 0) (Ψ : MvPowerSeries ι K) :
    constantCoeff (subst A Ψ) = constantCoeff Ψ := by
  have hs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  have h := constantCoeff_subst_eq_zero hs hA (f := Ψ - C (constantCoeff Ψ)) (by simp)
  rw [subst_sub hs, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_single lam]`. Rewrite using `[Derivation.map_smul, pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]`. Introduce `b _ hb`. Rewrite using `[Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ lam) h`.
-/
private theorem pderiv_sum_smul_X_eq_C {K ι Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (β : Λ → ι → K)
    (lam : Λ) (l : ι) :
    pderiv K lam (∑ lam', β lam' l • (X lam' : MvPowerSeries Λ K)) = C (β lam l) := by
  rw [map_sum, Finset.sum_eq_single lam]
  · rw [Derivation.map_smul, pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro b _ hb
    rw [Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

end Rules

end GlobalTheory.IsoTriv.LinChange

namespace GlobalTheory.IsoTriv

open MvPowerSeries GlobalTheory.FGDepth GlobalTheory.IsoTriv.LinChange

/- English proof (translation)
Unfold `LinSt`. Introduce `K _ _ ι Λ _ _ β P`. Establish `hA0 : ∀ l : ι, constantCoeff (∑ lam, β lam l • (X lam : MvPowerSeries Λ K)) = 0`. Introduce `l`. Simplify using `[MvPowerSeries.smul_eq_C_mul]`.

Proceed by induction on `P using MvPolynomial.induction_on`. Name the introduced variables `a`. Introduce `Ψ`. Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, derivAt0_C', derivAt0_C', constantCoeff_subst_of_constantCoeff_zero' _ hA0]`. Name the introduced variables `p q hp hq`.

Introduce `Ψ`. Rewrite using `[map_add, derivAt0_add', derivAt0_add', hp, hq]`. Name the introduced variables `p lam hp`. Introduce `Ψ`. Establish `hterm : ∀ l : ι, MvPolynomial.aeval (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p * (MvPolynomial.C (β lam l) * MvPolynomial.X l) = β lam l • (MvPolynomial.aeval (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι …`.

Introduce `l`. Rewrite using `[MvPolynomial.smul_eq_C_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul]`. Simplify using `only [MvPolynomial.aeval_X]`.

Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[hterm]`. Rewrite using `[DepthAdd.derivAt0_sum, derivAt0_mul_X, ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hA0, derivAt0_sumG]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[derivAt0_smulP, derivAt0_mul_X, hp, pderiv_sum_smul_X_eq_C, mul_comm _ (C (β lam l)), ← MvPowerSeries.smul_eq_C_mul, derivAt0_smulG]`.
-/
theorem linSt_holds : LinSt := by
  unfold LinSt
  intro K _ _ ι Λ _ _ β P
  classical
  have hA0 : ∀ l : ι, constantCoeff (∑ lam, β lam l • (X lam : MvPowerSeries Λ K)) = 0 := by
    intro l
    simp [MvPowerSeries.smul_eq_C_mul]
  induction P using MvPolynomial.induction_on
  · rename_i a
    intro Ψ
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, derivAt0_C', derivAt0_C',
      constantCoeff_subst_of_constantCoeff_zero' _ hA0]
  · rename_i p q hp hq
    intro Ψ
    rw [map_add, derivAt0_add', derivAt0_add', hp, hq]
  · rename_i p lam hp
    intro Ψ
    have hterm : ∀ l : ι, MvPolynomial.aeval
        (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
          (MvPolynomial.C (β lam l) * MvPolynomial.X l) =
        β lam l • (MvPolynomial.aeval
          (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
            MvPolynomial.X l) := by
      intro l
      rw [MvPolynomial.smul_eq_C_mul]
      ring
    rw [map_mul]
    simp only [MvPolynomial.aeval_X]
    rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [DepthAdd.derivAt0_sum, derivAt0_mul_X,
      ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hA0, derivAt0_sumG]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [derivAt0_smulP, derivAt0_mul_X, hp, pderiv_sum_smul_X_eq_C, mul_comm _ (C (β lam l)), ← MvPowerSeries.smul_eq_C_mul,
      derivAt0_smulG]

end GlobalTheory.IsoTriv
