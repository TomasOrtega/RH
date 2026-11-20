import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.DetTor

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Rewrite using `[Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det x).2 hx), det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul]`. Use `congr 1`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_conj_diag_exp {n : ℕ} {x : Matrix (Fin n) (Fin n) ℂ} (hx : IsUnit x.det) (t : Fin n → ℝ) (k : ℤ) :
    (x * diagonal (fun a => cexp ((t a : ℂ) * I)) * x⁻¹).det ^ k = cexp (((∑ a, (k : ℝ) * t a : ℝ) : ℂ) * I) := by
  rw [Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det x).2 hx), det_diagonal, ← Complex.exp_sum,
    ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Establish `R : GlobalTheory.SmoothForms.RealPoints C.θ T` using `(GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T`. Establish `hu` using `GlobalTheory.HolRead.AdExt.conj_mem_unitary (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ) (hB ρ) (by unfold sgnM; exact GlobalTheory.HolRead.AdExt.diag_unitary _ t)`. Establish `hk` using `GlobalTheory.HolRead.AdExt.atTau_spec R ρ hu`. Establish `key : ∀ ρ', (compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t))).det ^ m ρ' = (if ρ' = ρ then cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) else 1) * (compAt C.θ ρ' (Formalism.L2.Theta.mt T g)).det ^ m ρ'`. Introduce `ρ'`.

Establish `hm : compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t)) = compAt C.θ ρ' (Formalism.L2.Theta.mt T g) * compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t))` using `R.2.2.2.1 g _ ρ'`. Rewrite using `[hm, det_mul, mul_zpow, mul_comm]`. Use `congr 1`. Distinguish the cases in `c : ρ' = ρ`. Substitute `c` using the available equality.

Rewrite using `[if_pos rfl]`. Establish `h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ' t)) = B ρ' * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ')⁻¹` using `hk.2.1`. Rewrite using `[h1]`. Conclude with `det_conj_diag_exp (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ') t (m ρ')`. Rewrite using `[if_neg c]`.

Establish `h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) = 1` using `hk.2.2 ρ' c`. Rewrite using `[h1, det_one, _root_.one_zpow]`. Unfold `detPow`. Rewrite using `[Finset.prod_congr rfl fun ρ' _ => key ρ', Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ρ, if_pos (Finset.mem_univ _)]`.
-/
theorem detPow_mul_torAt (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (m : D.what₂.Tau → ℤ)
    (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T) :
    detPow C.θ T m (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * detPow C.θ T m g := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu := GlobalTheory.HolRead.AdExt.conj_mem_unitary (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ) (hB ρ)
    (by unfold sgnM; exact GlobalTheory.HolRead.AdExt.diag_unitary _ t)
  have hk := GlobalTheory.HolRead.AdExt.atTau_spec R ρ hu
  have key : ∀ ρ', (compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t))).det ^ m ρ' =
      (if ρ' = ρ then cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) else 1) *
        (compAt C.θ ρ' (Formalism.L2.Theta.mt T g)).det ^ m ρ' := by
    intro ρ'
    have hm : compAt C.θ ρ' (Formalism.L2.Theta.mt T (g * torAt C.θ T B ρ t)) =
        compAt C.θ ρ' (Formalism.L2.Theta.mt T g) * compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) :=
      R.2.2.2.1 g _ ρ'
    rw [hm, det_mul, mul_zpow, mul_comm]
    congr 1
    by_cases c : ρ' = ρ
    · subst c
      rw [if_pos rfl]
      have h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ' t)) =
          B ρ' * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ')⁻¹ := hk.2.1
      rw [h1]
      exact det_conj_diag_exp (GlobalTheory.AdSpan.ConjHol.isUnit_det_B C hB ρ') t (m ρ')
    · rw [if_neg c]
      have h1 : compAt C.θ ρ' (Formalism.L2.Theta.mt T (torAt C.θ T B ρ t)) = 1 := hk.2.2 ρ' c
      rw [h1, det_one, _root_.one_zpow]
  unfold detPow
  rw [Finset.prod_congr rfl fun ρ' _ => key ρ', Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ ρ,
    if_pos (Finset.mem_univ _)]

/- English proof (translation)
The claim follows from `detPow_mul_torAt`.
-/
example : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), detPow C.θ T m (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * detPow C.θ T m g := detPow_mul_torAt

end GlobalTheory.AdSpan.DetTor

end
