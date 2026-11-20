import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

namespace GlobalTheory.TranslLin

open PowerSeries

/- English proof (translation)
Simplify using `only [coef1]`. Rewrite using `[iteratedDeriv_const_mul_field, mul_div_assoc]`.
-/
theorem taylorCoeffAtZero_const_mul (F : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coef1 (fun z => c * F z) n = c * coef1 F n := by
  simp only [coef1]
  rw [iteratedDeriv_const_mul_field, mul_div_assoc]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [coef1]`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Establish `hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z)` using `by fun_prop`.

Rewrite using `[GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]`.
-/
theorem taylorCoeffAtZero_linearCombination {ι : Type} (s : Finset ι) (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (hφ : ∀ k, Differentiable ℂ (φ k)) (n : ℕ) :
    coef1 (fun z => ∑ k ∈ s, c k * φ k z) n = ∑ k ∈ s, c k * coef1 (φ k) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hd : Differentiable ℂ (fun z => ∑ k ∈ s, c k * φ k z) := by
      fun_prop
    rw [GlobalTheory.SerTransport.taylorCoeff_add_entire ((hφ a).const_mul (c a)) hd, taylorCoeffAtZero_const_mul, ih]

/- English proof (translation)
Take `⟨π, hπ⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ) (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))`. Conclude with `⟨π, fun q => LinearMap.congr_fun hπ q⟩`.
-/
theorem exists_retraction : ∃ π : ℂ →ₗ[Qbar] Qbar, ∀ q : Qbar, π (q : ℂ) = q := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qbar ℂ)
    (LinearMap.ker_eq_bot.2 (fun x y h => Subtype.val_injective h))
  exact ⟨π, fun q => LinearMap.congr_fun hπ q⟩

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
theorem lamC_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {y : ℂ} (h : y ∈ Qbar) :
    lamC lam y = lam ⟨y, h⟩ := dif_pos h

/- English proof (translation)
Introduce `p _ g ι _ φ c E hE hφ hEq`. Take `⟨π, hπ⟩` from `exists_retraction`. Use `⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩` and prove the remaining obligations. Establish `hE' : E = fun z => ∑ k, c k * φ k z` using `funext hEq`. Establish `key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) = ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar)`.

Introduce `n`. Establish `h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n`. Rewrite using `[hE']`. Conclude with `taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n`. Establish `h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n)` using `congrArg π h1`.

Rewrite `h2` using `[hπ, map_sum]`. Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k`. Rewrite using `[Algebra.smul_def, mul_comm]`.

Both sides reduce to the same expression. Rewrite using `[e, map_smul, smul_eq_mul, mul_comm]`. Establish `hser : GL3Theta.ser1 g.lam E = ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k)`. Use extensionality with `n`. Rewrite using `[GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n), GlobalTheory.SerTransport.lamC_coe]`. Establish `hs` using `HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))`. Simplify using `only [GlobalTheory.SerTransport.atU_eq, hser]`. Simplify using `only [← coe_substAlgHom hs, map_sum, map_mul]`.

Simplify using `only [coe_substAlgHom, subst_C]`. Both sides reduce to the same expression.
-/
theorem transl_lin : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (ι : Type) [Fintype ι] (φ : ι → ℂ → ℂ) (c : ι → ℂ)
    (E : ℂ → ℂ), AlgEnt E → (∀ k, AlgEnt (φ k)) → (∀ z, E z = ∑ k, c k * φ k z) →
      ∃ a : ι → ℂ, (∀ k, a k ∈ Qbar) ∧ g.atU E = ∑ k, PowerSeries.C (lamC g.lam (a k)) * g.atU (φ k) := by
  intro p _ g ι _ φ c E hE hφ hEq
  obtain ⟨π, hπ⟩ := exists_retraction
  refine ⟨fun k => ((π (c k) : Qbar) : ℂ), fun k => (π (c k)).2, ?_⟩
  have hE' : E = fun z => ∑ k, c k * φ k z := funext hEq
  have key : ∀ n, (⟨coef1 E n, hE.2 n⟩ : Qbar) =
      ∑ k, π (c k) * (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) := by
    intro n
    have h1 : coef1 E n = ∑ k, c k * coef1 (φ k) n := by
      rw [hE']; exact taylorCoeffAtZero_linearCombination Finset.univ φ c (fun k => (hφ k).1) n
    have h2 : π ((⟨coef1 E n, hE.2 n⟩ : Qbar) : ℂ) = π (∑ k, c k * coef1 (φ k) n) :=
      congrArg π h1
    rw [hπ, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : c k * coef1 (φ k) n = (⟨coef1 (φ k) n, (hφ k).2 n⟩ : Qbar) • c k := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have hser : GL3Theta.ser1 g.lam E =
      ∑ k, C (lamC g.lam ((π (c k) : Qbar) : ℂ)) * GL3Theta.ser1 g.lam (φ k) := by
    ext n
    rw [GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam (hE.2 n), key n, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, coeff_C_mul, GlobalTheory.SerTransport.coeff_padicTransportSeries, lamC_of g.lam ((hφ k).2 n),
      GlobalTheory.SerTransport.lamC_coe]
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  simp only [GlobalTheory.SerTransport.atU_eq, hser]
  simp only [← coe_substAlgHom hs, map_sum, map_mul]
  simp only [coe_substAlgHom, subst_C]
  rfl

end GlobalTheory.TranslLin
