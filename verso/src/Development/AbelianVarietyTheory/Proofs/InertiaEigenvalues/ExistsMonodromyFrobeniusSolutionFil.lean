import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTensorSemistablePeriodRingSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableCommStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Rewrite using `[crisIncl_tmul, LinearMap.lTensor_tmul]`. Simplify using `only [ιV, AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, hι, P.PD_ι]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lTensor_crisIncl_eq_ιV {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR)
    (hι : ∀ b, ι (Polynomial.C b) = P.ιB b) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (w : V ⊗[ℚ_[l]] P.R.B) :
    LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [crisIncl_tmul, LinearMap.lTensor_tmul]
    simp only [ιV, AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, AlgHom.toLinearMap_apply,
      LinearMap.coe_restrictScalars, hι, P.PD_ι]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Introduce `l _ P AI T ι hι K V _ _ x y h`. Take `⟨z₀, hz₀⟩` from `GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective l P V x`. Establish `he : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀ - z₀ - y) = 0`. Establish `h1 : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀) = (l : ℚ_[l]) • phiV P ℚ_[l] V x`. Rewrite using `[← End.mul_apply, monV_phiV, LinearMap.smul_apply, End.mul_apply, hz₀]`.

Rewrite using `[map_sub, map_sub, h1, hz₀, h, sub_self]`. Take `⟨u, hu⟩` from `(GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mp he`. Take `⟨x₁, y₁, hy₁, hx₁, hxy⟩` from `(GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K ℚ_[l] V).1 u (-(LinearMap.lTensor V ι.toLinearMap z₀))`. Use `⟨z₀ + crisIncl P ℚ_[l] V x₁, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : monV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) = 0` using `(GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x₁, rfl⟩`.

Rewrite using `[map_add, hz₀, h0, add_zero]`. Establish `h2 : phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁ = -crisIncl P ℚ_[l] V u`. Rewrite using `[GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V x₁, ← map_sub, ← hx₁, ← map_neg, neg_sub]`. Establish `h3 : phiV P ℚ_[l] V z₀ - z₀ = crisIncl P ℚ_[l] V u + y` using `by rw [hu]; abel`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws. Use `_ = y := by rw [h2, h3]; abel`. Rewrite using `[map_add, lTensor_crisIncl_eq_ιV P ι hι K V x₁]`. Establish `: LinearMap.lTensor V ι.toLinearMap z₀ + ιV (P.PD K) (LL` using `ℚ_[l]) (V := V) x₁ = y₁ := by`.

Rewrite using `[← sub_eq_zero, add_sub_assoc, hxy, add_neg_cancel]`. Rewrite using `[this]`. Conclude with `hy₁`.
-/
theorem solve_mon_phi_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P),
    (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P,
      monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧
      LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  intro l _ P AI T ι hι K V _ _ x y h
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.monodromyTensorSemistablePeriodRing_surjective l P V x
  have he : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀ - z₀ - y) = 0 := by
    have h1 : monV P ℚ_[l] V (phiV P ℚ_[l] V z₀) = (l : ℚ_[l]) • phiV P ℚ_[l] V x := by
      rw [← End.mul_apply, monV_phiV, LinearMap.smul_apply, End.mul_apply, hz₀]
    rw [map_sub, map_sub, h1, hz₀, h, sub_self]
  obtain ⟨u, hu⟩ := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mp he
  obtain ⟨x₁, y₁, hy₁, hx₁, hxy⟩ := (GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline l P AI T K ℚ_[l] V).1 u
    (-(LinearMap.lTensor V ι.toLinearMap z₀))
  refine ⟨z₀ + crisIncl P ℚ_[l] V x₁, ?_, ?_, ?_⟩
  · have h0 : monV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) = 0 := (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x₁, rfl⟩
    rw [map_add, hz₀, h0, add_zero]
  · have h2 : phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁ = -crisIncl P ℚ_[l] V u := by
      rw [GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K V x₁, ← map_sub, ← hx₁, ← map_neg, neg_sub]
    have h3 : phiV P ℚ_[l] V z₀ - z₀ = crisIncl P ℚ_[l] V u + y := by rw [hu]; abel
    calc phiV P ℚ_[l] V (z₀ + crisIncl P ℚ_[l] V x₁) - (z₀ + crisIncl P ℚ_[l] V x₁)
        = (phiV P ℚ_[l] V z₀ - z₀) + (phiV P ℚ_[l] V (crisIncl P ℚ_[l] V x₁) - crisIncl P ℚ_[l] V x₁) := by
          rw [map_add]; abel
      _ = y := by rw [h2, h3]; abel
  · rw [map_add, lTensor_crisIncl_eq_ιV P ι hι K V x₁]
    have : LinearMap.lTensor V ι.toLinearMap z₀ + ιV (P.PD K) (LL := ℚ_[l]) (V := V) x₁ = y₁ := by
      rw [← sub_eq_zero, add_sub_assoc, hxy, add_neg_cancel]
    rw [this]; exact hy₁

end GlobalTheory.PMon
