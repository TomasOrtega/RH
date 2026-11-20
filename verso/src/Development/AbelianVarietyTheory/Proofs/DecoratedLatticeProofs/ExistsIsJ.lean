import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
import Formalism.LocalToGlobal.HermitianForms.TiedBrInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModuleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHarishChandraParamRevEqWeylWeightTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.Top

/- English proof (translation)
Introduce `D u M`. Distinguish the cases in `hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i`. Use `swap`. Conclude with `⟨0, fun h => absurd h hsg⟩`. Establish `hAP : GlobalTheory.DefLift.AllPlus M` using `GlobalTheory.DefLift.allPlus_of_le (Ptw D) (Nat.sub_le _ _) M`.

Establish `hε : ∀ τ, M.ε τ = allPos D.sp.X'.rank` using `fun τ => funext fun a => hAP τ a`. Establish `hmod` using `fun τ => GlobalTheory.CompactModel.model_allPos D D.sp.X' _ M τ (hε τ)`. Establish `hpar` using `GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top D u M hsg`. Establish `hpl : ∀ τ, ∃ (j : M.H τ →ₗ[ℂ] MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ (M.H τ)), (∀ ξ, j ξ ∈ delSq ℂ _ (sgT u τ)) ∧ (∀ p ∈ delSq ℂ _ (sgT u τ), ∃ ξ, j ξ = p) ∧ (∀ a a', normFock (sgT u τ) (j (b a)) (j (b a')) = if a = a' …` using `fun τ => by`. Use `(hmod τ).1` as an intermediate fact.

Conclude with `GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module _ _ (rankP D) (sgT u τ) (M.H τ) (M.σ τ) (M.lam τ) (hmod τ).2.2.1 (hmod τ).2.2.2 (hpar τ)`. Use `choose jH d bH hj1 hj2 hj3 hj4 using hpl`. Take `⟨Jt, hJi, hJr, hJt⟩` from `GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span D.what₂.Tau (D.R.N D.R.m - 1) (sgT u) (fun τ => M.sm τ) (fun τ => jH τ ∘ₗ (M.sm τ).subtype) d (fun τ => (bH τ).map (LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm) (fun τ ξ => hj1 τ _) (fun τ p hp => by`. Take `⟨ξ, hξ⟩` from `hj2 τ p hp`. Conclude with `⟨(LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm ξ, by simpa using hξ⟩)`.

Use the proof step `(fun τ a a' => by simpa using hj3 τ a a')`. Use `set h := rankP D with hh`. Set `rd : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ` to `fun A => A.reindex (finCongr h) (finCongr h)`. Set `fr' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ` to `fun τ => rd (M.fr τ)`. Establish `hfr' : ∀ τ, IsUnit (fr' τ).det` using `fun τ => by`.

Simplify using `only [fr', rd, Matrix.det_reindex_self]`. Conclude with `GlobalTheory.DefLift.fr_det M τ`. Use `⟨(fnOf (gramC (gramP D) (embT D)) (shiftOf (sgT u)) fr') ∘ₗ Jt, fun _ => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(Formalism.L2.Forms.fnOf_injective _ _ _ hfr').comp hJi`. Rewrite using `[LinearMap.range_comp, hJr]`.

Conclude with `GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC _ _ _ _ _ hfr'`. Introduce `τ g hg v w hw y y' hy classical`. Take `⟨-, -, heval⟩` from `GlobalTheory.FockTen.nfAll_ten D.what₂.Tau (D.R.N D.R.m - 1) (sgT u)`. Simplify using `only [LinearMap.comp_apply, hJt, heval]`. Use `Finset.prod_congr rfl fun ρ _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Establish `hyτ : y.1 ρ = rd g * y'.1 ρ` using `by rw [hy ρ, Function.update_self]`. Use `set mk := M.fr ρ * g * (M.fr ρ)⁻¹ with hmk`. Establish `hwm : ((Function.update v ρ w ρ : M.sm ρ) : M.H ρ) = M.σ ρ mk (v ρ)`.

Rewrite using `[Function.update_self]`. Conclude with `hw`. Establish `hmk_u : mk ∈ Matrix.unitaryGroup (Fin D.sp.X'.rank) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Establish `hg' : gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g = (M.fr ρ)ᴴ * M.fr ρ` using `by rw [← hAP.gram]; exact hg`.

Establish `e1 : M.fr ρ * (M.fr ρ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (GlobalTheory.DefLift.fr_det M ρ)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hmk, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * (M.fr ρ * (M.fr ρ)⁻¹) := by`. Rewrite using `[hg']`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [e1, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `hrdmul : ∀ A B, rd (A * B) = rd A * rd B` using `fun A B => by`. Simplify using `only [rd, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`. Establish `hgn_u : rd mk ∈ Matrix.unitaryGroup _ ℂ`.

Rewrite `hmk_u`, the goal using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Establish `: (rd mk)ᴴ = rd mkᴴ` using `by simp only [rd, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]`. Rewrite using `[this, ← hrdmul, hmk_u]`. Simplify using `only [rd, Matrix.reindex_apply, Matrix.submatrix_one_equiv]`. Establish `hsub : (rd mk).submatrix (Fin.cast h) (Fin.cast h) = mk`.

Use extensionality with `i j`. Simplify using `[rd, Matrix.reindex_apply]`. Establish `hrd : rd mk = fr' ρ * rd g * (fr' ρ)⁻¹`. Simplify using `only [hmk, hrdmul, fr']`. Use `congr 1`.

Simplify using `only [rd, Matrix.inv_reindex]`. Establish `key` using `hj4 ρ (rd mk) hgn_u (v ρ)`. Rewrite `key` using `[hsub]`. Simplify using `only [Submodule.coe_subtype]`. Rewrite using `[hwm, key]`.

Establish `hoU : IsUnit ((fr' ρ)⁻¹).det`. Rewrite using `[Matrix.det_nonsing_inv]`. Conclude with `(hfr' ρ).ringInverse`. Establish `hab : y.1 ρ = (fr' ρ)⁻¹ * rd mk * ((fr' ρ)⁻¹)⁻¹ * y'.1 ρ`. Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ), hrd, hyτ]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ)]`. Establish `hfe` using `GlobalTheory.TenTypes.factor_eq (rd mk) (fr' ρ)⁻¹ (y.1 ρ) (y'.1 ρ) hgn_u hoU (shiftOf (sgT u) ρ) (jH ρ (v ρ)) hab`. Rewrite `hfe` using `[Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ)]`. Conclude with `hfe`.

Establish `hyρ : y.1 ρ = y'.1 ρ` using `by rw [hy ρ, Function.update_of_ne hρ, Matrix.one_mul]`. Rewrite using `[hyρ]`. Simplify using `only [Submodule.coe_subtype, Function.update_of_ne hρ]`.
-/
theorem exists_isJ : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), ∃ j : SmT M →ₗ[ℂ] (FrP D → ℂ), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → IsJ u M j := by
  intro D u M
  by_cases hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i
  swap
  · exact ⟨0, fun h => absurd h hsg⟩
  have hAP : GlobalTheory.DefLift.AllPlus M := GlobalTheory.DefLift.allPlus_of_le (Ptw D) (Nat.sub_le _ _) M
  have hε : ∀ τ, M.ε τ = allPos D.sp.X'.rank := fun τ => funext fun a => hAP τ a
  have hmod := fun τ => GlobalTheory.CompactModel.model_allPos D D.sp.X' _ M τ (hε τ)
  have hpar := GlobalTheory.T.neg_harishChandraParam_rev_eq_weylWeight_top D u M hsg
  have hpl : ∀ τ, ∃ (j : M.H τ →ₗ[ℂ] MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) (d : ℕ)
      (b : Module.Basis (Fin d) ℂ (M.H τ)), (∀ ξ, j ξ ∈ delSq ℂ _ (sgT u τ)) ∧
      (∀ p ∈ delSq ℂ _ (sgT u τ), ∃ ξ, j ξ = p) ∧
      (∀ a a', normFock (sgT u τ) (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧
      ∀ g ∈ Matrix.unitaryGroup (Fin (D.R.N D.R.m - 1)) ℂ, ∀ ξ,
        j (M.σ τ (g.submatrix (Fin.cast (rankP D)) (Fin.cast (rankP D))) ξ) =
          (g.det ^ (-(sgT u τ).detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := fun τ => by
    have := (hmod τ).1
    exact GlobalTheory.T.finite_dim_unitary_K_type_eq_dual_weyl_module _ _ (rankP D) (sgT u τ) (M.H τ) (M.σ τ) (M.lam τ) (hmod τ).2.2.1 (hmod τ).2.2.2 (hpar τ)
  choose jH d bH hj1 hj2 hj3 hj4 using hpl
  obtain ⟨Jt, hJi, hJr, hJt⟩ := GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span D.what₂.Tau (D.R.N D.R.m - 1) (sgT u) (fun τ => M.sm τ)
    (fun τ => jH τ ∘ₗ (M.sm τ).subtype) d (fun τ => (bH τ).map (LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm)
    (fun τ ξ => hj1 τ _) (fun τ p hp => by
      obtain ⟨ξ, hξ⟩ := hj2 τ p hp
      exact ⟨(LinearEquiv.ofTop (M.sm τ) (hmod τ).2.1).symm ξ, by simpa using hξ⟩)
    (fun τ a a' => by simpa using hj3 τ a a')

  set h := rankP D with hh
  let rd : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ :=
    fun A => A.reindex (finCongr h) (finCongr h)
  let fr' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ := fun τ => rd (M.fr τ)
  have hfr' : ∀ τ, IsUnit (fr' τ).det := fun τ => by
    simp only [fr', rd, Matrix.det_reindex_self]
    exact GlobalTheory.DefLift.fr_det M τ
  refine ⟨(fnOf (gramC (gramP D) (embT D)) (shiftOf (sgT u)) fr') ∘ₗ Jt, fun _ => ⟨?_, ?_, ?_⟩⟩
  · exact (Formalism.L2.Forms.fnOf_injective _ _ _ hfr').comp hJi
  · rw [LinearMap.range_comp, hJr]
    exact GlobalTheory.ValueSpaceCoordinates.map_fnOf_eq_ValC _ _ _ _ _ hfr'
  · intro τ g hg v w hw y y' hy
    classical
    obtain ⟨-, -, heval⟩ := GlobalTheory.FockTen.nfAll_ten D.what₂.Tau (D.R.N D.R.m - 1) (sgT u)
    simp only [LinearMap.comp_apply, hJt, heval]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases hρ : ρ = τ
    · subst hρ
      have hyτ : y.1 ρ = rd g * y'.1 ρ := by rw [hy ρ, Function.update_self]
      set mk := M.fr ρ * g * (M.fr ρ)⁻¹ with hmk
      have hwm : ((Function.update v ρ w ρ : M.sm ρ) : M.H ρ) = M.σ ρ mk (v ρ) := by
        rw [Function.update_self]; exact hw
      have hmk_u : mk ∈ Matrix.unitaryGroup (Fin D.sp.X'.rank) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
        have hg' : gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g = (M.fr ρ)ᴴ * M.fr ρ := by rw [← hAP.gram]; exact hg
        have e1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (GlobalTheory.DefLift.fr_det M ρ)
        calc mkᴴ * mk = ((M.fr ρ)⁻¹)ᴴ * (gᴴ * ((M.fr ρ)ᴴ * M.fr ρ) * g) * (M.fr ρ)⁻¹ := by
              simp only [hmk, Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * (M.fr ρ * (M.fr ρ)⁻¹) := by
              rw [hg']; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = 1 := by rw [e1, Matrix.conjTranspose_one, Matrix.one_mul]
      have hrdmul : ∀ A B, rd (A * B) = rd A * rd B := fun A B => by
        simp only [rd, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
      have hgn_u : rd mk ∈ Matrix.unitaryGroup _ ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmk_u ⊢
        have : (rd mk)ᴴ = rd mkᴴ := by simp only [rd, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
        rw [this, ← hrdmul, hmk_u]
        simp only [rd, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      have hsub : (rd mk).submatrix (Fin.cast h) (Fin.cast h) = mk := by
        ext i j; simp [rd, Matrix.reindex_apply]
      have hrd : rd mk = fr' ρ * rd g * (fr' ρ)⁻¹ := by
        simp only [hmk, hrdmul, fr']
        congr 1
        simp only [rd, Matrix.inv_reindex]
      have key := hj4 ρ (rd mk) hgn_u (v ρ)
      rw [hsub] at key
      simp only [Submodule.coe_subtype]
      rw [hwm, key]
      have hoU : IsUnit ((fr' ρ)⁻¹).det := by
        rw [Matrix.det_nonsing_inv]; exact (hfr' ρ).ringInverse
      have hab : y.1 ρ = (fr' ρ)⁻¹ * rd mk * ((fr' ρ)⁻¹)⁻¹ * y'.1 ρ := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ), hrd, hyτ]
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (hfr' ρ)]
      have hfe := GlobalTheory.TenTypes.factor_eq (rd mk) (fr' ρ)⁻¹ (y.1 ρ) (y'.1 ρ) hgn_u hoU (shiftOf (sgT u) ρ) (jH ρ (v ρ)) hab
      rw [Matrix.nonsing_inv_nonsing_inv _ (hfr' ρ)] at hfe
      exact hfe
    · have hyρ : y.1 ρ = y'.1 ρ := by rw [hy ρ, Function.update_of_ne hρ, Matrix.one_mul]
      rw [hyρ]
      simp only [Submodule.coe_subtype, Function.update_of_ne hρ]

end GlobalTheory.Core.Rk.Top
