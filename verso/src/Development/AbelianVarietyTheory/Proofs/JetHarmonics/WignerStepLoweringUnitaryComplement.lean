import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqContractLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriLoweringStepGlTensorDualStandardStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermExpHasDeriv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorOpContinuousOn
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WignerStepLower

open Formalism.FourierDecayAlt.P

/- English proof (translation)
Establish `h : ContinuousLinearMap.adjoint a v = S.orthogonalProjection (PiLp.single 2 c v)`. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left, ha, PiLp.inner_apply, Finset.sum_eq_single c]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[PiLp.single_apply, Pi.single_apply, hb]`. Simplify using the standard rewrite rules. Rewrite using `[h, ha]`. Both sides reduce to the same expression.
-/
theorem comp_adjoint_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (a : S →L[ℂ] V)
    (ha : ∀ y : S, a y = (y : PiLp 2 (fun _ : Fin k => V)) c) (v : V) :
    a (ContinuousLinearMap.adjoint a v) = S.starProjection (PiLp.single 2 c v) c := by
  have h : ContinuousLinearMap.adjoint a v = S.orthogonalProjection (PiLp.single 2 c v) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left, ha,
      PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [PiLp.single_apply, Pi.single_apply, hb]
    · simp
  rw [h, ha]
  rfl

/- English proof (translation)
Introduce `V _ _ _ n r z π u β L B l hz hT hty hL hu hB hl`. Take `⟨hH, hadj⟩` from `GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hty hL hu hB`. Establish `hR : IsRepW (n + 1) r z π` using `⟨hty.2.1, hty.2.2.1⟩`. Take `⟨πt, hRt, hnt, hft⟩` from `GlobalTheory.tensor_dual_standard V (n + 1) r z π B hz hT hR hty.2.2.2.1 hB`. Establish `hE` using `GlobalTheory.TensorDualDifferential.EB_tensor V (n + 1) r z π B πt hz hT hR hRt hB hft`.

Take `⟨S, hS, hS0, hirr, hcap, hw⟩` from `GlobalTheory.T.pieri_lowering_step_gl_tensor_dual_standard V n (EB π B) (EB πt B) β L l hH hadj hE hl`. Take `⟨π₂, hty₂, hπ₂⟩` from `GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) hz hT hRt hnt hB hS hS0 hirr (by`. Introduce `w y hy`. Rewrite using `[mem_CapSp.1 (hcap hy) w, FrameExtension.prod_Icc_fin]`. Use `congr 1`.

Unfold `cpol shf`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Establish `h1` using `hu j`. Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality.

Rewrite using `[Function.update_self, Function.update_self]`. Move the coercions through the operations in `at h1 ⊢`. Take the linear combination `-h1`. Establish `hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1` using `fun h => hj (Fin.ext (by omega))`. Rewrite using `[Function.update_of_ne hj, Function.update_of_ne hj']`.

Take the linear combination `-h1)`. Set `a : Fin (n + 1) → (S →L[ℂ] V)` to `fun c => (PiLp.proj 2 (fun _ : Fin (n + 1) => V) c).comp S.subtypeL`. Establish `ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c` using `fun _ _ => rfl`. Take `⟨hW, hA⟩` from `GlobalTheory.ContractLinear.wigMap_contract V (n + 1) r z π B S π₂ a hz hT hB (fun y => by`. Simplify using `only [ha]`.

Rewrite using `[← PiLp.norm_sq_eq_of_L2]`. Use the proof step `rfl)`. Use the proof step `(fun h hh y c => by`. Simplify using `only [ha]`. Rewrite using `[hπ₂ h hh y, hft h hh])`.

Use `⟨S, inferInstance, inferInstance, inferInstance, π₂, _, hty₂, hW, fun M v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [hA]`. Rewrite using `[comp_adjoint_apply S (Fin.last n) (a (Fin.last n)) (ha _) v]`. Conclude with `hw M v hv`.
-/
theorem wigner_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l - 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wM L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hty hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hty hL hu hB
  have hR : IsRepW (n + 1) r z π := ⟨hty.2.1, hty.2.2.1⟩
  obtain ⟨πt, hRt, hnt, hft⟩ := GlobalTheory.tensor_dual_standard V (n + 1) r z π B hz hT hR hty.2.2.2.1 hB
  have hE := GlobalTheory.TensorDualDifferential.EB_tensor V (n + 1) r z π B πt hz hT hR hRt hB hft
  obtain ⟨S, hS, hS0, hirr, hcap, hw⟩ := GlobalTheory.T.pieri_lowering_step_gl_tensor_dual_standard V n (EB π B) (EB πt B) β L l hH hadj hE hl
  obtain ⟨π₂, hty₂, hπ₂⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S
    (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - 1)) hz hT hRt hnt hB hS hS0 hirr (by
      intro w y hy
      rw [mem_CapSp.1 (hcap hy) w, FrameExtension.prod_Icc_fin]
      congr 1
      unfold cpol shf
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have h1 := hu j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        push_cast at h1 ⊢
        linear_combination -h1
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        linear_combination -h1)
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun _ _ => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.ContractLinear.wigMap_contract V (n + 1) r z π B S π₂ a hz hT hB
    (fun y => by
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (fun h hh y c => by
      simp only [ha]
      rw [hπ₂ h hh y, hft h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, π₂, _, hty₂, hW, fun M v hv => ?_⟩
  simp only [hA]
  rw [comp_adjoint_apply S (Fin.last n) (a (Fin.last n)) (ha _) v]
  exact hw M v hv

end GlobalTheory.WignerStepLower
