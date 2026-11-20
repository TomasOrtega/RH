import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartialStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierColumnTwiceNegColumnStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinearStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelWeylElementEqPartialFourierStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

/- English proof (translation)
Take `⟨A, u, c, l⟩` from `Y`. Simplify using `only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]`. Apply the tactic sequence `constructor <;> funext i <;> ring`.
-/
theorem rowMap_mul (g h : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) :
    rowMap (g * h) Y = rowMap h (rowMap g Y) := by
  obtain ⟨A, u, c, l⟩ := Y
  simp only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> ring

/- English proof (translation)
Take `⟨A, u, c, l⟩` from `Y`. Simplify using `[rowMap]`.
-/
theorem rowMap_one (Y : Gl r F) : rowMap (1 : SpecialLinearGroup (Fin 2) F) Y = Y := by
  obtain ⟨A, u, c, l⟩ := Y
  simp [rowMap]

/- English proof (translation)
Unfold `rowMap`. Use `fun_prop`.
-/
theorem continuous_rowMap (g : SpecialLinearGroup (Fin 2) F) : Continuous (rowMap (r := r) g) := by
  unfold rowMap
  fun_prop

/- English proof (translation)
Set `e : Gl r F ≃ₜ Gl r F` to `{ toFun := rowMap g, invFun := rowMap g⁻¹ left_inv := fun Y => by simp [← rowMap_mul, rowMap_one] right_inv := fun Y => by simp [← rowMap_mul, rowMap_one] continuous_toFun := continuous_rowMap g, continuous_invFun := continuous_rowMap g⁻¹ }`. Conclude with `⟨hh.1.comp_continuous (continuous_rowMap g), hh.2.comp_homeomorph e⟩`.
-/
theorem isTest_rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (hh : IsTest h) : IsTest (rowAct g h) := by
  let e : Gl r F ≃ₜ Gl r F :=
    { toFun := rowMap g, invFun := rowMap g⁻¹
      left_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      right_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      continuous_toFun := continuous_rowMap g, continuous_invFun := continuous_rowMap g⁻¹ }
  exact ⟨hh.1.comp_continuous (continuous_rowMap g), hh.2.comp_homeomorph e⟩

end GlobalTheory.JR.WeilMix

open GlobalTheory.JR.WeilMix in
/- English proof (translation)
Introduce `F E _ _ _ _ _ r M ψ hψ`. Establish `hT` using `GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn F E r M ψ hψ`. Establish `hI` using `GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ`. Establish `hL` using `GlobalTheory.T.mixedModelPartialFourier_linear F E r M ψ hψ`. Establish `hW` using `GlobalTheory.T.mixedModel_weylElement_eq_partialFourier F E r M ψ hψ`.

Establish `hψc : IsLocallyConstant (fun x : F => ψ x)` using `((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1`. Establish `h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f`. Introduce `f hf`. Rewrite using `[hI _ (hT _ (hT _ hf)), hI _ hf]`. Use function extensionality and compare the values at `Y`.

Simplify using `[negB]`. Use `⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `g f hf`. Conclude with `hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))`. Introduce `f hf`.

Establish `: rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f`. Use function extensionality and compare the values at `Y`. Simplify using `[rowAct, rowMap_one]`. Simplify using `only [weil, this]`. Conclude with `h4 f hf`.

Introduce `g h f hf`. Simplify using `only [weil]`. Rewrite using `[h4 _ (isTest_rowAct h _ (hT _ hf))]`. Use `congr 3`. Use function extensionality and compare the values at `Y`.

Simplify using `[rowAct, rowMap_mul]`. Introduce `g c f f' hf hf'`. Establish `hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b`. Introduce `a b`. Use function extensionality and compare the values at `Y`.

Simplify using `[rowAct]`. Simplify using `only [weil]`. Rewrite using `[hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')), hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))), hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]`. Introduce `f hf`. Use `⟨fun t Y => ?_, ?_⟩` and prove the remaining obligations.

Set `ft : Gl r F → ℂ` to `fun Y => ψ (t * mom Y 0) * f Y`. Establish `hft : IsTest ft`. Use `⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩` and prove the remaining obligations. Simplify using `only [mom, pow_zero, Matrix.one_mulVec]`. Use `fun_prop`.

Establish `key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft`. Use function extensionality and compare the values at `Y`. Take `⟨A, u, c, l⟩` from `Y`. Simplify using `only [rowAct, rowMap, ptrB, nS, ft]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Simplify using `only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, mul_zero, add_zero, mul_one, zero_add, mom, pow_zero, Matrix.one_mulVec]`. Establish `hu : (fun i => c i * t + u i) = t • c + u` using `by funext i; simp [mul_comm]`. Rewrite using `[hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _`. Rewrite using `[key, h4 ft hft]`. Use `show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _`. Rewrite using `[hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]`. Conclude with `hW f hf`.
-/
theorem GlobalTheory.JR.weil_repG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  intro F E _ _ _ _ _ r M ψ hψ
  have hT := GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn F E r M ψ hψ
  have hI := GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ
  have hL := GlobalTheory.T.mixedModelPartialFourier_linear F E r M ψ hψ
  have hW := GlobalTheory.T.mixedModel_weylElement_eq_partialFourier F E r M ψ hψ
  have hψc : IsLocallyConstant (fun x : F => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  have h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f := by
    intro f hf
    rw [hI _ (hT _ (hT _ hf)), hI _ hf]
    funext Y; simp [negB]
  refine ⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    exact hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))
  · intro f hf
    have : rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f := by
      funext Y; simp [rowAct, rowMap_one]
    simp only [weil, this]
    exact h4 f hf
  · intro g h f hf
    simp only [weil]
    rw [h4 _ (isTest_rowAct h _ (hT _ hf))]
    congr 3
    funext Y; simp [rowAct, rowMap_mul]
  · intro g c f f' hf hf'
    have hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b := by
      intro a b; funext Y; simp [rowAct]
    simp only [weil]
    rw [hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')),
      hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))),
      hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]
  · intro f hf
    refine ⟨fun t Y => ?_, ?_⟩
    · let ft : Gl r F → ℂ := fun Y => ψ (t * mom Y 0) * f Y
      have hft : IsTest ft := by
        refine ⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩
        simp only [mom, pow_zero, Matrix.one_mulVec]
        fun_prop
      have key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft := by
        funext Y
        obtain ⟨A, u, c, l⟩ := Y
        simp only [rowAct, rowMap, ptrB, nS, ft]
        congr 1
        funext b
        simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, mul_zero, add_zero,
          mul_one, zero_add, mom, pow_zero, Matrix.one_mulVec]
        have hu : (fun i => c i * t + u i) = t • c + u := by funext i; simp [mul_comm]
        rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c,
          AddChar.map_add_eq_mul]
        ring
      show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _
      rw [key, h4 ft hft]
    · show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _
      rw [hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]
      exact hW f hf
