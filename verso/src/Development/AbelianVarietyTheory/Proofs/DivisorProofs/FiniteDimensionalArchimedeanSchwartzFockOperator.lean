import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.FockKFinStep
open GlobalTheory.ThK.EvAt0.PolD LineDeriv

/- English proof (translation)
Use `conv_lhs => rw [← B.sum_repr b]`. Simplify using `only [lin, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]`. Rewrite using `[Finset.sum_comm]`. Simplify using `[map_sum, map_smul, Finset.mul_sum]`.
-/
theorem lin_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (b x : κ → mixedEmbedding.mixedSpace F) :
    lin b x = ∑ j, (B.repr b j : ℂ) * lin (B j) x := by
  conv_lhs => rw [← B.sum_repr b]
  simp only [lin, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  simp [map_sum, map_smul, Finset.mul_sum]

/- English proof (translation)
Use `conv_lhs => rw [← B.sum_repr a]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_smul, Complex.real_smul]`.
-/
theorem fderiv_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (x) :
    fderiv ℝ f x a = ∑ j, (B.repr a j : ℂ) * fderiv ℝ f x (B j) := by
  conv_lhs => rw [← B.sum_repr a]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Complex.real_smul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sumAt {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (s : Finset ι) (g : ι → SInf F κ) (x) :
    (∑ j ∈ s, g j) x = ∑ j ∈ s, g j x := by simp

/- English proof (translation)
Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Rewrite using `[dOp_apply, fderiv_expand B a f x, lin_expand B b x]`. Simplify using `only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, sumAt, smul_eq_mul, SchwartzMap.lineDerivOp_apply_eq_fderiv, mulOp_apply, Finset.mul_sum, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem dOp_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    dOp a b f = ∑ j, (B.repr a j : ℂ) • ∂_{B j} f -
      (2 * Real.pi * Complex.I : ℂ) • ∑ j, (B.repr b j : ℂ) • mulOp (B j) f := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [dOp_apply, fderiv_expand B a f x, lin_expand B b x]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, sumAt, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, mulOp_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `F _ _ κ _ P hP`. Set `B` to `Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)`. Set `T : Submodule ℂ (SInf F κ)` to `(⨆ j, P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap) ⊔ ⨆ j, P.map (mulOp (B j)).toLinearMap`. Use `haveI : FiniteDimensional ℂ T := by haveI := Submodule.finiteDimensional_iSup (fun j => P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap) haveI := Submodule.finiteDimensional_iSup (fun j => P.map (mulOp (B j)).toLinearMap)`. Conclude with `Submodule.finiteDimensional_sup _ _`.

Use `Submodule.finiteDimensional_of_le (S₂ := T) ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FockKFin.dStep, Submodule.span_le]`. Introduce and unpack `_ ⟨a, b, f, hf, rfl⟩`. Rewrite using `[dOp_expand B]`. Use `Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)` and prove the remaining obligations.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j ⟨f, hf, rfl⟩)`. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem (p := fun j => P.map (mulOp (B j)).toLinearMap) j ⟨f, hf, rfl⟩))`.
-/
theorem dStep_finiteDimensional : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  intro F _ _ κ _ P hP
  let B := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let T : Submodule ℂ (SInf F κ) :=
    (⨆ j, P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap) ⊔ ⨆ j, P.map (mulOp (B j)).toLinearMap
  haveI : FiniteDimensional ℂ T := by
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap)
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (mulOp (B j)).toLinearMap)
    exact Submodule.finiteDimensional_sup _ _
  refine Submodule.finiteDimensional_of_le (S₂ := T) ?_
  rw [GlobalTheory.FockKFin.dStep, Submodule.span_le]
  rintro _ ⟨a, b, f, hf, rfl⟩
  rw [dOp_expand B]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨f, hf, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (p := fun j => P.map (mulOp (B j)).toLinearMap) j ⟨f, hf, rfl⟩))

end GlobalTheory.FockKFinStep
