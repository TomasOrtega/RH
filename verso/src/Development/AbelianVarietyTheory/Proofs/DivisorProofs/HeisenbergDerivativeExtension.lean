import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section

namespace GlobalTheory.ThK.PlaneEv

/- English proof (translation)
Establish `hcomp : ⇑(ei F hd f) = ⇑f ∘ ⇑(insertZerosCLM F hd)` using `rfl`. Use function extensionality and compare the values at `x`. Rewrite using `[ei_apply, hg, hcomp]`. Simplify using `only [dH]`. Establish `hf : DifferentiableAt ℝ (⇑f) (insertZerosCLM F hd x)` using `f.differentiableAt`.

Rewrite using `[fderiv_comp x hf (insertZerosCLM F hd).differentiableAt, ContinuousLinearMap.fderiv]`. Establish `hs : (∑ i, ins0 hd x i * ins0 hd b i) = ∑ i, x i * b i` using `ins0_dotProduct_ins0 hd x b`. Rewrite using `[hs]`. Both sides reduce to the same expression.
-/
theorem ei_dH (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2)
    (a b : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F)
    (f g : SInf F (Fin n × Fin d)) (hg : ⇑g = dH (ins0 hd a) (ins0 hd b) ⇑f) :
    ⇑(ei F hd g) = dH a b ⇑(ei F hd f) := by
  classical
  have hcomp : ⇑(ei F hd f) = ⇑f ∘ ⇑(insertZerosCLM F hd) := rfl
  funext x
  rw [ei_apply, hg, hcomp]
  simp only [dH]
  have hf : DifferentiableAt ℝ (⇑f) (insertZerosCLM F hd x) := f.differentiableAt
  rw [fderiv_comp x hf (insertZerosCLM F hd).differentiableAt, ContinuousLinearMap.fderiv]
  have hs : (∑ i, ins0 hd x i * ins0 hd b i) = ∑ i, x i * b i :=
    ins0_dotProduct_ins0 hd x b
  rw [hs]
  rfl

end GlobalTheory.ThK.PlaneEv
