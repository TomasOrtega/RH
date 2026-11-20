import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchurPolar.isMultiplicityInner_inner` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMultiplicativeInnerProductModel.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.multiplicative_inner_product_model : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (U : Submodule ℂ (MMap M)), HM.Is U (ipM M μ 𝓕) → ∀ x y : HM.H, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) (inner ℂ x y) := by
  first | exact @GlobalTheory.SchurPolar.isMultiplicityInner_inner | exact GlobalTheory.SchurPolar.isMultiplicityInner_inner | (intros; apply GlobalTheory.SchurPolar.isMultiplicityInner_inner <;> assumption)
