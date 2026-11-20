import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceCuspForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConstantTermSliceCuspForm.lean&line=288#L288)
-/
theorem _root_.GlobalTheory.T.constant_term_slice_cusp_form : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a), GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ ∈ Sm E (a - r) := by
  first | exact @GlobalTheory.SliceTwoSmooth.slice_mem_Sm | exact GlobalTheory.SliceTwoSmooth.slice_mem_Sm | (intros; apply GlobalTheory.SliceTwoSmooth.slice_mem_Sm <;> assumption)
