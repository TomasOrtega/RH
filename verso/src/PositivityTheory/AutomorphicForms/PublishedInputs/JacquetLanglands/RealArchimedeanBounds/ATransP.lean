import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

/- English proof (translation)
Introduce `F _ _ _`. Set `b` to `mixedEmbedding.latticeBasis F`. Use `⟨(∑ i, ‖b i‖) + 1, by positivity, fun x => ?_⟩` and prove the remaining obligations. Set `p : mixedEmbedding.mixedSpace F` to `(fun w => x w.1, 0)`. Establish `hm : (ZSpan.floor b p : mixedEmbedding.mixedSpace F) ∈ Submodule.span ℤ (Set.range b)` using `(ZSpan.floor b p).2`.

Rewrite `hm` using `[mixedEmbedding.mem_span_latticeBasis]`. Take `⟨s, hs⟩` from `hm`. Use `⟨-(s : F), (RingOfIntegers.isIntegral_coe s).neg, fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `ZSpan.norm_fract_le b p`. Establish `h2 : (ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩ = x v + sg v (-(s : F))`.

Rewrite using `[ZSpan.fract_apply, ← hs]`. Simplify using `[p, sg, sub_eq_add_neg]`. Establish `h3 : ‖(ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩‖ ≤ ‖ZSpan.fract b p‖` using `(norm_le_pi_norm _ _).trans (norm_fst_le _)`. Rewrite `h3` using `[h2, Real.norm_eq_abs]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem aTrans : ATrans := by
  intro F _ _ _
  classical
  let b := mixedEmbedding.latticeBasis F
  refine ⟨(∑ i, ‖b i‖) + 1, by positivity, fun x => ?_⟩
  let p : mixedEmbedding.mixedSpace F := (fun w => x w.1, 0)
  have hm : (ZSpan.floor b p : mixedEmbedding.mixedSpace F) ∈
      Submodule.span ℤ (Set.range b) := (ZSpan.floor b p).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨s, hs⟩ := hm
  refine ⟨-(s : F), (RingOfIntegers.isIntegral_coe s).neg, fun v => ?_⟩
  have h1 := ZSpan.norm_fract_le b p
  have h2 : (ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩ = x v + sg v (-(s : F)) := by
    rw [ZSpan.fract_apply, ← hs]
    simp [p, sg, sub_eq_add_neg]
  have h3 : ‖(ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩‖ ≤ ‖ZSpan.fract b p‖ :=
    (norm_le_pi_norm _ _).trans (norm_fst_le _)
  rw [h2, Real.norm_eq_abs] at h3
  linarith

end UpperTheory.Esk
