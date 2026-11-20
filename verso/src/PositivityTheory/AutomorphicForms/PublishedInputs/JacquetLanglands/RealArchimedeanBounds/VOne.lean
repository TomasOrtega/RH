import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.ClassNumberLemmas

/- English proof (translation)
Establish `a1 : Valued.v (pLoc F w (e : Af F)) ≤ 1`. Establish `h` using `h1 w`. Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `h`. Establish `a2 : Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) ≤ 1`.

Establish `h` using `h2 w`. Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `h`. Establish `hm : Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`.

Use `le_antisymm a1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem v_one {F : Type} [Field F] [NumberField F] (e : (Af F)ˣ) (h1 : (e : Af F) ∈ PIW.ClassFinD.Ohat F)
    (h2 : ((e⁻¹ : (Af F)ˣ) : Af F) ∈ PIW.ClassFinD.Ohat F) (w : Pl F) : Valued.v (pLoc F w (e : Af F)) = 1 := by
  have a1 : Valued.v (pLoc F w (e : Af F)) ≤ 1 := by
    have h := h1 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have a2 : Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := by
    have h := h2 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hm : Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : _) = Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) := hm.symm
    _ ≤ Valued.v (pLoc F w (e : Af F)) * 1 := by gcongr
    _ = Valued.v (pLoc F w (e : Af F)) := mul_one _

end UpperTheory.Esk.ClassNumberLemmas

namespace UpperTheory.Esk

/- English proof (translation)
Introduce `F _ _`. Take `⟨C, hC⟩` from `PIW.ClassFinD.idele_class_finite F`. Use `⟨C, fun z => ?_⟩` and prove the remaining obligations. Take `⟨f, c, hc, e, he1, he2, hz⟩` from `hC z`. Conclude with `⟨f, e, c, hc, ClassNumberLemmas.v_one e he1 he2, hz⟩`.
-/
theorem aCls : ACls := by
  intro F _ _
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite F
  refine ⟨C, fun z => ?_⟩
  obtain ⟨f, c, hc, e, he1, he2, hz⟩ := hC z
  exact ⟨f, e, c, hc, ClassNumberLemmas.v_one e he1 he2, hz⟩

end UpperTheory.Esk
