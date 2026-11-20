import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.HcHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSat

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

/- English proof (translation)
Introduce `E _ _ _ n a b h w ν ϖ k hw hϖ hν`. Establish `h0 : ϖ ≠ 0` using `b_unif_ne_zero hϖ`. Establish `hord : ordL ((Units.mk0 ϖ h0 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1`. Rewrite using `[Units.val_mk0]`. Conclude with `ordL_unif hϖ`.

Establish `hH` using `PositivityTheory.Rg.BcB.F.Fok.ctT_hecke E n a b h w ν (Units.mk0 ϖ h0) hw hord hν k`. Rewrite `hH` using `[Units.val_mk0]`. Use `⟨hH.1, fun y hy g => (hH.2 y hy g).2, ?_⟩` and prove the remaining obligations. Establish `hm : ν (-1) = 1`. Apply `hν` to reduce the goal to its premises.

Use `ord_neg_one' (w := w)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.BCT.InertChar.ord_eq_ordL]`. Then use the resulting hypothesis. Rewrite using `[map_pow, hm, one_pow]`.
-/
theorem ctHecke_holds : CtHecke := by
  intro E _ _ _ n a b h w ν ϖ k hw hϖ hν
  have h0 : ϖ ≠ 0 := b_unif_ne_zero hϖ
  have hord : ordL ((Units.mk0 ϖ h0 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_mk0]; exact ordL_unif hϖ
  have hH := PositivityTheory.Rg.BcB.F.Fok.ctT_hecke E n a b h w ν (Units.mk0 ϖ h0) hw hord hν k
  rw [Units.val_mk0] at hH
  refine ⟨hH.1, fun y hy g => (hH.2 y hy g).2, ?_⟩
  have hm : ν (-1) = 1 := by
    apply hν
    have := ord_neg_one' (w := w)
    rwa [GlobalTheory.BCT.InertChar.ord_eq_ordL] at this
  rw [map_pow, hm, one_pow]

end PositivityTheory.Rg.BcB.F.FG

end
