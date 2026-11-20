import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormClassNorm

/- English proof (translation)
Introduce `E _ _ _ k _ _ r Q x hx`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `IsCMField.complexConj_ne_one E (AlgEquiv.ext h)`.

Establish `hθ : IsCMField.complexConj E (z - IsCMField.complexConj E z) = -(z - IsCMField.complexConj E z)`. Rewrite using `[map_sub, IsCMField.complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨b, B, hB⟩` from `GlobalTheory.TraceClasses.exists_bases Q (sub_ne_zero.2 hz.symm) hθ`. Establish `h1 : Isometric Q k (GlobalTheory.TraceClasses.gramRat Q B 1) ((1 : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q)`.

Use `(GlobalTheory.TraceClasses.isometric_tmul_iff Q B k (GlobalTheory.TraceClasses.gramRat Q B 1) 1).2 (GlobalTheory.HermLocal.CongrOver.of_congr ⟨1, by simp, by simp⟩)` as an intermediate fact. Simplify `this` using `[Algebra.TensorProduct.one_def]`. Establish `h2` using `Isometric.of_norm Q k hx h1`. Rewrite `h2` using `[one_mul]`. Establish `h3` using `GlobalTheory.TraceClasses.norm_div_mem Q hB k (δ := 1) (by simp) h2`.

Establish `h4 : GlobalTheory.QuadSymbol.toUnits (maximalRealSubfield E) k 1 = 1` using `map_one _`. Rewrite `h3` using `[h4, div_one]`. Then use the resulting hypothesis.
-/
theorem norm_mem_normGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k]
    [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r)
    (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k →
    Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  intro E _ _ _ k _ _ r Q x hx
  obtain ⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hθ : IsCMField.complexConj E (z - IsCMField.complexConj E z) =
      -(z - IsCMField.complexConj E z) := by
    rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  obtain ⟨b, B, hB⟩ := GlobalTheory.TraceClasses.exists_bases Q (sub_ne_zero.2 hz.symm) hθ
  have h1 : Isometric Q k (GlobalTheory.TraceClasses.gramRat Q B 1)
      ((1 : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) := by
    have := (GlobalTheory.TraceClasses.isometric_tmul_iff Q B k (GlobalTheory.TraceClasses.gramRat Q B 1) 1).2
      (GlobalTheory.HermLocal.CongrOver.of_congr ⟨1, by simp, by simp⟩)
    simpa [Algebra.TensorProduct.one_def] using this
  have h2 := Isometric.of_norm Q k hx h1
  rw [one_mul] at h2
  have h3 := GlobalTheory.TraceClasses.norm_div_mem Q hB k (δ := 1) (by simp) h2
  have h4 : GlobalTheory.QuadSymbol.toUnits (maximalRealSubfield E) k 1 = 1 := map_one _
  rwa [h4, div_one] at h3

end GlobalTheory.CompanionTheory.NormClassNorm

end
