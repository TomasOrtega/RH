import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ n _ w σ B hB`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (algebraMap E (w.adicCompletion E)).injective`. Take `⟨α, hαB, hα⟩` from `(GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1 (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)`. Establish `hϖ : Valued.v ((GroundTheory.Global.uniformizerUnit w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-1 : ℤ)`. Simplify using `using GroundTheory.Global.valued_uniformizerUnit_zpow w 1`.

Use `⟨fun j => GlobalTheory.SmGL.unrChar _ (α j), fun j => GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_unrChar _ (α j)), GroundTheory.Global.uniformizerUnit w, ?_, ?_, hϖ, ?_⟩` and prove the remaining obligations. Set `π : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))` to `⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩`. Conclude with `(GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries _ n _ _ π hα.2.2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)`. Introduce `j x hx`. Rewrite using `[GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hx]`.

Simplify using the standard rewrite rules. Rewrite using `[← hαB]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hϖ]`.

Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.SatSupp.hasSupport_of_hasSatGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  intro E _ _ n _ w σ B hB
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_ringHom (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  have hϖ : Valued.v ((GroundTheory.Global.uniformizerUnit w : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := by
    simpa using GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  refine ⟨fun j => GlobalTheory.SmGL.unrChar _ (α j),
    fun j => GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_unrChar _ (α j)),
    GroundTheory.Global.uniformizerUnit w, ?_, ?_, hϖ, ?_⟩
  · let π : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)) := ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩
    exact (GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries _ n _ _ π hα.2.2).of_equiv
      (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro j x hx
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
    simp
  · rw [← hαB]
    congr 1
    funext j
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hϖ]
    simp
