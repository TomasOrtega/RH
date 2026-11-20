import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.ContMkE
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SpanCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Splt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.KeyFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GmapCont

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π h0 Q hQ v w i hi hc σ σ' hσ hσ'`. Take `⟨θ, hθ⟩` from `UpperTheory.ConvolutionTheory.R2.I.splt F E D v w i hi hc`. Take `⟨ι, hι, he⟩` from `hσ'`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, ι y ≠ 0 := by`. Assume the negation of the conclusion as `hn`.

Conclude with `hι (LinearMap.ext fun y => by_contra fun h => hn ⟨y, h⟩)`. Choose the witnesses or unpack the hypotheses as in `⟨h, hh⟩ : ∃ h, WE D (ι y).1.1 h ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Conclude with `hy (Subtype.ext ((UpperTheory.ConvolutionTheory.R2.cusp F E D W M π h0 _ (hQ (ι y).2)).2 fun h => by_contra fun e => hn ⟨h, e⟩))`. Establish `hcont : ∀ u, Continuous (ι u).1.1` using `fun u => (H.spanCont F E D W M π _ (hQ (ι u).2)).1`.

Establish `hz : ∀ k, WE D (0 : GL (Fin 2) (A E) → ℂ) k = 0` using `fun k => by simp [WE]`. Set `J` to `(lc w).comp (Matrix.GeneralLinearGroup.map i.toRingHom)`. Set `T : σ'.V →ₗ[ℂ] (I.GLv v → ℂ)` to `{ toFun := fun u x => WE D (ι u).1.1 (h * J x) map_add' := fun u u' => funext fun x => by`. Use `(H.weEig F E D _ (hcont u)).2.2 _ 1 (hcont u') (h * J x)` as an intermediate fact. Rewrite `this` using `[one_smul, one_mul]`.

Rewrite using `[map_add]`. Conclude with `this`. Use the proof step `map_smul' := fun c u => funext fun x => by`. Use `(H.weEig F E D 0 continuous_const).2.2 _ c (hcont u) (h * J x)` as an intermediate fact. Rewrite `this` using `[zero_add, hz, zero_add]`.

Rewrite using `[map_smul]`. Conclude with `this }`. Use `UpperTheory.ConvolutionTheory.R2.I.fin F E π v w i hi σ σ' hσ T (fun e => hh ?_) (fun g u x => ?_) fun u => UpperTheory.ConvolutionTheory.R2.I.key F E D W M π v θ J hθ _ (hQ (ι u).2) h` and prove the remaining obligations. Use `congrFun (LinearMap.congr_fun e y) 1` as an intermediate fact. Simplify `this` using `[T]`.

Express the relevant statement in the definitionally equal form `WE D (ι _).1.1 _ = WE D (ι u).1.1 (h * J (x * g))`. Rewrite using `[he, map_mul, ← mul_assoc]`. Unfold `WE`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[← mul_assoc _ _ (J g)]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.R2.split :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Split W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Q hQ v w i hi hc σ σ' hσ hσ'
  obtain ⟨θ, hθ⟩ := UpperTheory.ConvolutionTheory.R2.I.splt F E D v w i hi hc
  obtain ⟨ι, hι, he⟩ := hσ'
  obtain ⟨y, hy⟩ : ∃ y, ι y ≠ 0 := by
    by_contra hn
    exact hι (LinearMap.ext fun y => by_contra fun h => hn ⟨y, h⟩)
  obtain ⟨h, hh⟩ : ∃ h, WE D (ι y).1.1 h ≠ 0 := by
    by_contra hn
    exact hy (Subtype.ext ((UpperTheory.ConvolutionTheory.R2.cusp F E D W M π h0 _ (hQ (ι y).2)).2 fun h => by_contra fun e => hn ⟨h, e⟩))
  have hcont : ∀ u, Continuous (ι u).1.1 := fun u => (H.spanCont F E D W M π _ (hQ (ι u).2)).1
  have hz : ∀ k, WE D (0 : GL (Fin 2) (A E) → ℂ) k = 0 := fun k => by simp [WE]
  let J := (lc w).comp (Matrix.GeneralLinearGroup.map i.toRingHom)
  let T : σ'.V →ₗ[ℂ] (I.GLv v → ℂ) :=
    { toFun := fun u x => WE D (ι u).1.1 (h * J x)
      map_add' := fun u u' => funext fun x => by
        have := (H.weEig F E D _ (hcont u)).2.2 _ 1 (hcont u') (h * J x)
        rw [one_smul, one_mul] at this
        rw [map_add]; exact this
      map_smul' := fun c u => funext fun x => by
        have := (H.weEig F E D 0 continuous_const).2.2 _ c (hcont u) (h * J x)
        rw [zero_add, hz, zero_add] at this
        rw [map_smul]; exact this }
  refine UpperTheory.ConvolutionTheory.R2.I.fin F E π v w i hi σ σ' hσ T (fun e => hh ?_) (fun g u x => ?_) fun u =>
    UpperTheory.ConvolutionTheory.R2.I.key F E D W M π v θ J hθ _ (hQ (ι u).2) h
  · have := congrFun (LinearMap.congr_fun e y) 1
    simpa [T] using this
  · change WE D (ι _).1.1 _ = WE D (ι u).1.1 (h * J (x * g))
    rw [he, map_mul, ← mul_assoc]
    unfold WE
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [← mul_assoc _ _ (J g)]
    rfl
