import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ContinuousPlaceEmbedReal

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Introduce `F _ _ _`. Establish `hd : ∀ (w : InfinitePlace F) (i : Fin 4) (φ : S4 F), ∃ φ' : S4 F, ∀ v, HasDerivAt (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) (φ'.1 v) 0`. Introduce `w i φ`. Take `⟨φ', h, hs⟩` from `dEx F w i φ.1 φ.2`. Conclude with `⟨⟨φ', h⟩, hs⟩`.

Use `choose dd hdd using hd`. Use `⟨{ x := fun w i => { toFun := fun φ => ⟨fun v => cw w (v i) * φ.1 v, xEx F w i φ.1 φ.2⟩ map_add' := fun φ ψ => by` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Express the relevant statement in the definitionally equal form `cw w (v i) * (φ.1 v + ψ.1 v) = cw w (v i) * φ.1 v + cw w (v i) * ψ.1 v`.

Rewrite using `[mul_add]`. Use the proof step `map_smul' := fun c φ => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Express the relevant statement in the definitionally equal form `cw w (v i) * (c * φ.1 v) = c * (cw w (v i) * φ.1 v)`.

Rewrite using `[mul_left_comm] }`. Use `d := fun w i => { toFun := dd w i map_add' := fun φ ψ => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Establish `h1` using `(hdd w i φ v).add (hdd w i ψ v)`.

Conclude with `(hdd w i (φ + ψ) v).unique h1`. Use the proof step `map_smul' := fun c φ => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Establish `h1` using `(hdd w i φ v).const_mul c`.

Conclude with `(hdd w i (c • φ) v).unique h1 }`. Use `x_apply := fun w i φ v => rfl`. Use `d_spec := fun w i φ v => hdd w i φ v }⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Nonempty (Ops F) := by
  intro F _ _ _
  have hd : ∀ (w : InfinitePlace F) (i : Fin 4) (φ : S4 F), ∃ φ' : S4 F, ∀ v,
      HasDerivAt (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) (φ'.1 v) 0 := by
    intro w i φ
    obtain ⟨φ', h, hs⟩ := dEx F w i φ.1 φ.2
    exact ⟨⟨φ', h⟩, hs⟩
  choose dd hdd using hd
  refine ⟨{
    x := fun w i =>
      { toFun := fun φ => ⟨fun v => cw w (v i) * φ.1 v, xEx F w i φ.1 φ.2⟩
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (φ.1 v + ψ.1 v) = cw w (v i) * φ.1 v + cw w (v i) * ψ.1 v
          rw [mul_add]
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (c * φ.1 v) = c * (cw w (v i) * φ.1 v)
          rw [mul_left_comm] }
    d := fun w i =>
      { toFun := dd w i
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).add (hdd w i ψ v)
          exact (hdd w i (φ + ψ) v).unique h1
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).const_mul c
          exact (hdd w i (c • φ) v).unique h1 }
    x_apply := fun w i φ v => rfl
    d_spec := fun w i φ v => hdd w i φ v }⟩
