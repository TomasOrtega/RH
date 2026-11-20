import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

/- English proof (translation)
Simplify using `only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `h g hg`.
-/
private theorem mem_fixL' {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) (h : ∀ g ∈ J, rhoL μ w g x = x) : x ∈ fixL μ w J := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

/- English proof (translation)
Use `letI : MeasurableSpace (Gw n w) := borel _`. Use `haveI : BorelSpace (Gw n w) := ⟨rfl⟩`. Take `⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩` from `UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w (Measure.haar) hV`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, f x ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hf0 (LinearMap.ext hc)`. Use `⟨{ carrier := {g | σ.ρ g x = x} mul_mem' := fun {a b} ha hb => by` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] },`.

Use `f x, σ.smooth x, hfV x, hx, fun g hg => ?_⟩`. Rewrite using `[← hfe g x]`. Conclude with `congrArg f hg`.
-/
private theorem exists_fixed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    ∃ (S : Subgroup (Gw n w)) (x : LL μ), IsOpen (S : Set (Gw n w)) ∧ x ∈ V ∧ x ≠ 0 ∧ ∀ g ∈ S, rhoL μ w g x = x := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w (Measure.haar) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  refine ⟨{ carrier := {g | σ.ρ g x = x}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              rw [map_mul, Module.End.mul_apply, hb, ha]
            one_mem' := by simp
            inv_mem' := fun {a} ha => by
              simp only [Set.mem_setOf_eq] at ha ⊢
              conv_lhs => rw [← ha]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] },
    f x, σ.smooth x, hfV x, hx, fun g hg => ?_⟩
  rw [← hfe g x]
  exact congrArg f hg

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hv`. Use `choose S x hSo hxV hx0 hxS using fun u : PlacesOver E v => exists_fixed μ V hV u.1`. Establish `hsp` using `fun u : PlacesOver E v => (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n).1`. Use `choose e he using hsp`. Set `U : Subgroup (Gw n v)` to `GLnLocal.integralGL (v.adicCompletion F) n ⊓ ⨅ u : PlacesOver E v, (S u).comap (mapGL n (completionMap v u.1))`.

Establish `hUo : IsOpen (U : Set (Gw n v))`. Establish `h2 : IsOpen (⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)))`. Use `isOpen_iInter_of_finite fun u => ?_` and prove the remaining obligations. Establish `: (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) = (e u) ⁻¹' (S u : Set (Gw n u.1))`. Use extensionality with `g`.

Simplify using `only [Set.mem_preimage, he]`. Rewrite using `[this]`. Conclude with `(hSo u).preimage (e u).continuous`. Establish `h3 : (U : Set (Gw n v)) = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)) ∩ ⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1))`. Use extensionality with `g`.

Simplify using `[U, Subgroup.mem_inf, Subgroup.mem_iInf]`. Rewrite using `[h3]`. Conclude with `(GLnLocal.isOpen_integralGL _ n).inter h2`. Establish `hUle : U ≤ GLnLocal.integralGL (v.adicCompletion F) n` using `inf_le_left`. Establish `hUc : IsCompact (U : Set (Gw n v))` using `(GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) hUle`.

Establish `hinj : ∀ u : PlacesOver E v, Function.Injective (mapGL n (completionMap v u.1))` using `fun u a b h => (e u).injective (by rw [he, he, h])`. Use `⟨U, fun u => U.map (mapGL n (completionMap v u.1)), ⟨hUc, hUo⟩, hUle, fun u => ?_⟩` and prove the remaining obligations. Establish `himg : ((U.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = (e u) '' (U : Set (Gw n v))`. Use extensionality with `y`. Simplify using `only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, he]`.

Use `⟨⟨?_, ?_⟩, fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[himg]`. Conclude with `hUc.image (e u).continuous`. Rewrite using `[himg]`. Conclude with `(e u).toHomeomorph.isOpenMap _ hUo`.

Conclude with `(Subgroup.mem_map_iff_mem (hinj u)).symm`. Introduce `hbot`. Establish `hmem : x u ∈ V ⊓ fixL μ u.1 (U.map (mapGL n (completionMap v u.1)))`. Use `⟨hxV u, mem_fixL' μ u.1 _ _ ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Conclude with `hxS u _ ((Subgroup.mem_iInf.1 hg.2) u)`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`. Conclude with `hx0 u hmem`.
-/
theorem splitLev : SplitLev := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hv
  choose S x hSo hxV hx0 hxS using fun u : PlacesOver E v => exists_fixed μ V hV u.1
  have hsp := fun u : PlacesOver E v => (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n).1
  choose e he using hsp
  let U : Subgroup (Gw n v) := GLnLocal.integralGL (v.adicCompletion F) n ⊓
    ⨅ u : PlacesOver E v, (S u).comap (mapGL n (completionMap v u.1))
  have hUo : IsOpen (U : Set (Gw n v)) := by
    have h2 : IsOpen (⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1))) := by
      refine isOpen_iInter_of_finite fun u => ?_
      have : (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) = (e u) ⁻¹' (S u : Set (Gw n u.1)) := by
        ext g; simp only [Set.mem_preimage, he]
      rw [this]
      exact (hSo u).preimage (e u).continuous
    have h3 : (U : Set (Gw n v)) = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)) ∩
        ⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) := by
      ext g
      simp [U, Subgroup.mem_inf, Subgroup.mem_iInf]
    rw [h3]
    exact (GLnLocal.isOpen_integralGL _ n).inter h2
  have hUle : U ≤ GLnLocal.integralGL (v.adicCompletion F) n := inf_le_left
  have hUc : IsCompact (U : Set (Gw n v)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) hUle
  have hinj : ∀ u : PlacesOver E v, Function.Injective (mapGL n (completionMap v u.1)) := fun u a b h =>
    (e u).injective (by rw [he, he, h])
  refine ⟨U, fun u => U.map (mapGL n (completionMap v u.1)), ⟨hUc, hUo⟩, hUle, fun u => ?_⟩
  have himg : ((U.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = (e u) '' (U : Set (Gw n v)) := by
    ext y
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, he]
  refine ⟨⟨?_, ?_⟩, fun g => ?_, ?_⟩
  · rw [himg]
    exact hUc.image (e u).continuous
  · rw [himg]
    exact (e u).toHomeomorph.isOpenMap _ hUo
  · exact (Subgroup.mem_map_iff_mem (hinj u)).symm
  · intro hbot
    have hmem : x u ∈ V ⊓ fixL μ u.1 (U.map (mapGL n (completionMap v u.1))) := by
      refine ⟨hxV u, mem_fixL' μ u.1 _ _ ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      exact hxS u _ ((Subgroup.mem_iInf.1 hg.2) u)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx0 u hmem

end UpperTheory.ConvolutionTheory.T
