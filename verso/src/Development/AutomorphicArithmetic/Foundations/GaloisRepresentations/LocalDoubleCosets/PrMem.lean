import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ B hB _ _ μ _ χ hker`. Use `haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hχc : Continuous (fun x : B => (χ x : ℂ))`. Use `continuous_of_continuousAt_one ((Units.coeHom ℂ).comp χ) ?_` as an intermediate fact. Conclude with `this`.

Use `(continuousAt_const (y := (1 : ℂ))).congr ?_ filter_upwards [hker.mem_nhds (one_mem χ.ker)] with x hx` and prove the remaining obligations. Establish `hx' : χ x = 1` using `MonoidHom.mem_ker.mp hx`. Simplify using `[hx']`. Establish `hint : ∀ f ∈ Cc G, ∀ g : G, Integrable (fun x : B => (χ x : ℂ) * f ((x : G)⁻¹ * g)) μ`. Introduce `f hf g`.

Rewrite `hf` using `[GroundTheory.Automorphic.mem_locallyConstantCompactSupport]`. Take `⟨hlc, hcs⟩` from `hf`. Establish `hemb : Topology.IsClosedEmbedding (fun x : B => (x : G)⁻¹ * g)` using `((Homeomorph.inv G).trans (Homeomorph.mulRight g)).isClosedEmbedding.comp hB.isClosedEmbedding_subtypeVal`. Establish `hcs' : HasCompactSupport (fun x : B => f ((x : G)⁻¹ * g))` using `hcs.comp_isClosedEmbedding hemb`. Conclude with `Continuous.integrable_of_hasCompactSupport (hχc.mul (hlc.continuous.comp hemb.continuous)) hcs'.mul_left`.

Use `⟨fun f hf => ?_, fun f hf f' hf' => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_indF]`. Prove the components needed by the constructor for the conclusion. Introduce `b g`. Simplify using `only [pr]`.

Rewrite using `[← integral_mul_left_eq_self _ b, ← integral_const_mul]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [map_mul, Units.val_mul, Subgroup.coe_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]`. Take `⟨K, -, hK⟩` from `GroundTheory.Automorphic.exists_forall_mul_right hf`.

Use `⟨(K : Subgroup G), K.isOpen, fun k hk g => ?_⟩` and prove the remaining obligations. Simplify using `only [pr]`. Use `congr 1`. Use extensionality with `x`. Rewrite using `[← mul_assoc, hK _ _ hk]`.

Use function extensionality and compare the values at `g`. Simplify using `only [pr, Pi.add_apply, mul_add]`. Conclude with `integral_add (hint f hf g) (hint f' hf' g)`.
-/
theorem UpperTheory.Gal.LocD.prMem :
    PrMem := by
  intro G _ _ _ _ _ _ _ B hB _ _ μ _ χ hker
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  have hχc : Continuous (fun x : B => (χ x : ℂ)) := by
    have := continuous_of_continuousAt_one ((Units.coeHom ℂ).comp χ) ?_
    · exact this
    · refine (continuousAt_const (y := (1 : ℂ))).congr ?_
      filter_upwards [hker.mem_nhds (one_mem χ.ker)] with x hx
      have hx' : χ x = 1 := MonoidHom.mem_ker.mp hx
      simp [hx']
  have hint : ∀ f ∈ Cc G, ∀ g : G,
      Integrable (fun x : B => (χ x : ℂ) * f ((x : G)⁻¹ * g)) μ := by
    intro f hf g
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf
    obtain ⟨hlc, hcs⟩ := hf
    have hemb : Topology.IsClosedEmbedding (fun x : B => (x : G)⁻¹ * g) :=
      ((Homeomorph.inv G).trans (Homeomorph.mulRight g)).isClosedEmbedding.comp
        hB.isClosedEmbedding_subtypeVal
    have hcs' : HasCompactSupport (fun x : B => f ((x : G)⁻¹ * g)) :=
      hcs.comp_isClosedEmbedding hemb
    exact Continuous.integrable_of_hasCompactSupport
      (hχc.mul (hlc.continuous.comp hemb.continuous)) hcs'.mul_left
  refine ⟨fun f hf => ?_, fun f hf f' hf' => ?_⟩
  · rw [mem_indF]
    constructor
    · intro b g
      simp only [pr]
      rw [← integral_mul_left_eq_self _ b, ← integral_const_mul]
      congr 1
      ext x
      simp only [map_mul, Units.val_mul, Subgroup.coe_mul, _root_.mul_inv_rev, mul_assoc,
        inv_mul_cancel_left]
    · obtain ⟨K, -, hK⟩ := GroundTheory.Automorphic.exists_forall_mul_right hf
      refine ⟨(K : Subgroup G), K.isOpen, fun k hk g => ?_⟩
      simp only [pr]
      congr 1
      ext x
      rw [← mul_assoc, hK _ _ hk]
  · funext g
    simp only [pr, Pi.add_apply, mul_add]
    exact integral_add (hint f hf g) (hint f' hf' g)
