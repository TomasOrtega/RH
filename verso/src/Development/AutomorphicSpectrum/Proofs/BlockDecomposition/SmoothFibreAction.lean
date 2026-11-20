import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestLast
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

open Topology

/- English proof (translation)
Establish `: CompactSpace (tsupport φ)` using `isCompact_iff_compactSpace.mp hc`. Establish `h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite` using `(hl.comp_continuous continuous_subtype_val).range_finite`. Use `(h1.insert 0).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Distinguish the cases in `hx : x ∈ tsupport φ`.

Conclude with `Or.inr ⟨⟨x, hx⟩, rfl⟩`. Conclude with `Or.inl (image_eq_zero_of_notMem_tsupport hx)`.
-/
theorem range_finite {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace A`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := A)`. Use `letI : UniformSpace Z := ⊥`. Use `haveI : DiscreteTopology Z := ⟨rfl⟩`. Establish `hu : UniformContinuous φ` using `hc.uniformContinuous_of_continuous hl.continuous`.

Establish `hid : {p : Z × Z | p.1 = p.2} ∈ _root_.uniformity Z`. Establish `: _root_.uniformity Z = Filter.principal {p : Z × Z | p.1 = p.2}` using `rfl`. Rewrite using `[this]`. Conclude with `Filter.mem_principal_self _`. Establish `h1` using `hu hid`.

Rewrite `h1` using `[Filter.mem_map, uniformity_eq_comap_nhds_zero A, Filter.mem_comap]`. Take `⟨N, hN, hsub⟩` from `h1`. Use `⟨N, hN, fun w hw v => ?_⟩` and prove the remaining obligations. Establish `h2 : (v, v + w) ∈ (fun x : A × A => x.2 - x.1) ⁻¹' N` using `by show v + w - v ∈ N`. Simplify using `using hw`.

Conclude with `(hsub h2).symm`.
-/
theorem exists_nhds_translation_invariant {A Z : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddCommGroup Z] {φ : A → Z} (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) : ∃ N ∈ 𝓝 (0 : A), ∀ w ∈ N, ∀ v, φ (v + w) = φ v := by
  letI := IsTopologicalAddGroup.rightUniformSpace A
  haveI := isUniformAddGroup_of_addCommGroup (G := A)
  letI : UniformSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  have hu : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hid : {p : Z × Z | p.1 = p.2} ∈ _root_.uniformity Z := by
    have : _root_.uniformity Z = Filter.principal {p : Z × Z | p.1 = p.2} := rfl
    rw [this]
    exact Filter.mem_principal_self _
  have h1 := hu hid
  rw [Filter.mem_map, uniformity_eq_comap_nhds_zero A, Filter.mem_comap] at h1
  obtain ⟨N, hN, hsub⟩ := h1
  refine ⟨N, hN, fun w hw v => ?_⟩
  have h2 : (v, v + w) ∈ (fun x : A × A => x.2 - x.1) ⁻¹' N := by
    show v + w - v ∈ N
    simpa using hw
  exact (hsub h2).symm

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yhd4.main ρ v h`.
-/
theorem isOpen_stabiliser {G V : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (h : {g | ρ g v = v} ∈ 𝓝 (1 : G)) :
    IsOpen {g | ρ g v = v} :=
  _root_.UpperTheory.Reformulated.B.Yhd4.main ρ v h

/- English proof (translation)
Introduce `φ`. Use `isOpen_stabiliser (fibAct t ρ₀) φ ?_` and prove the remaining obligations. Establish `hU : (⋂ z ∈ Set.range φ.1, {g : Multiplicative (Fin i → k) | ρ₀ g z = z}) ∈ 𝓝 1` using `(Filter.biInter_mem (range_finite φ.2.1 φ.2.2)).2 fun z _ => (hρ z).mem_nhds (show ρ₀ 1 z = z by rw [map_one, Module.End.one_apply])`. Take `⟨N, hN, hinv⟩` from `exists_nhds_translation_invariant φ.2.1 φ.2.2`. Establish `hT : Continuous fun y : Multiplicative (Fin (i + t) → k) => Multiplicative.ofAdd (topP i t y.toAdd)` using `continuous_ofAdd.comp ((continuous_topP i t).comp continuous_toAdd)`.

Establish `hM : Continuous fun y : Multiplicative (Fin (i + t) → k) => middlePart i t y.toAdd` using `(continuous_midP i t).comp continuous_toAdd`. Establish `h1` using `hT.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hU`. Establish `h2` using `hM.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hN`. Use `Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hy1, hy2⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Use `show ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) = φ.1 v`. Rewrite using `[hinv _ hy2 v]`. Conclude with `Set.mem_iInter₂.1 hy1 (φ.1 v) ⟨v, rfl⟩`.
-/
theorem isSmooth_fibAct (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (hρ : IsSmooth ρ₀) :
    IsSmooth (fibAct t ρ₀) := by
  intro φ
  refine isOpen_stabiliser (fibAct t ρ₀) φ ?_
  have hU : (⋂ z ∈ Set.range φ.1, {g : Multiplicative (Fin i → k) | ρ₀ g z = z}) ∈ 𝓝 1 :=
    (Filter.biInter_mem (range_finite φ.2.1 φ.2.2)).2 fun z _ =>
      (hρ z).mem_nhds (show ρ₀ 1 z = z by rw [map_one, Module.End.one_apply])
  obtain ⟨N, hN, hinv⟩ := exists_nhds_translation_invariant φ.2.1 φ.2.2
  have hT : Continuous fun y : Multiplicative (Fin (i + t) → k) =>
      Multiplicative.ofAdd (topP i t y.toAdd) :=
    continuous_ofAdd.comp ((continuous_topP i t).comp continuous_toAdd)
  have hM : Continuous fun y : Multiplicative (Fin (i + t) → k) => middlePart i t y.toAdd :=
    (continuous_midP i t).comp continuous_toAdd
  have h1 := hT.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hU
  have h2 := hM.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hN
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro y ⟨hy1, hy2⟩
  apply Subtype.ext
  funext v
  show ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) = φ.1 v
  rw [hinv _ hy2 v]
  exact Set.mem_iInter₂.1 hy1 (φ.1 v) ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

end
