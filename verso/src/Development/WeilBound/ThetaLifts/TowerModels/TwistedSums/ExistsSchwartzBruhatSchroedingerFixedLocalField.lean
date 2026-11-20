import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.IsLocallyConstantHeisenbergLatticeVacuumFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SchrTestVec
open _root_.GlobalTheory

/- English proof (translation)
Use `⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ (B : Set (κ → K))`. Use `filter_upwards [hBo.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hy]`. Use `filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]`. Conclude with `HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _`. Introduce `h`.

Use `congrFun h 0` as an intermediate fact. Rewrite `this` using `[Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)]`. Conclude with `one_ne_zero this`. Establish `hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) => z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2)` using `(continuous_snd.dotProduct continuous_fst.snd).add (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))`. Establish `h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)), x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀`.

Use `hBc.eventually_forall_of_forall_eventually (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_` and prove the remaining obligations. Use `(hU₀.preimage hc).mem_nhds ?_` and prove the remaining obligations. Simplify using `using h0`. Establish `h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K))` using `(hBo.preimage continuous_fst).mem_nhds B.zero_mem`. Use `⟨_, h1.and h2, fun w hw => ?_⟩` and prove the remaining obligations.

Take `⟨hw1, hw2⟩` from `hw`. Use function extensionality and compare the values at `x`. Use `show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _`. Distinguish the cases in `hx : x ∈ (B : Set (κ → K))`. Rewrite using `[hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx, Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]`.

Establish `hx' : x + w.1 ∉ (B : Set (κ → K))` using `fun h => hx (by simpa using B.sub_mem h hw2)`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]`.
-/
theorem exists_fixed_of_subgroup {K : Type} [CommRing K] [Invertible (2 : K)] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {κ : Type} [Fintype κ] (ψ : AddChar K ℂ) (U₀ : Set K) (hU₀ : IsOpen U₀) (h0 : (0 : K) ∈ U₀)
    (hψ : ∀ t ∈ U₀, ψ t = 1) (B : AddSubgroup (κ → K)) (hBo : IsOpen (B : Set (κ → K)))
    (hBc : IsCompact (B : Set (κ → K))) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → K), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → K) × (κ → K)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  refine ⟨(B : Set (κ → K)).indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (B : Set (κ → K))
    · filter_upwards [hBo.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · exact HasCompactSupport.intro hBc fun x hx => Set.indicator_of_notMem hx _
  · intro h
    have := congrFun h 0
    rw [Set.indicator_of_mem (show (0 : κ → K) ∈ (B : Set (κ → K)) from B.zero_mem)] at this
    exact one_ne_zero this
  · have hc : Continuous fun z : ((κ → K) × (κ → K)) × (κ → K) =>
        z.2 ⬝ᵥ z.1.2 + ⅟(2 : K) * (z.1.1 ⬝ᵥ z.1.2) :=
      (continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
    have h1 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, ∀ x ∈ (B : Set (κ → K)),
        x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀ := by
      refine hBc.eventually_forall_of_forall_eventually
        (P := fun (w : (κ → K) × (κ → K)) (x : κ → K) => x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) ∈ U₀) fun x _ => ?_
      refine (hU₀.preimage hc).mem_nhds ?_
      simpa using h0
    have h2 : ∀ᶠ w : (κ → K) × (κ → K) in nhds 0, w.1 ∈ (B : Set (κ → K)) :=
      (hBo.preimage continuous_fst).mem_nhds B.zero_mem
    refine ⟨_, h1.and h2, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    funext x
    show ψ (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * (B : Set (κ → K)).indicator (fun _ => (1 : ℂ)) (x + w.1) = _
    by_cases hx : x ∈ (B : Set (κ → K))
    · rw [hψ _ (hw1 x hx), one_mul, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x + w.1 ∈ (B : Set (κ → K)) from B.add_mem hx hw2)]
    · have hx' : x + w.1 ∉ (B : Set (κ → K)) := fun h => hx (by simpa using B.sub_mem h hw2)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]

/- English proof (translation)
Introduce `F _ _ v ψ hψ κ _`. Take `⟨U₀, hU₀⟩` from `Tw.HeisLatVac.lc_exists_open_ker ψ hψ`. Use `exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀ (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_` and prove the remaining obligations. Conclude with `isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _`. Conclude with `isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)`.
-/
theorem exists_fixed : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ∀ {κ : Type} [Fintype κ], ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), φ₁ ≠ 0 ∧
      ∃ U ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ U, GlobalTheory.WeilM.schr ψ w φ₁ = φ₁ := by
  intro F _ _ v ψ hψ κ _
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψ
  refine exists_fixed_of_subgroup ψ U₀ U₀.isOpen U₀.zero_mem hU₀
    (AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup) ?_ ?_
  · exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  · exact isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)

end Tw.SchrTestVec
