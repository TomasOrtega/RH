import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import GroundTheory.GlobalFields.Adele.Compact

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchUniq

variable {F : Type} [Field F] [NumberField F]

def intFinInd (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator (Set.pi Set.univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) 1

/- English proof (translation)
Use `set C := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))`. Establish `hoI : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))` using `GroundTheory.Global.isOpen_integralFiniteAdeles`. Establish `hcI` using `GroundTheory.Global.isCompact_integralFiniteAdeles F`. Establish `ho : IsOpen C` using `isOpen_set_pi Set.finite_univ fun _ _ => hoI`. Establish `hc : IsClosed C` using `isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hoI`.

Establish `hk : IsCompact C` using `isCompact_univ_pi fun _ => hcI`. Use `⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ C`.

Use `filter_upwards [ho.mem_nhds hx] with y hy`. Simplify using `only [intFinInd]`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Both sides reduce to the same expression. Use `filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy`.

Simplify using `only [intFinInd]`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
theorem intFinInd_mem_SB (κ : Type) [Fintype κ] : intFinInd F κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set C := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hoI : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles
  have hcI := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have ho : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => hoI
  have hc : IsClosed C :=
    isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hoI
  have hk : IsCompact C := isCompact_univ_pi fun _ => hcI
  refine ⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ C
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Establish `h` using `congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i`. Establish `h2` using `congrArg Prod.snd h`. Express the relevant statement in the definitionally equal form `(1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at h2`. Rewrite `h2` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 := congrArg Prod.snd h
  change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at h2
  rwa [one_mul] at h2

/- English proof (translation)
Introduce `F _ _ κ _`. Use `⟨fun x => intFinInd F κ (fun i => (x i).2), fun f => ⟨fun x z hz => ?_, ?_⟩, fun f₁ f₂ h => ?_⟩` and prove the remaining obligations. Establish `: (fun i => (x + z) i |>.2) = fun i => (x i).2`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(x i).2 + (z i).2 = (x i).2`.

Rewrite using `[snd_eq_zero_of_at hz i, add_zero]`. Simplify using `only [this]`. Conclude with `Submodule.subset_span ⟨f, intFinInd F κ, intFinInd_mem_SB κ, rfl⟩`. Use extensionality with `y`. Establish `h1` using `congrFun h (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)), 0))`.

Establish `hy : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y`. Use function extensionality and compare the values at `i`. Simplify using `[evI]`. Establish `h0 : intFinInd F κ (fun _ => 0) = 1`. Simplify using `only [intFinInd]`.

Rewrite using `[Set.indicator_of_mem (show (fun _ => (0 : FiniteAdeleRing (𝓞 F) F)) ∈ Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem)]`. Both sides reduce to the same expression. Simplify using `only [tens, hy, h0, mul_one] at h1`. Conclude with `h1`.
-/
theorem exists_admissible_finite_factor : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ,
    (∀ f : SInf F κ, Rest (evI F) (⇑f) r₀) ∧
    ∀ f₁ f₂ : SInf F κ, tens (evI F) (⇑f₁) r₀ = tens (evI F) (⇑f₂) r₀ → f₁ = f₂ := by
  intro F _ _ κ _
  refine ⟨fun x => intFinInd F κ (fun i => (x i).2), fun f => ⟨fun x z hz => ?_, ?_⟩, fun f₁ f₂ h => ?_⟩
  · have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intFinInd F κ, intFinInd_mem_SB κ, rfl⟩
  · ext y
    have h1 := congrFun h (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)), 0))
    have hy : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y := by
      funext i
      simp [evI]
    have h0 : intFinInd F κ (fun _ => 0) = 1 := by
      simp only [intFinInd]
      rw [Set.indicator_of_mem (show (fun _ => (0 : FiniteAdeleRing (𝓞 F) F)) ∈ Set.pi Set.univ
        fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem)]
      rfl
    simp only [tens, hy, h0, mul_one] at h1
    exact h1

end GlobalTheory.ArchUniq
