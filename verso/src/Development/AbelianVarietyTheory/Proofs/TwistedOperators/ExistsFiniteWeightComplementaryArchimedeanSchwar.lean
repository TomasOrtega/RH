import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.Adele.Compact

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchRest

/- English proof (translation)
Introduce `F _ _ κ _`. Set `I : Set (FiniteAdeleRing (𝓞 F) F)` to `(GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)`. Establish `hIo : IsOpen I` using `GroundTheory.Global.isOpen_integralFiniteAdeles`. Establish `hIc : IsClosed I` using `AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hIo`. Establish `hIk : IsCompact I` using `GroundTheory.Global.isCompact_integralFiniteAdeles F`.

Set `S : Set (κ → FiniteAdeleRing (𝓞 F) F)` to `Set.univ.pi fun _ => I`. Establish `hSo : IsOpen S` using `isOpen_set_pi Set.finite_univ fun _ _ => hIo`. Establish `hSc : IsClosed S` using `isClosed_set_pi fun _ _ => hIc`. Establish `hSk : IsCompact S` using `isCompact_univ_pi fun _ => hIk`. Set `g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ` to `S.indicator 1`.

Establish `hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)`. Use `⟨?_, HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Distinguish the cases in `hx : x ∈ S`.

Conclude with `⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩`. Conclude with `⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩`. Use `⟨fun x => g fun i => (x i).2, ?_, fun f => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h0 : (fun i => ((0 : κ → AF F) i).2) ∈ S` using `fun i _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem`. Simplify using `only [g, Set.indicator_of_mem h0, Pi.one_apply]`.

Conclude with `one_ne_zero`. Introduce `x z hz`. Establish `hz2 : ∀ i, (z i).2 = 0`. Set `u : AF F` to `((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))`. Establish `e` using `hz u (by show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`.

Conclude with `map_zero _)`. Introduce `i`. Establish `e'` using `congrFun e i`. Establish `h1 : (u • z) i = u * z i` using `rfl`. Rewrite `e'` using `[h1]`.

Establish `h2 : (u * z i).2 = 1 * (z i).2` using `rfl`. Use `congrArg Prod.snd e'` as an intermediate fact. Rewrite `this` using `[h2, one_mul]`. Conclude with `this`. Use `show g (fun i => ((x + z) i).2) = g (fun i => (x i).2)`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Use `show (x i).2 + (z i).2 = (x i).2`. Rewrite using `[hz2 i, add_zero]`. Establish `e : tens (evI F) (⇑f) (fun x => g fun i => (x i).2) = pureA F (⇑f) g` using `rfl`.

Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨f, g, hg, rfl⟩`.
-/
theorem exists_rest_arch : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  intro F _ _ κ _
  classical
  let I : Set (FiniteAdeleRing (𝓞 F) F) := (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hIo : IsOpen I := GroundTheory.Global.isOpen_integralFiniteAdeles
  have hIc : IsClosed I :=
    AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hIo
  have hIk : IsCompact I := GroundTheory.Global.isCompact_integralFiniteAdeles F
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => I
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hIo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => hIc
  have hSk : IsCompact S := isCompact_univ_pi fun _ => hIk
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ S
    · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
    · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  refine ⟨fun x => g fun i => (x i).2, ?_, fun f => ⟨?_, ?_⟩⟩
  · have h0 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply]
    exact one_ne_zero
  · intro x z hz
    have hz2 : ∀ i, (z i).2 = 0 := by
      let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
      have e := hz u (by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _)
      intro i
      have e' := congrFun e i
      have h1 : (u • z) i = u * z i := rfl
      rw [h1] at e'
      have h2 : (u * z i).2 = 1 * (z i).2 := rfl
      have := congrArg Prod.snd e'
      rw [h2, one_mul] at this
      exact this
    show g (fun i => ((x + z) i).2) = g (fun i => (x i).2)
    congr 1
    funext i
    show (x i).2 + (z i).2 = (x i).2
    rw [hz2 i, add_zero]
  · have e : tens (evI F) (⇑f) (fun x => g fun i => (x i).2) = pureA F (⇑f) g := rfl
    rw [e]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩

end GlobalTheory.ArchRest
