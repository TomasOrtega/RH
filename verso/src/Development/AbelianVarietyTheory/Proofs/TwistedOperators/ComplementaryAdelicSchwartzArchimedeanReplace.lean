import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TwistRest

open scoped Classical in
/- English proof (translation)
Introduce `F _ _ κ _ f f₁ r hr hf`. Take `⟨hinv, hsch⟩` from `hr`. Use `set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef`. Establish `hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2)`. Introduce `x`.

Set `z : κ → AF F` to `fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))`. Establish `hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z`. Introduce `u hu`. Establish `hu1 : u.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `(u * z i : AF F) = 0`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u.1 * (x i).1 = 0`. Rewrite using `[hu1, zero_mul]`. Express the relevant statement in the definitionally equal form `u.2 * 0 = 0`.

Conclude with `mul_zero _`. Set `x' : κ → AF F` to `fun i => ((0 : InfiniteAdeleRing F), (x i).2)`. Use `hinv x' z hz` as an intermediate fact. Establish `hx : x = x' + z`. Use function extensionality and compare the values at `i`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x i).1 = (0 : InfiniteAdeleRing F) + (x i).1`. Rewrite using `[zero_add]`. Express the relevant statement in the definitionally equal form `(x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)`. Rewrite using `[add_zero]`.

Conclude with `(congrArg r hx).trans this`. Establish `htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g`. Introduce `f'`. Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]`.

Rewrite using `[hrg x]`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hf (SchwartzMap.ext h)`.

Set `a : κ → InfiniteAdeleRing F` to `fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)`. Set `Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ)` to `{ toFun := fun Φ y => Φ (fun i => (a i, y i)) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g'`. Introduce `f' g'`. Use function extensionality and compare the values at `y`.

Simplify using `[Λ, GlobalTheory.WeilM.pureA, a]`. Establish `hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `Φ ⟨f', g', hg', rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, hΛ]`.

Conclude with `Submodule.smul_mem _ _ hg'`. Establish `hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)`. Establish `h1` using `hle (htens f ▸ hsch)`. Rewrite `h1` using `[Submodule.mem_comap, hΛ]`. Use `Submodule.smul_mem _ (f x₀)⁻¹ h1` as an intermediate fact.

Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hx₀, one_smul]`. Then use the resulting hypothesis. Use `⟨hinv, ?_⟩` and prove the remaining obligations. Rewrite using `[htens f₁]`. Conclude with `Submodule.subset_span ⟨f₁, g, hg, rfl⟩`.
-/
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    simp [Λ, GlobalTheory.WeilM.pureA, a]
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
