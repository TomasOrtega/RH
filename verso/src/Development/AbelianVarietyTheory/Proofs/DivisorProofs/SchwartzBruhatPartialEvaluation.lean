import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SliceSB

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Consider the cases of `i with`. Consider the case `inl i => exact (continuous_apply i).comp continuous_fst`. Consider the case `inr i => exact (continuous_apply i).comp continuous_snd`.
-/
theorem continuous_sumElim {k : Type} [TopologicalSpace k] {κ κ' : Type} :
    Continuous (fun p : (κ → k) × (κ' → k) => (Sum.elim p.1 p.2 : κ ⊕ κ' → k)) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

/- English proof (translation)
Introduce `k _ _ κ κ' _ _ f hf`. Take `⟨hlc, hcs⟩` from `hf`. Establish `hΦ` using `continuous_sumElim (k := k) (κ := κ) (κ' := κ')`. Use `⟨fun x₁ => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `he : Continuous (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k))` using `hΦ.comp (Continuous.prodMk continuous_const continuous_id)`.

Establish `hli : Function.LeftInverse (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k))` using `fun x₂ => rfl`. Establish `hce : Topology.IsClosedEmbedding (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k))` using `hli.isClosedEmbedding (continuous_pi fun i => continuous_apply _) he`. Conclude with `⟨hlc.comp_continuous he, hcs.comp_isClosedEmbedding hce⟩`. Use `set K := (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) '' tsupport f`. Establish `hK : IsCompact K` using `hcs.isCompact.image (continuous_pi fun i => continuous_apply _)`.

Establish `hloc : IsLocallyConstant (fun x₁ : κ → k => fun x₂ : κ' → k => f (Sum.elim x₁ x₂))`. Rewrite using `[IsLocallyConstant.iff_eventually_eq _]`. Introduce `x₀`. Establish `hF : IsLocallyConstant (fun p : (κ → k) × (κ' → k) => f (Sum.elim p.1 p.2))` using `hlc.comp_continuous hΦ`. Establish `h1 : ∀ y ∈ K, ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y), (fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) z.1 z.2`.

Introduce `y _`. Establish `h0` using `(IsLocallyConstant.iff_eventually_eq _).mp hF (x₀, y)`. Establish `hc : Continuous (fun z : (κ → k) × (κ' → k) => (x₀, z.2))` using `continuous_const.prodMk continuous_snd`. Establish `h3 : ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y), f (Sum.elim x₀ z.2) = f (Sum.elim x₀ y)` using `(hc.tendsto (x₀, y)).eventually h0`. Use `filter_upwards [h0, h3] with z hz hz'`.

Conclude with `hz.trans hz'.symm`. Establish `h2` using `hK.eventually_forall_of_forall_eventually (P := fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) h1`. Use `filter_upwards [h2] with x hx`. Use function extensionality and compare the values at `y`. Distinguish the cases in `hy : y ∈ K`.

Conclude with `hx y hy`. Establish `hz : ∀ x', f (Sum.elim x' y) = 0`. Introduce `x'`. Assume the negation of the conclusion as `hne`. Conclude with `hy ⟨Sum.elim x' y, subset_tsupport f hne, rfl⟩`.

Rewrite using `[hz, hz]`. Use `⟨(hloc.comp l), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hcs.isCompact.image (f := fun z : κ ⊕ κ' → k => z ∘ Sum.inl) (continuous_pi fun i => continuous_apply _)) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `: (fun x₂ : κ' → k => f (Sum.elim x x₂)) = 0`.

Use function extensionality and compare the values at `x₂`. Assume the negation of the conclusion as `hne`. Conclude with `hx ⟨Sum.elim x x₂, subset_tsupport f hne, rfl⟩`. Simplify using `only [this, map_zero]`.
-/
theorem slice_mem : ∀ (k : Type) [TopologicalSpace k] [T2Space k] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ f ∈ SB (κ ⊕ κ' → k),
    (∀ x₁ : κ → k, (fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) ∈ SB (κ' → k)) ∧
      ∀ l : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ, (fun x₁ : κ → k => l fun x₂ => f (Sum.elim x₁ x₂)) ∈ SB (κ → k) := by
  intro k _ _ κ κ' _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hΦ := continuous_sumElim (k := k) (κ := κ) (κ' := κ')
  refine ⟨fun x₁ => ?_, fun l => ?_⟩
  · have he : Continuous (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hΦ.comp (Continuous.prodMk continuous_const continuous_id)
    have hli : Function.LeftInverse (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      fun x₂ => rfl
    have hce : Topology.IsClosedEmbedding (fun x₂ : κ' → k => (Sum.elim x₁ x₂ : κ ⊕ κ' → k)) :=
      hli.isClosedEmbedding (continuous_pi fun i => continuous_apply _) he
    exact ⟨hlc.comp_continuous he, hcs.comp_isClosedEmbedding hce⟩
  · set K := (fun z : κ ⊕ κ' → k => z ∘ Sum.inr) '' tsupport f
    have hK : IsCompact K := hcs.isCompact.image (continuous_pi fun i => continuous_apply _)
    have hloc : IsLocallyConstant (fun x₁ : κ → k => fun x₂ : κ' → k => f (Sum.elim x₁ x₂)) := by
      rw [IsLocallyConstant.iff_eventually_eq _]
      intro x₀
      have hF : IsLocallyConstant (fun p : (κ → k) × (κ' → k) => f (Sum.elim p.1 p.2)) := hlc.comp_continuous hΦ
      have h1 : ∀ y ∈ K, ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y),
          (fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) z.1 z.2 := by
        intro y _
        have h0 := (IsLocallyConstant.iff_eventually_eq _).mp hF (x₀, y)
        have hc : Continuous (fun z : (κ → k) × (κ' → k) => (x₀, z.2)) := continuous_const.prodMk continuous_snd
        have h3 : ∀ᶠ z : (κ → k) × (κ' → k) in nhds (x₀, y), f (Sum.elim x₀ z.2) = f (Sum.elim x₀ y) :=
          (hc.tendsto (x₀, y)).eventually h0
        filter_upwards [h0, h3] with z hz hz'
        exact hz.trans hz'.symm
      have h2 := hK.eventually_forall_of_forall_eventually (P := fun x y => f (Sum.elim x y) = f (Sum.elim x₀ y)) h1
      filter_upwards [h2] with x hx
      funext y
      by_cases hy : y ∈ K
      · exact hx y hy
      · have hz : ∀ x', f (Sum.elim x' y) = 0 := by
          intro x'
          by_contra hne
          exact hy ⟨Sum.elim x' y, subset_tsupport f hne, rfl⟩
        rw [hz, hz]
    refine ⟨(hloc.comp l), ?_⟩
    refine HasCompactSupport.intro (hcs.isCompact.image (f := fun z : κ ⊕ κ' → k => z ∘ Sum.inl) (continuous_pi fun i => continuous_apply _)) ?_
    intro x hx
    have : (fun x₂ : κ' → k => f (Sum.elim x x₂)) = 0 := by
      funext x₂
      by_contra hne
      exact hx ⟨Sum.elim x x₂, subset_tsupport f hne, rfl⟩
    simp only [this, map_zero]

end GlobalTheory.SliceSB
