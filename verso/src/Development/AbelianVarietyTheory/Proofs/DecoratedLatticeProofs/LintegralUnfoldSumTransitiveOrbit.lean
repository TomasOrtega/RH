import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace Unf

/- English proof (translation)
Introduce `H _ _ _ ν _ Γ _ Y _ _ y₀ htr 𝓕 𝓖 hF hG Φ hΦ hinv`. Use `set S : Subgroup H := (MulAction.stabilizer Γ y₀).map Γ.subtype with hSdef`. Use `haveI : Countable S := by`. Establish `hle : S ≤ Γ` using `Subgroup.map_subtype_le _`. Conclude with `Function.Injective.countable (Subgroup.inclusion_injective hle)`.

Use `choose σ hσ using htr`. Establish `hO : ∀ γ : Γ, γ • y₀ ∈ (Set.univ : Set Y)` using `fun _ => Set.mem_univ _`. Establish `hσ' : ∀ a : (Set.univ : Set Y), σ a • y₀ = a` using `fun a => hσ a`. Establish `hG'` using `GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO (fun a => σ a) hσ'`. Establish `hinvS : ∀ (s : S) (h : H), Φ y₀ (s • h) = Φ y₀ h`.

Introduce and unpack `⟨s, hs⟩ h`. Take `⟨t, ht, rfl⟩` from `Subgroup.mem_map.1 hs`. Use `hinv t y₀ h` as an intermediate fact. Rewrite `this` using `[show t • y₀ = y₀ from ht]`. Simplify `this` using `[Subgroup.smul_def]`.

Establish `hfun : ∀ (y : Y) (h : H), Φ y ((σ y : H) * h) = Φ y₀ h` using `fun y h => by`. Use `hinv (σ y) y₀ h` as an intermediate fact. Rewrite `this` using `[hσ y]`. Then use the resulting hypothesis. Establish `hlint : ∀ y : Y, ∫⁻ h in GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν` using `fun y => by`. Rewrite using `[← GlobalTheory.OrbitUnfold.setLIntegral_pull (σ y : H) (fun h => ‖Φ y h‖ₑ)]`.

Simplify using `only [hfun]`. Establish `hint : ∀ y : Y, ∫ h in GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), Φ y₀ h ∂ν = ∫ h in 𝓕, Φ y h ∂ν` using `fun y => by`. Rewrite using `[← GlobalTheory.OrbitUnfold.setIntegral_pull (σ y : H) (Φ y)]`. Simplify using `only [hfun]`. Establish `hd : Pairwise (Function.onFun (AEDisjoint ν) fun y : Y => GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H))`.

Introduce `a b hab`. Use `GlobalTheory.OrbitUnfold.aedisjoint_pull hF fun h => hab ?_` and prove the remaining obligations. Rewrite using `[← hσ a, ← hσ b, h]`. Establish `hU : (⋃ a : (Set.univ : Set Y), GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) = ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H)`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite `hG'` using `[hU]`. Establish `hL1 : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν` using `hG.setLIntegral_eq hG' (fun h => ‖Φ y₀ h‖ₑ) (fun s h => by simp only [hinvS])`. Establish `hL2 : ∫⁻ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν`. Rewrite using `[lintegral_iUnion₀ (fun y => GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hd]`.

Simplify using `only [hlint]`. Establish `hL3 : ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν` using `lintegral_tsum fun y => (hΦ y).enorm.aemeasurable`. Establish `hmain : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν`. Rewrite using `[hL1, hL2, hL3]`. Use `⟨hmain, fun hfin => ?_⟩` and prove the remaining obligations.

Establish `hfin' : ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤` using `by rwa [← hL3]`. Establish `hI : IntegrableOn (Φ y₀) (⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H)) ν`. Use `⟨(hΦ y₀).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[HasFiniteIntegral, hL2]`. Conclude with `lt_top_iff_ne_top.2 hfin'`.

Establish `hI1 : ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), Φ y₀ h ∂ν` using `hG.setIntegral_eq hG' (fun s h => hinvS s h)`. Rewrite using `[hI1, integral_iUnion_ae (fun y => GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hd hI]`. Simplify using `only [hint]`. Conclude with `(integral_tsum (fun y => (hΦ y).aestronglyMeasurable) hfin').symm`.
-/
theorem lintegral_integral_unfold_transitive : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  intro H _ _ _ ν _ Γ _ Y _ _ y₀ htr 𝓕 𝓖 hF hG Φ hΦ hinv
  set S : Subgroup H := (MulAction.stabilizer Γ y₀).map Γ.subtype with hSdef
  haveI : Countable S := by
    have hle : S ≤ Γ := Subgroup.map_subtype_le _
    exact Function.Injective.countable (Subgroup.inclusion_injective hle)
  choose σ hσ using htr
  have hO : ∀ γ : Γ, γ • y₀ ∈ (Set.univ : Set Y) := fun _ => Set.mem_univ _
  have hσ' : ∀ a : (Set.univ : Set Y), σ a • y₀ = a := fun a => hσ a
  have hG' := GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull hF y₀ hO (fun a => σ a) hσ'
  have hinvS : ∀ (s : S) (h : H), Φ y₀ (s • h) = Φ y₀ h := by
    rintro ⟨s, hs⟩ h
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have := hinv t y₀ h
    rw [show t • y₀ = y₀ from ht] at this
    simpa [Subgroup.smul_def] using this
  have hfun : ∀ (y : Y) (h : H), Φ y ((σ y : H) * h) = Φ y₀ h := fun y h => by
    have := hinv (σ y) y₀ h
    rwa [hσ y] at this
  have hlint : ∀ y : Y, ∫⁻ h in GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := fun y => by
    rw [← GlobalTheory.OrbitUnfold.setLIntegral_pull (σ y : H) (fun h => ‖Φ y h‖ₑ)]
    simp only [hfun]
  have hint : ∀ y : Y, ∫ h in GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), Φ y₀ h ∂ν
      = ∫ h in 𝓕, Φ y h ∂ν := fun y => by
    rw [← GlobalTheory.OrbitUnfold.setIntegral_pull (σ y : H) (Φ y)]
    simp only [hfun]
  have hd : Pairwise (Function.onFun (AEDisjoint ν) fun y : Y =>
      GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H)) := by
    intro a b hab
    refine GlobalTheory.OrbitUnfold.aedisjoint_pull hF fun h => hab ?_
    rw [← hσ a, ← hσ b, h]
  have hU : (⋃ a : (Set.univ : Set Y), GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H))
      = ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H) := by
    ext x; simp
  rw [hU] at hG'
  have hL1 : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν :=
    hG.setLIntegral_eq hG' (fun h => ‖Φ y₀ h‖ₑ) (fun s h => by simp only [hinvS])
  have hL2 : ∫⁻ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := by
    rw [lintegral_iUnion₀ (fun y => GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hd]
    simp only [hlint]
  have hL3 : ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
    lintegral_tsum fun y => (hΦ y).enorm.aemeasurable
  have hmain : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν := by
    rw [hL1, hL2, hL3]
  refine ⟨hmain, fun hfin => ?_⟩
  have hfin' : ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ := by rwa [← hL3]
  have hI : IntegrableOn (Φ y₀) (⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H)) ν := by
    refine ⟨(hΦ y₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL2]
    exact lt_top_iff_ne_top.2 hfin'
  have hI1 : ∫ h in 𝓖, Φ y₀ h ∂ν
      = ∫ h in ⋃ y : Y, GlobalTheory.OrbitUnfold.pull 𝓕 (σ y : H), Φ y₀ h ∂ν :=
    hG.setIntegral_eq hG' (fun s h => hinvS s h)
  rw [hI1, integral_iUnion_ae (fun y => GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _) hd hI]
  simp only [hint]
  exact (integral_tsum (fun y => (hΦ y).aestronglyMeasurable) hfin').symm

end Unf
end GlobalTheory
