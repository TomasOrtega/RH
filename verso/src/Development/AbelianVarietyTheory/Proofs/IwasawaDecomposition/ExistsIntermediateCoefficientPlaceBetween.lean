import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl

/- English proof (translation)
Introduce `D₁ D₂ D₃ hR v₁ v₃ h13`. Establish `hmem : ∀ x : D₂.what₂.LL, D₂.what₂.embLL x ∈ D₃.what₂.embLL.fieldRange` using `fun x => by`. Take `⟨y, hy⟩` from `hR ⟨x, rfl⟩`. Conclude with `⟨y, hy⟩`. Set `ι : D₂.what₂.LL →+* D₃.what₂.LL` to `(D₃.what₂.embLL.rangeRestrictFieldEquiv).symm.toRingHom.comp (D₂.what₂.embLL.codRestrict _ hmem)`.

Establish `hι : ∀ x, D₃.what₂.embLL (ι x) = D₂.what₂.embLL x` using `fun x => by`. Use `(D₃.what₂.embLL.rangeRestrictFieldEquiv).apply_symm_apply ⟨D₂.what₂.embLL x, hmem x⟩` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Set `ιO : 𝓞 D₂.what₂.LL →+* 𝓞 D₃.what₂.LL` to `RingOfIntegers.mapRingHom ι`. Establish `hιO : ∀ x : 𝓞 D₂.what₂.LL, ((ιO x : 𝓞 D₃.what₂.LL) : D₃.what₂.LL) = ι (x : D₂.what₂.LL)` using `fun x => rfl`.

Use `set Q := (D₃.plEq v₃).asIdeal with hQ`. Set `P : Ideal (𝓞 D₂.what₂.LL)` to `Q.comap ιO`. Establish `hPprime : P.IsPrime` using `Ideal.comap_isPrime ιO Q`. Establish `hQne : Q ≠ ⊥` using `(D₃.plEq v₃).ne_bot`. Establish `hn : Ideal.absNorm Q ≠ 0`.

Introduce `h`. Conclude with `hQne (Ideal.absNorm_eq_zero_iff.mp h)`. Establish `hPne : P ≠ ⊥`. Introduce `h`. Establish `hin : ((Ideal.absNorm Q : ℕ) : 𝓞 D₂.what₂.LL) ∈ P` using `by show ιO _ ∈ Q`.

Rewrite using `[map_natCast]`. Conclude with `Ideal.absNorm_mem Q`. Rewrite `hin` using `[h, Ideal.mem_bot]`. Conclude with `hn (by exact_mod_cast hin)`. Use `⟨D₂.plEq.symm ⟨P, hPprime, hPne⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x₁ x₂ hx`. Rewrite using `[Equiv.apply_symm_apply]`. Use `show x₁ ∈ (D₁.plEq v₁).asIdeal ↔ ιO x₂ ∈ Q`. Conclude with `h13 x₁ (ιO x₂) (by rw [hιO, hι]; exact hx)`. Introduce `x₂ x₃ hx`.

Rewrite using `[Equiv.apply_symm_apply]`. Use `show ιO x₂ ∈ Q ↔ x₃ ∈ Q`. Establish `: ιO x₂ = x₃`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `D₃.what₂.embLL.injective` to reduce the goal to its premises.

Use `show D₃.what₂.embLL (ι (x₂ : D₂.what₂.LL)) = _`. Rewrite using `[hι]`. Conclude with `hx`. Rewrite using `[this]`.
-/
theorem exists_below_between : ∀ (D₁ D₂ D₃ : Formalism.BasicNotions.D7), Set.range D₂.what₂.embLL ⊆ Set.range D₃.what₂.embLL → ∀ (v₁ : D₁.what₂.places.Pl) (v₃ : D₃.what₂.places.Pl), GlobalTheory.Mem.Top.Bl.Below D₁ D₃ v₁ v₃ → ∃ v₂ : D₂.what₂.places.Pl, GlobalTheory.Mem.Top.Bl.Below D₁ D₂ v₁ v₂ ∧ GlobalTheory.Mem.Top.Bl.Below D₂ D₃ v₂ v₃ := by
  intro D₁ D₂ D₃ hR v₁ v₃ h13

  have hmem : ∀ x : D₂.what₂.LL, D₂.what₂.embLL x ∈ D₃.what₂.embLL.fieldRange := fun x => by
    obtain ⟨y, hy⟩ := hR ⟨x, rfl⟩
    exact ⟨y, hy⟩
  let ι : D₂.what₂.LL →+* D₃.what₂.LL :=
    (D₃.what₂.embLL.rangeRestrictFieldEquiv).symm.toRingHom.comp (D₂.what₂.embLL.codRestrict _ hmem)
  have hι : ∀ x, D₃.what₂.embLL (ι x) = D₂.what₂.embLL x := fun x => by
    have := (D₃.what₂.embLL.rangeRestrictFieldEquiv).apply_symm_apply ⟨D₂.what₂.embLL x, hmem x⟩
    exact congrArg Subtype.val this
  let ιO : 𝓞 D₂.what₂.LL →+* 𝓞 D₃.what₂.LL := RingOfIntegers.mapRingHom ι
  have hιO : ∀ x : 𝓞 D₂.what₂.LL, ((ιO x : 𝓞 D₃.what₂.LL) : D₃.what₂.LL) = ι (x : D₂.what₂.LL) := fun x => rfl
  set Q := (D₃.plEq v₃).asIdeal with hQ
  let P : Ideal (𝓞 D₂.what₂.LL) := Q.comap ιO
  have hPprime : P.IsPrime := Ideal.comap_isPrime ιO Q
  have hQne : Q ≠ ⊥ := (D₃.plEq v₃).ne_bot
  have hn : Ideal.absNorm Q ≠ 0 := by
    intro h; exact hQne (Ideal.absNorm_eq_zero_iff.mp h)
  have hPne : P ≠ ⊥ := by
    intro h
    have hin : ((Ideal.absNorm Q : ℕ) : 𝓞 D₂.what₂.LL) ∈ P := by
      show ιO _ ∈ Q
      rw [map_natCast]; exact Ideal.absNorm_mem Q
    rw [h, Ideal.mem_bot] at hin
    exact hn (by exact_mod_cast hin)
  refine ⟨D₂.plEq.symm ⟨P, hPprime, hPne⟩, ?_, ?_⟩
  · intro x₁ x₂ hx
    rw [Equiv.apply_symm_apply]
    show x₁ ∈ (D₁.plEq v₁).asIdeal ↔ ιO x₂ ∈ Q
    exact h13 x₁ (ιO x₂) (by rw [hιO, hι]; exact hx)
  · intro x₂ x₃ hx
    rw [Equiv.apply_symm_apply]
    show ιO x₂ ∈ Q ↔ x₃ ∈ Q
    have : ιO x₂ = x₃ := by
      apply Subtype.ext
      apply D₃.what₂.embLL.injective
      show D₃.what₂.embLL (ι (x₂ : D₂.what₂.LL)) = _
      rw [hι]; exact hx
    rw [this]

end GlobalTheory.Mem.Top.Bl
