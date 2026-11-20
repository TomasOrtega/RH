import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharDotProductTrivialOnTsupportNhds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiDoubleUnfoldingBilinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiUnfoldingHeisenbergExchange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHeisenbergActionLineModulationTranslatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfTensColMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

/- English proof (translation)
Introduce `D k _ _ _ _ _ _ p ψ χ hχ`. Take `⟨ε, hε, hloc⟩` from `GlobalTheory.T.splitPlace_heisenbergAction_line_modulation_translation D k p ψ χ hχ`. Use `⟨ε, hε, ?_⟩` and prove the remaining obligations. Introduce `n n' n'' _ _ _ _ _ _ σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ _ L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' Ψ₁ Ψ₂ a a' b b' ha ha' hb hb' h1 h1' h2 h2' φ hφ`. Distinguish the cases in `hA0 : a = 0 ∧ a' = 0`.

Take `⟨rfl, rfl⟩` from `hA0`. Simplify using the standard rewrite rules. Distinguish the cases in `hB0 : b = 0 ∧ b' = 0`. Take `⟨rfl, rfl⟩` from `hB0`. Simplify using the standard rewrite rules.

Establish `hstd : IsStdChar D ψ (-1)` using `s₁.weil.std`. Take `⟨sbC, sbC', sbR, sbR'⟩` from `GlobalTheory.FinPl.tens_SB_iff k n n'`. Take `⟨sbC2, sbC2', sbR2, sbR2'⟩` from `GlobalTheory.FinPl.tens_SB_iff k n n''`. Establish `hΨ₁ : Ψ₁ ∈ SB (Matrix n n' k)`. Distinguish the cases in `h0 : a = 0`.

Conclude with `sbC' Ψ₁ a' h1'.2.2.2.1 (fun h => hA0 ⟨h0, h⟩)`. Conclude with `sbC' Ψ₁ a h1.2.2.2.1 h0`. Establish `hΨ₂ : Ψ₂ ∈ SB (Matrix n'' n k)`. Distinguish the cases in `h0 : b = 0`. Conclude with `sbR2' Ψ₂ b' h2'.2.2.2.1 (fun h => hB0 ⟨h0, h⟩)`.

Conclude with `sbR2' Ψ₂ b h2.2.2.2.1 h0`. Take `⟨⟨T₁, hT₁⟩, -⟩` from `h1.2.2.2.2`. Take `⟨⟨T₂, hT₂⟩, -⟩` from `h2.2.2.2.2`. Set `A : ((n → k) → ℂ) → (WO B.V₀ J.W₀ → ℂ)` to `fun a => T₁ (extFun α₀ β (tensCol Ψ₁ a))`. Set `Bb : ((n → k) → ℂ) → (WO J.W₀ B'.V₀ → ℂ)` to `fun b => T₂ (extFun β γ₀ (tensRow Ψ₂ b))`.

Establish `hA_eq : ∀ a₀ Ξ, Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) Ξ → Ξ = A a₀` using `fun a₀ Ξ h => h.2.2.2.2.2 T₁ hT₁`. Establish `hB_eq : ∀ b₀ Ξ, Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) Ξ → Ξ = Bb b₀` using `fun b₀ Ξ h => h.2.2.2.2.2 T₂ hT₂`. Establish `OB1` using `GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hstd B.V₀ J.W₀ α₀ β L₁ L₂ h1.1 h1.2.1 f₁ h1.2.2.1`. Establish `OB2` using `GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p (n'' ⊕ Fin 1) n ψ hstd J.W₀ B'.V₀ β γ₀ L₂' L₃ h2.1 h2.2.1 f₂ h2.2.2.1`. Establish `hA_over : ∀ a₀ ∈ SB (n → k), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) (A a₀)`.

Introduce `a₀ ha₀`. Take `⟨f, hf, -⟩` from `OB1.1 _ (sbC Ψ₁ a₀ hΨ₁ ha₀)`. Rewrite using `[← hA_eq a₀ f hf]` and apply the resulting hypothesis. Establish `hB_over : ∀ b₀ ∈ SB (n → k), Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) (Bb b₀)`. Introduce `b₀ hb₀`.

Take `⟨f, hf, -⟩` from `OB2.1 _ (sbR2 Ψ₂ b₀ hΨ₂ hb₀)`. Rewrite using `[← hB_eq b₀ f hf]` and apply the resulting hypothesis. Establish `hA_th : ∀ a₀ ∈ SB (n → k), IsThetaFunO ψ B.V₀ J.W₀ (A a₀)` using `fun a₀ h => (OB1.2.1 _ _ (hA_over a₀ h)).1`. Establish `hB_th : ∀ b₀ ∈ SB (n → k), IsThetaFunO ψ J.W₀ B'.V₀ (Bb b₀)` using `fun b₀ h => (OB2.2.1 _ _ (hB_over b₀ h)).1`. Establish `hA_add : ∀ a₀ a₁, A (a₀ + a₁) = A a₀ + A a₁`.

Introduce `a₀ a₁`. Use `show T₁ _ = T₁ _ + T₁ _`. Rewrite using `[← map_add]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only [extFun, tensCol, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hA_smul : ∀ (c : ℂ) a₀, A (c • a₀) = c • A a₀`. Introduce `c a₀`. Use `show T₁ _ = c • T₁ _`.

Rewrite using `[← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [extFun, tensCol, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> ring`.

Establish `hB_add : ∀ b₀ b₁, Bb (b₀ + b₁) = Bb b₀ + Bb b₁`. Introduce `b₀ b₁`. Use `show T₂ _ = T₂ _ + T₂ _`. Rewrite using `[← map_add]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [extFun, tensRow, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hB_smul : ∀ (c : ℂ) b₀, Bb (c • b₀) = c • Bb b₀`. Introduce `c b₀`.

Use `show T₂ _ = c • T₂ _`. Rewrite using `[← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [extFun, tensRow, Pi.smul_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs <;> ring`. Take `⟨add₁, smul₁, add₂, smul₂⟩` from `GlobalTheory.DoubleStepLin.besselFourierJacobi_doubleUnfolding_bilinear D ψ σ B J B' s₁ s₂ l vL φ hφ`. Take `⟨hχc, hχ1⟩` from `GlobalTheory.FinPl.SplitChar.cont_ne_one D k p ψ χ hχ hstd`. Set `χε : AddChar k Circle` to `χ.compAddMonoidHom (AddMonoidHom.mulLeft ε)`. Establish `hχε : ∀ x, χε x = χ (ε * x)` using `fun x => rfl`.

Apply the tactic sequence `have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [h]`. Establish `hχεc : Continuous χε` using `hχc.comp (continuous_const.mul continuous_id)`. Establish `hχε1 : χε ≠ 1`. Introduce `h`. Apply `hχ1` to reduce the goal to its premises.

Use extensionality with `x`. Use `congrArg (fun f : AddChar k Circle => f (ε * x)) h` as an intermediate fact. Simplify using `only [hχε, AddChar.one_apply] at this`. Rewrite `this` using `[← mul_assoc, hε2, one_mul]`. Simplify using `[this]`.

Establish `key : ∀ h₁ : GA D B'.A, ∃ c : ℂ, ∀ a₀ b₀ : SB (n → k), hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁ = c * ∫ η, (∫ y, a₀.1 y * (χε (η ⬝ᵥ y) : ℂ) ∂μ) * b₀.1 η ∂μ`. Introduce `h₁`. Set `Bf : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ` to `LinearMap.mk₂ ℂ (fun a₀ b₀ => hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁) (fun m₁ m₂ n₀ => by`. Simplify using `only [Submodule.coe_add, hA_add]`. Rewrite using `[add₁ _ _ _ (hA_th _ m₁.2) (hA_th _ m₂.2) (hB_th _ n₀.2)]`.

Use the proof step `rfl)`. Use the proof step `(fun c m n₀ => by`. Simplify using `only [Submodule.coe_smul, hA_smul]`. Rewrite using `[smul₁]`. Use the proof step `rfl)`.

Use the proof step `(fun m n₁ n₂ => by`. Simplify using `only [Submodule.coe_add, hB_add]`. Rewrite using `[add₂ _ _ _ (hA_th _ m.2) (hB_th _ n₁.2) (hB_th _ n₂.2)]`. Use the proof step `rfl)`. Use the proof step `(fun c m n₀ => by`.

Simplify using `only [Submodule.coe_smul, hB_smul]`. Rewrite using `[smul₂]`. Use the proof step `rfl)`. Take `⟨c, hc⟩` from `GlobalTheory.HeisLine.heis_invariant_form k n χε hχεc hχε1 μ Bf (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by`. Take `⟨⟨w₀, hw₁, hw₂⟩, -⟩` from `hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t`.

Establish `e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1)`. Establish `hfun : a₁.1 = fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a₀.1 y` using `funext fun y => by rw [ha₁ y, hχε]`. Rewrite using `[hfun]`. Conclude with `(hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm`. Establish `e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1)`.

Establish `hfun : b₁.1 = fun η => b₀.1 (η - t)` using `funext hb₁`. Rewrite using `[hfun]`. Conclude with `(hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm`. Use `show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁`. Rewrite using `[e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])`.

Use the proof step `(fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by`. Take `⟨-, ⟨w₀, hw₁, hw₂⟩⟩` from `hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t`. Establish `e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1)`. Establish `hfun : a₁.1 = fun y => a₀.1 (y - t)` using `funext ha₁`. Rewrite using `[hfun]`.

Conclude with `(hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm`. Establish `e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1)`. Establish `hfun : b₁.1 = fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b₀.1 η` using `funext fun η => by rw [hb₁ η, hχε]`. Rewrite using `[hfun]`. Conclude with `(hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm`.

Use `show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁`. Rewrite using `[e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])`. Conclude with `⟨c, fun a₀ b₀ => hc a₀ b₀⟩`. Establish `eΞ₁` using `hA_eq a Ξ₁ h1`. Establish `eΞ₁'` using `hA_eq a' Ξ₁' h1'`.

Establish `eΞ₂` using `hB_eq b Ξ₂ h2`. Establish `eΞ₂'` using `hB_eq b' Ξ₂' h2'`. Use function extensionality and compare the values at `h₁`. Take `⟨c, hc⟩` from `key h₁`. Establish `k1` using `hc ⟨a, ha⟩ ⟨b, hb⟩`.

Establish `k2` using `hc ⟨a', ha'⟩ ⟨b', hb'⟩`. Simplify using `only [hχε] at k1 k2`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[eΞ₁, eΞ₁', eΞ₂, eΞ₂', k1, k2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contraction_all : ∀ D : D7, GlobalTheory.FinPl.Contraction D := by
  intro D k _ _ _ _ _ _ p ψ χ hχ
  obtain ⟨ε, hε, hloc⟩ := GlobalTheory.T.splitPlace_heisenbergAction_line_modulation_translation D k p ψ χ hχ
  refine ⟨ε, hε, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ _ L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' Ψ₁ Ψ₂
    a a' b b' ha ha' hb hb' h1 h1' h2 h2' φ hφ
  by_cases hA0 : a = 0 ∧ a' = 0
  · obtain ⟨rfl, rfl⟩ := hA0
    simp
  by_cases hB0 : b = 0 ∧ b' = 0
  · obtain ⟨rfl, rfl⟩ := hB0
    simp
  have hstd : IsStdChar D ψ (-1) := s₁.weil.std
  obtain ⟨sbC, sbC', sbR, sbR'⟩ := GlobalTheory.FinPl.tens_SB_iff k n n'
  obtain ⟨sbC2, sbC2', sbR2, sbR2'⟩ := GlobalTheory.FinPl.tens_SB_iff k n n''
  have hΨ₁ : Ψ₁ ∈ SB (Matrix n n' k) := by
    by_cases h0 : a = 0
    · exact sbC' Ψ₁ a' h1'.2.2.2.1 (fun h => hA0 ⟨h0, h⟩)
    · exact sbC' Ψ₁ a h1.2.2.2.1 h0
  have hΨ₂ : Ψ₂ ∈ SB (Matrix n'' n k) := by
    by_cases h0 : b = 0
    · exact sbR2' Ψ₂ b' h2'.2.2.2.1 (fun h => hB0 ⟨h0, h⟩)
    · exact sbR2' Ψ₂ b h2.2.2.2.1 h0
  obtain ⟨⟨T₁, hT₁⟩, -⟩ := h1.2.2.2.2
  obtain ⟨⟨T₂, hT₂⟩, -⟩ := h2.2.2.2.2
  let A : ((n → k) → ℂ) → (WO B.V₀ J.W₀ → ℂ) := fun a => T₁ (extFun α₀ β (tensCol Ψ₁ a))
  let Bb : ((n → k) → ℂ) → (WO J.W₀ B'.V₀ → ℂ) := fun b => T₂ (extFun β γ₀ (tensRow Ψ₂ b))
  have hA_eq : ∀ a₀ Ξ, Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) Ξ → Ξ = A a₀ := fun a₀ Ξ h => h.2.2.2.2.2 T₁ hT₁
  have hB_eq : ∀ b₀ Ξ, Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) Ξ → Ξ = Bb b₀ := fun b₀ Ξ h => h.2.2.2.2.2 T₂ hT₂
  have OB1 := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hstd B.V₀ J.W₀ α₀ β L₁ L₂ h1.1 h1.2.1 f₁ h1.2.2.1
  have OB2 := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p (n'' ⊕ Fin 1) n ψ hstd J.W₀ B'.V₀ β γ₀ L₂' L₃ h2.1 h2.2.1 f₂ h2.2.2.1
  have hA_over : ∀ a₀ ∈ SB (n → k), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) (A a₀) := by
    intro a₀ ha₀
    obtain ⟨f, hf, -⟩ := OB1.1 _ (sbC Ψ₁ a₀ hΨ₁ ha₀)
    rwa [← hA_eq a₀ f hf]
  have hB_over : ∀ b₀ ∈ SB (n → k), Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) (Bb b₀) := by
    intro b₀ hb₀
    obtain ⟨f, hf, -⟩ := OB2.1 _ (sbR2 Ψ₂ b₀ hΨ₂ hb₀)
    rwa [← hB_eq b₀ f hf]
  have hA_th : ∀ a₀ ∈ SB (n → k), IsThetaFunO ψ B.V₀ J.W₀ (A a₀) := fun a₀ h => (OB1.2.1 _ _ (hA_over a₀ h)).1
  have hB_th : ∀ b₀ ∈ SB (n → k), IsThetaFunO ψ J.W₀ B'.V₀ (Bb b₀) := fun b₀ h => (OB2.2.1 _ _ (hB_over b₀ h)).1
  have hA_add : ∀ a₀ a₁, A (a₀ + a₁) = A a₀ + A a₁ := by
    intro a₀ a₁
    show T₁ _ = T₁ _ + T₁ _
    rw [← map_add]; congr 1; funext x
    simp only [extFun, tensCol, Pi.add_apply]
    split_ifs <;> ring
  have hA_smul : ∀ (c : ℂ) a₀, A (c • a₀) = c • A a₀ := by
    intro c a₀
    show T₁ _ = c • T₁ _
    rw [← map_smul]; congr 1; funext x
    simp only [extFun, tensCol, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  have hB_add : ∀ b₀ b₁, Bb (b₀ + b₁) = Bb b₀ + Bb b₁ := by
    intro b₀ b₁
    show T₂ _ = T₂ _ + T₂ _
    rw [← map_add]; congr 1; funext x
    simp only [extFun, tensRow, Pi.add_apply]
    split_ifs <;> ring
  have hB_smul : ∀ (c : ℂ) b₀, Bb (c • b₀) = c • Bb b₀ := by
    intro c b₀
    show T₂ _ = c • T₂ _
    rw [← map_smul]; congr 1; funext x
    simp only [extFun, tensRow, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  obtain ⟨add₁, smul₁, add₂, smul₂⟩ := GlobalTheory.DoubleStepLin.besselFourierJacobi_doubleUnfolding_bilinear D ψ σ B J B' s₁ s₂ l vL φ hφ
  obtain ⟨hχc, hχ1⟩ := GlobalTheory.FinPl.SplitChar.cont_ne_one D k p ψ χ hχ hstd
  let χε : AddChar k Circle := χ.compAddMonoidHom (AddMonoidHom.mulLeft ε)
  have hχε : ∀ x, χε x = χ (ε * x) := fun x => rfl
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [h]
  have hχεc : Continuous χε := hχc.comp (continuous_const.mul continuous_id)
  have hχε1 : χε ≠ 1 := by
    intro h
    apply hχ1
    ext x
    have := congrArg (fun f : AddChar k Circle => f (ε * x)) h
    simp only [hχε, AddChar.one_apply] at this
    rw [← mul_assoc, hε2, one_mul] at this
    simp [this]
  have key : ∀ h₁ : GA D B'.A, ∃ c : ℂ, ∀ a₀ b₀ : SB (n → k), hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁ =
      c * ∫ η, (∫ y, a₀.1 y * (χε (η ⬝ᵥ y) : ℂ) ∂μ) * b₀.1 η ∂μ := by
    intro h₁
    let Bf : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun a₀ b₀ => hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁)
      (fun m₁ m₂ n₀ => by
        simp only [Submodule.coe_add, hA_add]
        rw [add₁ _ _ _ (hA_th _ m₁.2) (hA_th _ m₂.2) (hB_th _ n₀.2)]; rfl)
      (fun c m n₀ => by
        simp only [Submodule.coe_smul, hA_smul]
        rw [smul₁]; rfl)
      (fun m n₁ n₂ => by
        simp only [Submodule.coe_add, hB_add]
        rw [add₂ _ _ _ (hA_th _ m.2) (hB_th _ n₁.2) (hB_th _ n₂.2)]; rfl)
      (fun c m n₀ => by
        simp only [Submodule.coe_smul, hB_smul]
        rw [smul₂]; rfl)
    obtain ⟨c, hc⟩ := GlobalTheory.HeisLine.heis_invariant_form k n χε hχεc hχε1 μ Bf
      (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by
        obtain ⟨⟨w₀, hw₁, hw₂⟩, -⟩ := hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t
        have e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1) := by
          have hfun : a₁.1 = fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a₀.1 y := funext fun y => by rw [ha₁ y, hχε]
          rw [hfun]
          exact (hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm
        have e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1) := by
          have hfun : b₁.1 = fun η => b₀.1 (η - t) := funext hb₁
          rw [hfun]
          exact (hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm
        show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁
        rw [e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])
      (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by
        obtain ⟨-, ⟨w₀, hw₁, hw₂⟩⟩ := hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t
        have e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1) := by
          have hfun : a₁.1 = fun y => a₀.1 (y - t) := funext ha₁
          rw [hfun]
          exact (hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm
        have e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1) := by
          have hfun : b₁.1 = fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b₀.1 η := funext fun η => by rw [hb₁ η, hχε]
          rw [hfun]
          exact (hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm
        show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁
        rw [e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])
    exact ⟨c, fun a₀ b₀ => hc a₀ b₀⟩
  have eΞ₁ := hA_eq a Ξ₁ h1
  have eΞ₁' := hA_eq a' Ξ₁' h1'
  have eΞ₂ := hB_eq b Ξ₂ h2
  have eΞ₂' := hB_eq b' Ξ₂' h2'
  funext h₁
  obtain ⟨c, hc⟩ := key h₁
  have k1 := hc ⟨a, ha⟩ ⟨b, hb⟩
  have k2 := hc ⟨a', ha'⟩ ⟨b', hb'⟩
  simp only [hχε] at k1 k2
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eΞ₁, eΞ₁', eΞ₂, eΞ₂', k1, k2]
  ring

end GlobalTheory.FinPl
