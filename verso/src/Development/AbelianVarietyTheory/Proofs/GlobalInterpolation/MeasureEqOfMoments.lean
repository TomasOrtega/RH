import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMahlerExpansion

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomN

/- English proof (translation)
Introduce `q _ κ _ μ μ' h`. Set `e` to `Fintype.equivFin κ`. Set `π : C(κ → ℤ_[q], Fin (Fintype.card κ) → ℤ_[q])` to `⟨fun b i => b (e.symm i), by fun_prop⟩`. Set `π' : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q])` to `⟨fun a i => a (e i), by fun_prop⟩`. Set `Φ : C(Fin (Fintype.card κ) → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] C(κ → ℤ_[q], ℂ_[q])` to `{ toFun := fun G => G.comp π map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl cont := ContinuousMap.continuous_precomp π }`.

Establish `hz : (μ - μ').comp Φ = 0`. Use `GlobalTheory.MonomialDense.eq_zero_of_monomials q _ _ fun m k g hg => ?_` and prove the remaining obligations. Use `h m (fun l => e.symm (k l)) (Φ g) fun b => hg (π b)` as an intermediate fact. Simplify using `[this]`. Use extensionality with `F`.

Establish `hF : Φ (F.comp π') = F`. Use extensionality with `b`. Express the relevant statement in the definitionally equal form `F (π' (π b)) = F b`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[π, π']`. Use `congrArg (fun ν => ν (F.comp π')) hz` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, hF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply] at this`. Conclude with `sub_eq_zero.mp this`.
-/
theorem measure_eq_of_moments : ∀ (q : ℕ) [Fact q.Prime] (κ : Type) [Fintype κ]
    (μ μ' : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]),
    (∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])),
      (∀ a, f a = ∏ l, zc (a (j l))) → μ f = μ' f) → μ = μ' := by
  intro q _ κ _ μ μ' h
  let e := Fintype.equivFin κ
  let π : C(κ → ℤ_[q], Fin (Fintype.card κ) → ℤ_[q]) :=
    ⟨fun b i => b (e.symm i), by fun_prop⟩
  let π' : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q]) :=
    ⟨fun a i => a (e i), by fun_prop⟩
  let Φ : C(Fin (Fintype.card κ) → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] C(κ → ℤ_[q], ℂ_[q]) :=
    { toFun := fun G => G.comp π
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp π }
  have hz : (μ - μ').comp Φ = 0 := by
    refine GlobalTheory.MonomialDense.eq_zero_of_monomials q _ _ fun m k g hg => ?_
    have := h m (fun l => e.symm (k l)) (Φ g) fun b => hg (π b)
    simp [this]
  ext F
  have hF : Φ (F.comp π') = F := by
    ext b
    change F (π' (π b)) = F b
    congr 1
    funext i
    simp [π, π']
  have := congrArg (fun ν => ν (F.comp π')) hz
  simp only [ContinuousLinearMap.comp_apply, hF, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.MomN
