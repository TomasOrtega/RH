import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
namespace GlobalTheory.EvKer

/- English proof (translation)
Introduce `F _ _ κ _ e ei ev hSB hstd hpure hinj v ψ hψ hev`. Assume the negation of the conclusion as `hne`. Take `⟨f₀, hf₀⟩` from `GlobalTheory.TensUniq.exists_sInf_ne_zero F κ`. Use `set φ : ∀ w : Pl F, (κ → Fv F w) → ℂ := Function.update (fun w => stdInd F κ w) v ψ with hφdef`. Establish `hφSB : ∀ w, φ w ∈ SB (κ → Fv F w)`.

Introduce `w`. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Simplify `hψ` using `[φ]`. Simplify `GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) w` using `[φ, Function.update_of_ne h, stdInd]`.

Establish `hφev : ∀ᶠ w in cofinite, φ w = stdInd F κ w`. Conclude with `(Filter.eventually_cofinite_ne v).mono fun w h => by simp [φ, Function.update_of_ne h]`. Establish `hmem : pure f₀ φ ∈ schA F κ` using `GlobalTheory.TensUniq.pure_mem_schA f₀ φ hφSB (by simpa [stdInd] using hφev)`. Establish `hcomp : (fun w => ev w (φ w)) = Function.update (fun w => ev w (stdInd F κ w)) v 0`. Use function extensionality and compare the values at `w`.

Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Simplify using `[φ, hev]`. Simplify using `[φ, Function.update_of_ne h]`. Establish `hevstd : ∀ᶠ w in cofinite, (fun w => ev w (stdInd F κ w)) w = {x : κ → Fv F w | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F w}.indicator 1`.

Simplify `hstd` using `[stdInd]`. Take `⟨r, -, hr⟩` from `GlobalTheory.PureFactor.exists_rest_factor v (ei f₀) _ hevstd`. Establish `hzero : e (pure f₀ φ) = 0`. Rewrite using `[hpure f₀ φ hφSB hφev, hcomp, ← hr 0]`. Use function extensionality and compare the values at `x`.

Simplify using `[tens]`. Establish `h0 : pure f₀ φ = 0` using `hinj hmem (Submodule.zero_mem _) (by rw [hzero, map_zero])`. Establish `hall : ∀ w, φ w ≠ 0`. Introduce `w`. Distinguish the cases in `h : w = v`.

Substitute `h` using the available equality. Simplify `hne` using `[φ]`. Simplify using `only [φ, Function.update_of_ne h]`. Introduce `h1`. Use `congrFun h1 0` as an intermediate fact.

Simplify using `[stdInd, Set.indicator, zero_mem] at this`. Use `GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ φ hall (by simpa [stdInd] using hφev) h0` as an intermediate fact. Conclude with `hf₀ (by rw [this]; rfl)`.
-/
theorem ker_trivial : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  intro F _ _ κ _ e ei ev hSB hstd hpure hinj v ψ hψ hev
  classical
  by_contra hne
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  set φ : ∀ w : Pl F, (κ → Fv F w) → ℂ := Function.update (fun w => stdInd F κ w) v ψ with hφdef
  have hφSB : ∀ w, φ w ∈ SB (κ → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hψ
    · simpa [φ, Function.update_of_ne h, stdInd] using GlobalTheory.StdVacuum.indicator_mem_SB (κ := κ) w
  have hφev : ∀ᶠ w in cofinite, φ w = stdInd F κ w := by
    exact (Filter.eventually_cofinite_ne v).mono fun w h => by simp [φ, Function.update_of_ne h]
  have hmem : pure f₀ φ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA f₀ φ hφSB (by simpa [stdInd] using hφev)
  have hcomp : (fun w => ev w (φ w)) = Function.update (fun w => ev w (stdInd F κ w)) v 0 := by
    funext w
    by_cases h : w = v
    · subst h; simp [φ, hev]
    · simp [φ, Function.update_of_ne h]
  have hevstd : ∀ᶠ w in cofinite, (fun w => ev w (stdInd F κ w)) w =
      {x : κ → Fv F w | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F w}.indicator 1 := by
    simpa [stdInd] using hstd
  obtain ⟨r, -, hr⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f₀) _ hevstd
  have hzero : e (pure f₀ φ) = 0 := by
    rw [hpure f₀ φ hφSB hφev, hcomp, ← hr 0]
    funext x
    simp [tens]
  have h0 : pure f₀ φ = 0 := hinj hmem (Submodule.zero_mem _) (by rw [hzero, map_zero])
  have hall : ∀ w, φ w ≠ 0 := by
    intro w
    by_cases h : w = v
    · subst h; simpa [φ] using hne
    · simp only [φ, Function.update_of_ne h]
      intro h1
      have := congrFun h1 0
      simp [stdInd, Set.indicator, zero_mem] at this
  have := GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ φ hall (by simpa [stdInd] using hφev) h0
  exact hf₀ (by rw [this]; rfl)

end GlobalTheory.EvKer
