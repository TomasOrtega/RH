import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.MatCoefLevel

/- English proof (translation)
Introduce `D ψ hψ S T μ 𝓕 hcov f f₀ hf hf₀`. Take `⟨U₁, hU₁, hl₁⟩` from `hf.level`. Take `⟨U₂, hU₂, hl₂⟩` from `hf₀.level`. Use `⟨U₁ ⊓ U₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.coe_inf]`.

Conclude with `hU₁.inter hU₂`. Introduce `w hw u hu hinf`. Take `⟨hμ, h𝓕, -⟩` from `hcov`. Establish `hu₁ : heisO ψ S T u f = f` using `hl₁ u (AddSubgroup.mem_inf.1 hu).1 hinf`. Establish `hu₂ : heisO ψ S T u f₀ = f₀` using `hl₂ u (AddSubgroup.mem_inf.1 hu).2 hinf`.

Establish `hg` using `GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ w`. Establish `e1` using `GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf hg u`. Rewrite `e1` using `[hu₁, heisO_comm, hu₂]`. Establish `e2 : GlobalTheory.Ker.ipO μ 𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) = starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀)`. Unfold `GlobalTheory.Ker.ipO`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `e1` using `[e2]`. Establish `hw' : GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) ≠ 0` using `hw`. Establish `h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) = 0`. Take the linear combination `e1`. Establish `h4 : starRingEnd ℂ (ψ (symplO S T u w)) = 1` using `sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hw')`.

Establish `h5 : ψ (symplO S T u w) = 1`. Establish `h6` using `congrArg (starRingEnd ℂ) h4`. Rewrite `h6` using `[Complex.conj_conj, map_one]`. Then use the resulting hypothesis. Conclude with `(psi_symplO_swap ψ _ _).1 h5`.
-/
theorem matCoef_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, thPair μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1 := by
  intro D ψ hψ S T μ 𝓕 hcov f f₀ hf hf₀
  obtain ⟨U₁, hU₁, hl₁⟩ := hf.level
  obtain ⟨U₂, hU₂, hl₂⟩ := hf₀.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro w hw u hu hinf
  obtain ⟨hμ, h𝓕, -⟩ := hcov
  have hu₁ : heisO ψ S T u f = f := hl₁ u (AddSubgroup.mem_inf.1 hu).1 hinf
  have hu₂ : heisO ψ S T u f₀ = f₀ := hl₂ u (AddSubgroup.mem_inf.1 hu).2 hinf
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ w
  have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf hg u
  rw [hu₁, heisO_comm, hu₂] at e1
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
      starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) := by
    unfold GlobalTheory.Ker.ipO
    rw [← integral_const_mul]
    congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  rw [e2] at e1
  have hw' : GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) ≠ 0 := hw
  have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO μ 𝓕 f (heisO ψ S T w f₀) = 0 := by
    linear_combination e1
  have h4 : starRingEnd ℂ (ψ (symplO S T u w)) = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hw')
  have h5 : ψ (symplO S T u w) = 1 := by
    have h6 := congrArg (starRingEnd ℂ) h4
    rwa [Complex.conj_conj, map_one] at h6
  exact (psi_symplO_swap ψ _ _).1 h5

end GlobalTheory.MatCoefLevel

end
