import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.LabAtRealPlace

/- English proof (translation)
Establish `h1 : D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) ∈ D.R.Psi`. Rewrite using `[show D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) = (D.eTau τ).1 from D.host.gal.apply_symm_apply _]`. Conclude with `(D.eTau τ).2`. Conclude with `(D.host.galE_mem_Psi_iff _).1 h1`.
-/
theorem sigmaOf_sqrt (D : D7) (τ : D.what₂.Tau) :
    D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD = D.host.sqrtMinusD := by
  have h1 : D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) ∈
      D.R.Psi := by
    rw [show D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) = (D.eTau τ).1 from D.host.gal.apply_symm_apply _]
    exact (D.eTau τ).2
  exact (D.host.galE_mem_Psi_iff _).1 h1

/- English proof (translation)
Establish `hm : D.host.sqrtMinusD ∈ D.host.K` using `IntermediateField.mem_adjoin_simple_self ℚ _`. Establish `e1 : Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = σ (D.embE D.host.sqrtMinusD)` using `by show σ (D.embE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD)) = _`. Rewrite using `[sigmaOf_sqrt]`. Establish `e2 : Formalism.IndefR.Conj.labE D.what₂.embLL ρ D.host.sqrtMinusD = D.what₂.embLL (D.embE D.host.sqrtMinusD)` using `by show D.what₂.embLL (D.embE (D.host.sigmaOf ((D.eTau ρ).1 : D.R.GG) D.host.sqrtMinusD)) = _`. Rewrite using `[sigmaOf_sqrt]`.

Rewrite using `[e1, h.2 _ hm, ← e2, Formalism.IndefR.Conj.labE_base]`.
-/
theorem labE_sqrt (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (τ ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = tauE D ρ D.host.sqrtMinusD := by
  have hm : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have e1 : Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = σ (D.embE D.host.sqrtMinusD) := by
    show σ (D.embE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  have e2 : Formalism.IndefR.Conj.labE D.what₂.embLL ρ D.host.sqrtMinusD = D.what₂.embLL (D.embE D.host.sqrtMinusD) := by
    show D.what₂.embLL (D.embE (D.host.sigmaOf ((D.eTau ρ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  rw [e1, h.2 _ hm, ← e2, Formalism.IndefR.Conj.labE_base]

/- English proof (translation)
Establish `hex : ∃ τ, Formalism.IndefR.Links.labE σ τ = tauE D ρ ∨ Formalism.IndefR.Links.labE σ τ = (starRingEnd ℂ).comp (tauE D ρ)`. Take `⟨B, hB⟩` from `Formalism.IndefR.Conj.labExists σ`. Establish `h'` using `hB (B.perm.symm ρ)`. Rewrite `h'` using `[Formalism.IndefR.Conj.ArchLab.emb, Equiv.apply_symm_apply]`. Use `⟨B.perm.symm ρ, ?_⟩` and prove the remaining obligations.

Use `split_ifs at h'`. Use `exacts [Or.inl h', Or.inr h']`. Rewrite using `[Formalism.IndefR.Links.lab, dif_pos hex]`. Use `hex.choose_spec.resolve_right fun h' => ?_` and prove the remaining obligations. Establish `h2` using `labE_sqrt D σ s h hex.choose ρ`.

Rewrite `h2` using `[h', RingHom.comp_apply]`. Take `⟨x, hx⟩` from `Complex.conj_eq_iff_real.1 h2`. Establish `h3 : (tauE D ρ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ)`. Rewrite using `[← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]`. Rewrite `h3` using `[hx]`.

Establish `h4 : x ^ 2 = -(D.host.d : ℝ)` using `by exact_mod_cast h3`. Establish `h5 : (0 : ℝ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`. Use polynomial arithmetic with `[sq_nonneg x]`.
-/
theorem labE_lab (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := by
  have hex : ∃ τ, Formalism.IndefR.Links.labE σ τ = tauE D ρ ∨
      Formalism.IndefR.Links.labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    obtain ⟨B, hB⟩ := Formalism.IndefR.Conj.labExists σ
    have h' := hB (B.perm.symm ρ)
    rw [Formalism.IndefR.Conj.ArchLab.emb, Equiv.apply_symm_apply] at h'
    refine ⟨B.perm.symm ρ, ?_⟩
    split_ifs at h'
    exacts [Or.inl h', Or.inr h']
  rw [Formalism.IndefR.Links.lab, dif_pos hex]
  refine hex.choose_spec.resolve_right fun h' => ?_
  have h2 := labE_sqrt D σ s h hex.choose ρ
  rw [h', RingHom.comp_apply] at h2
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : (tauE D ρ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
  rw [hx] at h3
  have h4 : x ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  nlinarith [sq_nonneg x]

/- English proof (translation)
Introduce `D σ s h ρ` and use `labE_lab D σ s h ρ`.
-/
theorem main : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s → ∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := fun D σ s h ρ => labE_lab D σ s h ρ

end GlobalTheory.LabAtRealPlace
