import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSumOfInputs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
end GlobalTheory.IneAway
namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels
end GlobalTheory.TypeLeaf
namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise
end GlobalTheory.TypeLeaf.ConjPlace
namespace GlobalTheory.AdmTame
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
/- English proof (translation)
Introduce `D h0 hG hA hL`. Take `⟨hLP, hAut, -⟩` from `h0`. Establish `hW : GlobalTheory.TypeLeaf.WildOne D` using `hL.1`. Establish `hGal : _root_.UpperTheory.GalS.GalAwayN D` using `_root_.GlobalTheory.AdmTame.galAwayOfS' hG`. Establish `hF : GlobalTheory.TypeLeaf.FrobDense D`.

Introduce `T hT`. Rewrite using `[dense_iff_closure_eq]`. Conclude with `hA.2.2.1 T hT`. Establish `hCL : GlobalTheory.TypeLeaf.CharLaws D`. Introduce `w a χ χ' hχ hχ'`.

Take `⟨-, -, -, h4, h5, -⟩` from `hLP w a a χ χ' 0 hχ hχ'`. Conclude with `⟨h4, h5⟩`. Establish `hM : GlobalTheory.TypeLeaf.MultOne D`. Introduce `a π π' ha h`. Establish `hp` using `hA.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by simp [isoLoc, spehLoc, h w])`.

Rewrite `hp` using `[List.singleton_perm_singleton]`. Simplify using `only [Formalism.BasicNotions.Part.mk.injEq, heq_eq_eq, true_and] at hp`. Conclude with `hp.1`. Establish `hT : GlobalTheory.TypeLeaf.TwistInv D` using `GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D hCL hM`. Establish `hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)`.

Introduce `τ z hz`. Take `⟨m, hm⟩` from `D.R.t_odd`. Take `⟨h1, h2⟩` from `hAut.2.1 τ`. Rewrite `hz` using `[h2]`. Apply the tactic sequence `rcases h1 with h1 | h1 <;> rw [h1] at hz <;> simp at hz <;> subst hz`.

Use `⟨-(m : ℤ) - 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-(m : ℤ), ?_⟩` and prove the remaining obligations.

Rewrite using `[hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : GlobalTheory.TypeLeaf.PointPar D` using `GlobalTheory.TypeLeaf.pointPar_of_twist D hT hAut.1.1 hz`. Introduce `i Sig hx hf hsq hc ρ hρ`.

Conclude with `_root_.GlobalTheory.TypeLeaf.tameSum_of_inputs_alt D hW (GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime D) hGal hF hP i Sig hx (_root_.UpperTheory.GalS.fullLabS_of_fullLabS_trivial ⟨hf, fun k v => hL.2 k v _ (hf k v) (hsq k v) (DiscreteGroups.sglob.DzType.big_of_le_n …`. Take `⟨π, rfl⟩` from `hc`. Rewrite using `[GlobalTheory.InertialTypesCmp.lpDim_isoLoc]`. Simplify using `[rankIso, Ranks.nV]))⟩) hc ρ hρ`.
-/
theorem main_alt_alt_alt : ∀ D : D7, SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → SumRepresentations.adm5 D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.AdmissibleResidualTameEigenvalues D := by
  intro D h0 hG hA hL
  obtain ⟨hLP, hAut, -⟩ := h0
  have hW : GlobalTheory.TypeLeaf.WildOne D := hL.1
  have hGal : _root_.UpperTheory.GalS.GalAwayN D := _root_.GlobalTheory.AdmTame.galAwayOfS' hG
  have hF : GlobalTheory.TypeLeaf.FrobDense D := by
    intro T hT
    rw [dense_iff_closure_eq]
    exact hA.2.2.1 T hT
  have hCL : GlobalTheory.TypeLeaf.CharLaws D := by
    intro w a χ χ' hχ hχ'
    obtain ⟨-, -, -, h4, h5, -⟩ := hLP w a a χ χ' 0 hχ hχ'
    exact ⟨h4, h5⟩
  have hM : GlobalTheory.TypeLeaf.MultOne D := by
    intro a π π' ha h
    have hp := hA.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
      (Filter.Eventually.of_forall fun w => by simp [isoLoc, spehLoc, h w])
    rw [List.singleton_perm_singleton] at hp
    simp only [Formalism.BasicNotions.Part.mk.injEq, heq_eq_eq, true_and] at hp
    exact hp.1
  have hT : GlobalTheory.TypeLeaf.TwistInv D := GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D hCL hM
  have hz : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ,
      ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
    intro τ z hz
    obtain ⟨m, hm⟩ := D.R.t_odd
    obtain ⟨h1, h2⟩ := hAut.2.1 τ
    rw [h2] at hz
    rcases h1 with h1 | h1 <;> rw [h1] at hz <;> simp at hz <;> subst hz
    · refine ⟨-(m : ℤ) - 1, ?_⟩
      rw [hm]; push_cast; ring
    · refine ⟨-(m : ℤ), ?_⟩
      rw [hm]; push_cast; ring
  have hP : GlobalTheory.TypeLeaf.PointPar D := GlobalTheory.TypeLeaf.pointPar_of_twist D hT hAut.1.1 hz
  intro i Sig hx hf hsq hc ρ hρ
  exact _root_.GlobalTheory.TypeLeaf.tameSum_of_inputs_alt D hW (GlobalTheory.T.firstCharacter_trivial_wildInertia_typePrime D) hGal hF hP i Sig hx
    (_root_.UpperTheory.GalS.fullLabS_of_fullLabS_trivial ⟨hf, fun k v => hL.2 k v _ (hf k v) (hsq k v) (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by
      obtain ⟨π, rfl⟩ := hc
      rw [GlobalTheory.InertialTypesCmp.lpDim_isoLoc]
      simp [rankIso, Ranks.nV]))⟩) hc ρ hρ
end GlobalTheory.AdmTame
end
end
