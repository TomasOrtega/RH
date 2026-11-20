import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEquality
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
noncomputable section

namespace GlobalTheory.HeckeCharacterEquality

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

def _root_.UpperTheory.GalS.HeckeCharacterEqualityOfRealisation : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      UpperTheory.GalS.RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG χ w) s)) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'

/- English proof (translation)
Introduce `D hA i χ χ' s ρ h h'`. Establish `hAN` using `hA.1.1.2.2.2.2.2.2.1`. Establish `hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.locG χ w) → D.naut.locG χ w = D.naut.locG χ' w`. Introduce `w hw hu`. Establish `e` using `congrArg (fun a => D.naut.lpTw a (-s)) (((h w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)).symm.trans (h' w hw))`.

Simplify `e` using `[D.naut.lpTw_add, D.naut.lpTw_zero]`. Establish `hp` using `hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by`. Establish `hfin` using `placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero`. Use `filter_upwards [hfin.compl_mem_cofinite, D.naut.locG_unr_ae χ] with w hw hu`. Simplify using `only [isoLoc, spehLoc, List.foldr]`.

Rewrite using `[hloc w hw hu])`. Use `List.perm_singleton.1 hp` as an intermediate fact. Simplify using `using this`.
-/
theorem heckeCharacterEqualityOfRealisation : UpperTheory.GalS.HeckeCharacterEqualityOfRealisation := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.locG χ w) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw hu
    have e := congrArg (fun a => D.naut.lpTw a (-s)) (((h w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite, D.naut.locG_unr_ae χ] with w hw hu
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw hu])
  have := List.perm_singleton.1 hp
  simpa using this

end GlobalTheory.HeckeCharacterEquality

end
