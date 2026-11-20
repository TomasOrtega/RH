import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisAdmissibleIffRepPureAvatar

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.AlgCharFromGal

/- English proof (translation)
Simplify using `[Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]`.
-/
theorem charpoly_fin_one {K : Type*} [CommRing K] (M : Matrix (Fin 1) (Fin 1) K) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

/- English proof (translation)
Introduce `D hA i π s z hz`. Take `⟨ρ, hc, h1, h2⟩` from `(hA i).2.2 π s (fun τ x hx => ⟨z τ, by`. Use `Multiset.mem_map_of_mem (fun y => y + (s : ℂ)) hx` as an intermediate fact. Rewrite using `[hz τ, Multiset.mem_singleton] at this⟩)` and apply the resulting hypothesis. Use `⟨ρ, hc, fun w hw hu B σ hB hσ => ?_, fun w hw => (h2 w hw).1, fun τ => ?_⟩` and prove the remaining obligations.

Establish `hu' : D.naut.unr (D.naut.wdOf i ρ w)`. Rewrite using `[h1 w hw]`. Conclude with `(D.naut.unr_tw _ _).2 hu`. Establish `e` using `D.naut.wdOf_frob i ρ w hw hc hu' B σ hB hσ`. Establish `hcard : Multiset.card (D.naut.frobEig (D.naut.wdOf i ρ w)) = 1`.

Rewrite using `[D.naut.frobEig_card _ hu', D.naut.wdOf_dim]`. Take `⟨α, hα⟩` from `Multiset.card_eq_one.1 hcard`. Rewrite `e` using `[hα, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Rewrite using `[← h1 w hw, hα]`. Use `congr 1`.

Establish `e0` using `congrArg (fun p => p.coeff 0) e`. Simplify using `using e0.symm`. Take `⟨w, hw, hτ⟩` from `GlobalTheory.GaloisInputCompare.exists_inducesW D.nd i τ`. Apply `Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective` to reduce the goal to its premises. Rewrite using `[(h2 w hw).2.2 τ hτ]`.

Establish `e` using `hz ((D.naut.iotaQC i).toRingHom.comp τ)`. Rewrite using `[show (fun y : ℂ => -(y + (s : ℂ))) = (fun y => -y) ∘ (fun y => y + (s : ℂ)) from rfl, ← Multiset.map_map, e]`. Simplify using the standard rewrite rules.
-/
theorem main : ∀ D : D7, SumRepresentations.adm2 D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  intro D hA i π s z hz
  obtain ⟨ρ, hc, h1, h2⟩ := (hA i).2.2 π s (fun τ x hx => ⟨z τ, by
      have := Multiset.mem_map_of_mem (fun y => y + (s : ℂ)) hx
      rwa [hz τ, Multiset.mem_singleton] at this⟩)
  refine ⟨ρ, hc, fun w hw hu B σ hB hσ => ?_, fun w hw => (h2 w hw).1, fun τ => ?_⟩
  · have hu' : D.naut.unr (D.naut.wdOf i ρ w) := by
      rw [h1 w hw]; exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ w hw hc hu' B σ hB hσ
    have hcard : Multiset.card (D.naut.frobEig (D.naut.wdOf i ρ w)) = 1 := by
      rw [D.naut.frobEig_card _ hu', D.naut.wdOf_dim]
    obtain ⟨α, hα⟩ := Multiset.card_eq_one.1 hcard
    rw [hα, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C] at e
    rw [← h1 w hw, hα]
    congr 1
    have e0 := congrArg (fun p => p.coeff 0) e
    simpa using e0.symm
  · obtain ⟨w, hw, hτ⟩ := GlobalTheory.GaloisInputCompare.exists_inducesW D.nd i τ
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(h2 w hw).2.2 τ hτ]
    have e := hz ((D.naut.iotaQC i).toRingHom.comp τ)
    rw [show (fun y : ℂ => -(y + (s : ℂ))) = (fun y => -y) ∘ (fun y => y + (s : ℂ)) from rfl,
      ← Multiset.map_map, e]
    simp

end GlobalTheory.AlgCharFromGal

end
