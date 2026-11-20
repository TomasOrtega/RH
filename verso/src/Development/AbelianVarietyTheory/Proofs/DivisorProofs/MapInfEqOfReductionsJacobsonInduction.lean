import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

/- English proof (translation)
Use `haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a a' inferInstance fun e => (h e) ▸ le_sup_left`. Conclude with `GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a' a inferInstance fun e => (h e).symm ▸ le_sup_left`.
-/
theorem eq_of_sup_baseIdeal_pow_eq {C : Type} [CommRing C] [IsNoetherianRing C] {J : Ideal C}
    (hJ : J ≤ Ideal.jacobson ⊥) {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of C)) [IsProper p]
    (a a' : V.IdealSheafData)
    (h : ∀ e : ℕ, a ⊔ baseIdeal p (J ^ (e + 1)) = a' ⊔ baseIdeal p (J ^ (e + 1))) : a = a' := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  refine le_antisymm ?_ ?_
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a a' inferInstance fun e => (h e) ▸ le_sup_left
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a' a inferInstance fun e => (h e).symm ▸ le_sup_left

/- English proof (translation)
Introduce `C _ _ J hJ W' π U hπ hU K τ hK`. Take `⟨k₀, hk₀⟩` from `GlobalTheory.T.exists_map_comap_inf_sup_pow_eq (Spec (CommRingCat.of C)) W' π U inferInstance hU K τ hK`. Use `⟨k₀, fun k hk T' T'' h' h'' => ?_⟩` and prove the remaining obligations. Establish `e' : T' = τ.comap π`. Use `eq_of_sup_baseIdeal_pow_eq hJ π _ _ fun e => ?_` and prove the remaining obligations.

Rewrite using `[h' e, Scheme.IdealSheafData.comap_sup, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, Category.comp_id]`. Establish `e'' : T'' = τ ⊔ K ^ k`. Use `eq_of_sup_baseIdeal_pow_eq hJ (𝟙 _) _ _ fun e => ?_` and prove the remaining obligations. Rewrite using `[h'' e, sup_right_comm]`. Rewrite using `[e', e'']`.

Conclude with `hk₀ k hk`.
-/
theorem map_inf_eq_of_reductions : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  intro C _ _ J hJ W' π U hπ hU K τ hK
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_map_comap_inf_sup_pow_eq (Spec (CommRingCat.of C)) W' π U inferInstance hU K τ hK
  refine ⟨k₀, fun k hk T' T'' h' h'' => ?_⟩
  have e' : T' = τ.comap π := by
    refine eq_of_sup_baseIdeal_pow_eq hJ π _ _ fun e => ?_
    rw [h' e, Scheme.IdealSheafData.comap_sup, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, Category.comp_id]
  have e'' : T'' = τ ⊔ K ^ k := by
    refine eq_of_sup_baseIdeal_pow_eq hJ (𝟙 _) _ _ fun e => ?_
    rw [h'' e, sup_right_comm]
  rw [e', e'']
  exact hk₀ k hk

end GlobalTheory.FormalAlg
