import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hom_eq_id {a : (NE κ)ᵒᵖ} (f : a ⟶ a) : f = 𝟙 a :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/- English proof (translation)
Substitute using the available equality. Rewrite the conclusion using the stated equalities.
-/
theorem mp_single (c : CC F 0) (i j : κ) (hij : j = i) (h : sub (ne {j} (Finset.singleton_nonempty j)) ⊆
    sub (ne {i} (Finset.singleton_nonempty i))) (hc : ({j} : Finset κ).card = 0 + 1) :
    mp F (homOf h) (c ⟨{j}, hc⟩) = c ⟨{i}, Finset.card_singleton i⟩ := by
  subst hij
  rw [hom_eq_id (homOf h), mp_id]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem sum_cubeSign_two (t : Finset κ) (ht : t.card = 2) : ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem orderedCech_degreeZero_cocycles_correspond : (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧
    ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := by
  refine ⟨fun c _ he => ?_, fun g hg => ?_⟩
  · funext s
    obtain ⟨s, hs⟩ := s
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    have H := congrFun he (ne {i} (Finset.singleton_nonempty i))
    have hm : mn (ne {i} (Finset.singleton_nonempty i)) = i := Finset.min'_singleton i
    have := mp_single F c i _ hm
    simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] at H
    exact (this (Finset.singleton_subset_iff.2 (mn_mem _)) (Finset.card_singleton _)).symm.trans H
  · have hg' : ∀ {T T' : (NE κ)ᵒᵖ} (φ : T ⟶ T'), mp F φ (g T) = g T' := by
      intro T T' φ
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      exact (sub_eq_zero.1 this).symm
    refine ⟨fun s => g (ne s.1 (card_nonempty s)), ?_, ?_⟩
    · funext t
      rw [δ_apply]
      simp only [hg']
      rw [← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i),
        sum_cubeSign_two t.1 t.2, zero_smul]
      rfl
    · funext a
      simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact hg' _

end GlobalTheory.CechPoset
