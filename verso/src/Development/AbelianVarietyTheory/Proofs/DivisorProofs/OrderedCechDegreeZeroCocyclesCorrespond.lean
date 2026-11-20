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
The claim follows from `Quiver.Hom.unop_inj (Subsingleton.elim _ _)`.
-/
theorem hom_eq_id {a : (NE κ)ᵒᵖ} (f : a ⟶ a) : f = 𝟙 a :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/- English proof (translation)
Substitute `hij` using the available equality. Rewrite using `[hom_eq_id (homOf h), mp_id]`.
-/
theorem mp_single (c : CC F 0) (i j : κ) (hij : j = i) (h : sub (ne {j} (Finset.singleton_nonempty j)) ⊆
    sub (ne {i} (Finset.singleton_nonempty i))) (hc : ({j} : Finset κ).card = 0 + 1) :
    mp F (homOf h) (c ⟨{j}, hc⟩) = c ⟨{i}, Finset.card_singleton i⟩ := by
  subst hij
  rw [hom_eq_id (homOf h), mp_id]

/- English proof (translation)
Take `⟨x, y, hxy, rfl⟩` from `Finset.card_eq_two.1 ht`. Rewrite using `[Finset.sum_pair hxy]`. Break down `lt_or_gt_of_ne hxy with h | h` into its components or cases. Simplify using `[GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]`. Simplify using `[GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]`.
-/
theorem sum_cubeSign_two (t : Finset κ) (ht : t.card = 2) : ∑ i ∈ t, GlobalTheory.cubeSign t i = 0 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hxy]
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]
  · simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h, h.not_gt]

/- English proof (translation)
Use `⟨fun c _ he => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Take `⟨s, hs⟩` from `s`. Take `⟨i, rfl⟩` from `Finset.card_eq_one.1 hs`. Establish `H` using `congrFun he (ne {i} (Finset.singleton_nonempty i))`.

Establish `hm : mn (ne {i} (Finset.singleton_nonempty i)) = i` using `Finset.min'_singleton i`. Use `mp_single F c i _ hm` as an intermediate fact. Simplify using `only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] at H`. Conclude with `(this (Finset.singleton_subset_iff.2 (mn_mem _)) (Finset.card_singleton _)).symm.trans H`. Establish `hg' : ∀ {T T' : (NE κ)ᵒᵖ} (φ : T ⟶ T'), mp F φ (g T) = g T'`.

Introduce `T T' φ`. Use `congrFun (congrFun (congrFun hg T) T') φ` as an intermediate fact. Rewrite `this` using `[amitsur_d0_apply]`. Conclude with `(sub_eq_zero.1 this).symm`. Use `⟨fun s => g (ne s.1 (card_nonempty s)), ?_, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `t`. Rewrite using `[δ_apply]`. Simplify using `only [hg']`. Rewrite using `[← Finset.sum_smul, Finset.sum_coe_sort t.1 (fun i => GlobalTheory.cubeSign t.1 i), sum_cubeSign_two t.1 t.2, zero_smul]`. Both sides reduce to the same expression.

Use function extensionality and compare the values at `a`. Simplify using `only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Conclude with `hg' _`.
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
