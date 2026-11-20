import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

/- English proof (translation)
The claim follows from `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by by_cases h : TrivSqZeroExt.fst x = 0 · right rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] simp [h] · left rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] exact isUnit_iff_ne_zero.2 h`.
-/
theorem isLocalRing_dualNumber_field (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

/- English proof (translation)
Take `⟨V, hV, h⟩` from `exists_pull_eq_zero c (IsLocalRing.closedPoint R)`. Establish `hV' : V = ⊤` using `(IsLocalRing.closedPoint_mem_iff V).1 hV`. Establish `e` using `pull_eq_zero_of_mem V (𝟙 _) (fun z ↦ by rw [hV']; trivial) h`. Rewrite `e` using `[pull_id]`. Then use the resulting hypothesis.
-/
theorem pic_sp_local_eq_zero (R : Type) [CommRing R] [IsLocalRing R] (c : Pic (Sp R)) : c = 0 := by
  obtain ⟨V, hV, h⟩ := exists_pull_eq_zero c (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have e := pull_eq_zero_of_mem V (𝟙 _) (fun z ↦ by rw [hV']; trivial) h
  rwa [pull_id] at e

/- English proof (translation)
Establish `hε : φ DualNumber.eps = 0`. Establish `e : φ DualNumber.eps * φ DualNumber.eps = 0` using `by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]`. Conclude with `mul_self_eq_zero.1 e`. Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := by ext <;> simp`.

Use `conv_lhs => rw [hx]`. Rewrite using `[map_add, DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, hε, mul_zero, add_zero]`. Both sides reduce to the same expression.
-/
theorem ringHom_dualNumber_factor {k K : Type} [CommRing k] [Field K] (φ : DualNumber k →+* K) :
    φ = (φ.comp (dnInl k)).comp (dnFst k) := by
  have hε : φ DualNumber.eps = 0 := by
    have e : φ DualNumber.eps * φ DualNumber.eps = 0 := by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 e
  refine RingHom.ext fun x ↦ ?_
  have hx : x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul, hε, mul_zero, add_zero]
  rfl

/- English proof (translation)
Introduce `S A _ hA k _ s D hD h0`. Use `haveI := isLocalRing_dualNumber_field k`. Use `haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))`. Use `haveI : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)`. Use `haveI : IsLocallyNoetherian (Over.mk s).left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))`.

Use `⟨hD, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A (Over.mk s) hA D hD ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[triv_ev_iff hD]`. Conclude with `pic_sp_local_eq_zero _ _`. Introduce `K _ _ s' t`. Take `⟨φ, hφ⟩` from `Spec.map_surjective t.left`.

Use `set ψ : k →+* K := φ.hom.comp (dnInl k)`. Establish `ht : t.left = spMap ψ ≫ spMap (dnFst k)`. Rewrite using `[← hφ, ← Spec.map_comp]`. Use `congr 1`. Use `ext1`.

Conclude with `ringHom_dualNumber_factor φ.hom`. Establish `hN : (ev D (fst A (Over.mk s')) (snd A (Over.mk s') ≫ t)).IsLB` using `pull_isLB hD _`. Use `(isAdditive_iff hN).2 fun Y a a' y ↦ ?_` and prove the remaining obligations. Establish `key : ∀ b : Y ⟶ A, evc hN b y = 0` using `fun b ↦ by`. Rewrite using `[evc_ev hD, lift_fst, lift_snd_assoc]`.

Set `u : Y ⟶ Over.mk (spMap (dnFst k) ≫ s)` to `Over.homMk (y.left ≫ spMap ψ) (by`. Establish `e1 : y.left ≫ s' = Y.hom` using `by simpa using Over.w y`. Establish `e2 : t.left ≫ s = s'` using `by simpa using Over.w t`. Simplify using `only [Over.mk_hom]`. Rewrite using `[Category.assoc, ← Category.assoc (spMap ψ), ← ht, e2, e1])`.

Establish `hu : y ≫ t = u ≫ ptMap s (dnFst k)`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Simplify using `only [Over.comp_left, ptMap_left, ht]`. Both sides reduce to the same expression. Rewrite using `[hu, evc, ← lift_whiskerLeft, Over.comp_left, pull_comp, h0, map_zero]`.

Rewrite using `[key, key, key, add_zero]`.
-/
theorem fam_of_triv_mod_eps : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k]
    (s : Sp (DualNumber k) ⟶ S) (D : LB (A ⊗ Over.mk s).left) (hD : D.IsLB),
    GlobalTheory.CechPic.pull (A ◁ ptMap s (dnFst k)).left (cls D hD) = 0 → Fam A D := by
  intro S A _ hA k _ s D hD h0
  haveI := isLocalRing_dualNumber_field k
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k (DualNumber k)
  haveI : IsLocallyNoetherian (Over.mk s).left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  refine ⟨hD, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A (Over.mk s) hA D hD ?_ ?_⟩
  · rw [triv_ev_iff hD]
    exact pic_sp_local_eq_zero _ _
  · intro K _ _ s' t
    obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
    set ψ : k →+* K := φ.hom.comp (dnInl k)
    have ht : t.left = spMap ψ ≫ spMap (dnFst k) := by
      rw [← hφ, ← Spec.map_comp]
      congr 1
      ext1
      exact ringHom_dualNumber_factor φ.hom
    have hN : (ev D (fst A (Over.mk s')) (snd A (Over.mk s') ≫ t)).IsLB := pull_isLB hD _
    refine (isAdditive_iff hN).2 fun Y a a' y ↦ ?_
    have key : ∀ b : Y ⟶ A, evc hN b y = 0 := fun b ↦ by
      rw [evc_ev hD, lift_fst, lift_snd_assoc]
      let u : Y ⟶ Over.mk (spMap (dnFst k) ≫ s) := Over.homMk (y.left ≫ spMap ψ) (by
        have e1 : y.left ≫ s' = Y.hom := by simpa using Over.w y
        have e2 : t.left ≫ s = s' := by simpa using Over.w t
        simp only [Over.mk_hom]
        rw [Category.assoc, ← Category.assoc (spMap ψ), ← ht, e2, e1])
      have hu : y ≫ t = u ≫ ptMap s (dnFst k) := by
        refine Over.OverMorphism.ext ?_
        simp only [Over.comp_left, ptMap_left, ht]
        rfl
      rw [hu, evc, ← lift_whiskerLeft, Over.comp_left, pull_comp, h0, map_zero]
    rw [key, key, key, add_zero]

end GlobalTheory.DualOpen
