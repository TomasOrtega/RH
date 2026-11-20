import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HTPullTan

open GlobalTheory.UPel.HT

/- English proof (translation)
Introduce `O _ S S' A A' _ _ f φ a a' h hact R' _ x b c v v₀ hv₀`. Take `⟨e₀, he₀⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl`. Establish `one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ`. Rewrite using `[← he₀, map_one]`. Establish `sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R'))`.

Use `(Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)` and prove the remaining obligations. Apply the tactic sequence `ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _`. Use `(Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))` and prove the remaining obligations. Use extensionality with `a`.

Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hR : ∀ (u w : epsPtR x ⟶ A') (u₀ w₀ : epsPtR (x ≫ f) ⟶ A), u₀.left = u.left ≫ φ → w₀.left = w.left ≫ φ → (u.left = spMap (epsScaleR c) ≫ w.left ↔ u₀.left = spMap (epsScaleR c) ≫ w₀.left)` using `fun u w u₀ w₀ hu hw => by`. Rewrite using `[hu, hw]`. Use `⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩` and prove the remaining obligations. Use `(Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))` and prove the remaining obligations.

Use `(congrArg (spMap (epsScaleR c) ≫ ·) (Over.w w)).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)`. Use `and_congr ?_ ?_` and prove the remaining obligations. Rewrite using `[one, hv₀]`. Use `⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm, fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩` and prove the remaining obligations.

Use `((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm` and prove the remaining obligations. Use `(congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))`. Use `hR _ _ _ _ ?_ hv₀` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, hv₀, Category.assoc, Category.assoc, hact]`.
-/
theorem isTanScal_iff_of_left_eq : ∀ {O : Type} [Ring O] {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] (f : S' ⟶ S) (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A'), IsGrpPullback A' A f φ → (∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) → ∀ {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A), v₀.left = v.left ≫ φ → (GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀) := by
  intro O _ S S' A A' _ _ f φ a a' h hact R' _ x b c v v₀ hv₀
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A') (u₀ w₀ : epsPtR (x ≫ f) ⟶ A), u₀.left = u.left ≫ φ → w₀.left = w.left ≫ φ →
      (u.left = spMap (epsScaleR c) ≫ w.left ↔
      u₀.left = spMap (epsScaleR c) ≫ w₀.left) := fun u w u₀ w₀ hu hw => by
    rw [hu, hw]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, hv₀]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · refine hR _ _ _ _ ?_ hv₀
    rw [Over.comp_left, Over.comp_left, hv₀, Category.assoc, Category.assoc, hact]

end GlobalTheory.HTPullTan
