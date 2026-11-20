import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LiePull

/- English proof (translation)
Substitute `hg` using the available equality. Use `⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => ?_, fun y => ?_⟩, fun x => rfl⟩` and prove the remaining obligations. Establish `e' : x.left ≫ φ = y.left ≫ φ` using `congrArg (fun z => z.left) e`. Conclude with `Over.OverMorphism.ext (h.1.hom_ext e' ((Over.w x).trans (Over.w y).symm))`. Conclude with `⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩`.
-/
theorem exists_pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    ∃ e : (T ⟶ G') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hg
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => ?_, fun y => ?_⟩, fun x => rfl⟩
  · have e' : x.left ≫ φ = y.left ≫ φ := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (h.1.hom_ext e' ((Over.w x).trans (Over.w y).symm))
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

/- English proof (translation)
Take `⟨v, hv, H⟩` from `H`. Use `⟨fun i => e (v i), fun i => (hP _).1 (hv i), fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `e.surjective w`. Establish `pr : ∀ u : Fin n → A, e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod` using `fun u => by`. Rewrite using `[map_list_prod, List.map_ofFn]`.

Both sides reduce to the same expression. Use `(existsUnique_congr fun c => ⟨?_, ?_⟩).1 (H w ((hP _).2 hw))` and prove the remaining obligations. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩`. Introduce and unpack `⟨u, hu, hw⟩`.

Use `⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[pr, hw]`. Simplify using the standard rewrite rules.
-/
theorem basis_transport {A B k : Type} [Monoid A] [Monoid B] (e : A ≃* B) {P : A → Prop} {Q : B → Prop}
    {R : k → A → A → Prop} {R' : k → B → B → Prop} (hP : ∀ x, P x ↔ Q (e x))
    (hR : ∀ c x y, R c x y ↔ R' c (e x) (e y)) (n : ℕ)
    (H : ∃ v : Fin n → A, (∀ i, P (v i)) ∧ ∀ w, P w →
      ∃! c : Fin n → k, ∃ u : Fin n → A, (∀ i, R (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod) :
    ∃ v : Fin n → B, (∀ i, Q (v i)) ∧ ∀ w, Q w →
      ∃! c : Fin n → k, ∃ u : Fin n → B, (∀ i, R' (c i) (u i) (v i)) ∧ w = (List.ofFn u).prod := by
  obtain ⟨v, hv, H⟩ := H
  refine ⟨fun i => e (v i), fun i => (hP _).1 (hv i), fun w hw => ?_⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  have pr : ∀ u : Fin n → A, e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (H w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

/- English proof (translation)
Introduce `O _ S S' G G' _ _ f φ a a' h hact k _ x τ n`. Take `⟨e, he⟩` from `exists_pushEquiv h (epsPt x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f) (Category.assoc _ _ _).symm`. Take `⟨e₀, he₀⟩` from `exists_pushEquiv h (Over.mk x) (x ≫ f) rfl`. Establish `one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ`. Rewrite using `[← he₀, map_one]`.

Establish `sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) = spMap (algebraMap k (DualNumber k))` using `fun c => by`. Use `(Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)` and prove the remaining obligations. Apply the tactic sequence `ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `fs : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _`. Use `(Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))` and prove the remaining obligations.

Use extensionality with `a`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hR : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔ (e u).left = spMap (epsScale c) ≫ (e v).left` using `fun c u v => by`. Rewrite using `[he, he]`. Use `⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩` and prove the remaining obligations.

Use `(Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))` and prove the remaining obligations. Use `(congrArg (spMap (epsScale c) ≫ ·) (Over.w v)).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))`. Establish `hP : ∀ v : epsPt x ⟶ G', IsLieEigen a' x τ v ↔ IsLieEigen a (x ≫ f) τ (e v)` using `fun v => by`. Use `and_congr ?_ (forall_congr' fun c => ?_)` and prove the remaining obligations.

Rewrite using `[one, he]`. Use `⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm, fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩` and prove the remaining obligations. Use `((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm` and prove the remaining obligations. Use `(congrArg (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ ·) (Over.w v)).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))`.

Establish `E : e (v ≫ a'.act c) = e v ≫ a.act c` using `Over.OverMorphism.ext (by`. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])`. Rewrite using `[hR, E]`. Prove the components needed by the constructor for the conclusion. Conclude with `basis_transport e (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left) (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) hP hR n`.

Conclude with `basis_transport e.symm (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left) (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) (fun v => by rw [hP, e.apply_symm_apply]) (fun c u v => by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n`.
-/
theorem lieMult_pull : ∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n := by
  intro O _ S S' G G' _ _ f φ a a' h hact k _ x τ n
  obtain ⟨e, he⟩ := exists_pushEquiv h (epsPt x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔
      (e u).left = spMap (epsScale c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScale c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  have hP : ∀ v : epsPt x ⟶ G', IsLieEigen a' x τ v ↔ IsLieEigen a (x ≫ f) τ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  constructor
  · exact basis_transport e (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left) hP hR n
  · exact basis_transport e.symm (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
      (fun v => by rw [hP, e.apply_symm_apply])
      (fun c u v => by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n

end GlobalTheory.LiePull
