import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

/- English proof (translation)
Substitute `hb` using the available equality. Set `ρ : (Over.mk a ⟶ G') →* (Over.mk (a ≫ f) ⟶ G)` to `MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 (Over.mk a) x y _ _ rfl rfl).symm`. Establish `hρ : ∀ x, (ρ x).left = x.left ≫ φ` using `fun _ => rfl`. Use `⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun y => ?_⟩, hρ⟩` and prove the remaining obligations. Use `Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))` and prove the remaining obligations.

Conclude with `(hρ x).symm.trans ((congrArg (fun z => z.left) hxy).trans (hρ y))`. Conclude with `⟨Over.homMk (h.1.lift y.left a (Over.w y)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext ((hρ _).trans (h.1.lift_fst _ _ _))⟩`.
-/
theorem exists_mulEquiv_of_isGrpPullback (h : IsGrpPullback G' G f φ) {X : Scheme.{0}} (a : X ⟶ S') (b : X ⟶ S)
    (hb : b = a ≫ f) :
    ∃ e : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hb
  let ρ : (Over.mk a ⟶ G') →* (Over.mk (a ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 (Over.mk a) x y _ _ rfl rfl).symm
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun y => ?_⟩, hρ⟩
  · refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    exact (hρ x).symm.trans ((congrArg (fun z => z.left) hxy).trans (hρ y))
  · exact ⟨Over.homMk (h.1.lift y.left a (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hρ _).trans (h.1.lift_fst _ _ _))⟩

variable {k : Type} [Field k]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Apply the tactic sequence `ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem spMap_epsScale_comp_algebraMap (c : k) :
    spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) = spMap (algebraMap k (DualNumber k)) := by
  rw [← Spec.map_comp]
  congr 1
  ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.
-/
theorem spMap_fstHom_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 (Sp k) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

/- English proof (translation)
Take `⟨e, he⟩` from `exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap k (DualNumber k)) ≫ x) (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f) (Category.assoc _ _ _).symm`. Take `⟨e₀, he₀⟩` from `exists_mulEquiv_of_isGrpPullback h x (x ≫ f) rfl`. Establish `one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ`. Rewrite using `[← he₀, map_one]`. Establish `scale : ∀ (c : k) (u v : epsPt x ⟶ G'), u.left = spMap (epsScale c) ≫ v.left ↔ (e u).left = spMap (epsScale c) ≫ (e v).left`.

Introduce `c u v`. Rewrite using `[he, he, ← Category.assoc]`. Use `⟨fun huv => congrArg (· ≫ φ) huv, fun huv => h.1.hom_ext huv ?_⟩` and prove the remaining obligations. Use `(Over.w u).trans (Eq.symm ?_)` and prove the remaining obligations. Use `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)` and prove the remaining obligations.

Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (spMap_epsScale_comp_algebraMap c))`. Establish `eact : ∀ (a : O) (v : epsPt x ⟶ G'), e (v ≫ act'.act a) = e v ≫ act.act a`. Introduce `a v`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc]`.

Establish `eig : ∀ v : epsPt x ⟶ G', IsLieEigen act' x τ v ↔ IsLieEigen act (x ≫ f) τ (e v)`. Introduce `v`. Use `and_congr ?_ (forall_congr' fun a => by rw [scale, eact])` and prove the remaining obligations. Rewrite using `[he, one, ← Category.assoc]`. Use `⟨fun hv => by rw [hv], fun hv => h.1.hom_ext hv ?_⟩` and prove the remaining obligations.

Use `Eq.trans ?_ (Over.w (1 : Over.mk x ⟶ G')).symm` and prove the remaining obligations. Use `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) spMap_fstHom_comp_algebraMap).trans (Category.id_comp _))`. Establish `prod : ∀ u : Fin n → (epsPt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod`. Introduce `u`.

Rewrite using `[map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Establish `key : ∀ (v : Fin n → (epsPt x ⟶ G')) (w : epsPt x ⟶ G') (c : Fin n → k), (∃ u : Fin n → (epsPt x ⟶ G'), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔ ∃ u : Fin n → (epsPt (x ≫ f) ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (e (v i)).lef …`. Introduce `v w c`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨fun i => e (u i), fun i => (scale _ _ _).1 (hu i), prod u⟩`. Introduce and unpack `⟨u, hu, hw⟩`. Use `⟨fun i => e.symm (u i), fun i => (scale _ _ _).2 ?_, e.injective ?_⟩` and prove the remaining obligations. Rewrite using `[e.apply_symm_apply]`.

Conclude with `hu i`. Rewrite using `[prod, hw]`. Simplify using `only [e.apply_symm_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hw⟩`.

Use `⟨fun i => e (v i), fun i => (eig _).1 (hv i), fun w hw' => ?_⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `e.surjective w`. Conclude with `(existsUnique_congr (key v w)).1 (hw w ((eig w).2 hw'))`. Introduce and unpack `⟨v, hv, hw⟩`. Take `⟨v, rfl⟩ : ∃ v' : Fin n → (epsPt x ⟶ G'), v = fun i => e (v' i)` from `⟨fun i => e.symm (v i), funext fun i => (e.apply_symm_apply _).symm⟩`.

Conclude with `⟨v, fun i => (eig _).2 (hv i), fun w hw' => (existsUnique_congr (key v w)).2 (hw _ ((eig w).1 hw'))⟩`.
-/
theorem lieMult_iff_of_isGrpPullback (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (act' : OAct O G')
    (act : OAct O G) (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (x : Sp k ⟶ S') (τ : O →+* k)
    (n : ℕ) : LieMult act' x τ n ↔ LieMult act (x ≫ f) τ n := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap k (DualNumber k)) ≫ x)
    (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f) (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_of_isGrpPullback h x (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have scale : ∀ (c : k) (u v : epsPt x ⟶ G'),
      u.left = spMap (epsScale c) ≫ v.left ↔ (e u).left = spMap (epsScale c) ≫ (e v).left := by
    intro c u v
    rw [he, he, ← Category.assoc]
    refine ⟨fun huv => congrArg (· ≫ φ) huv, fun huv => h.1.hom_ext huv ?_⟩
    refine (Over.w u).trans (Eq.symm ?_)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (spMap_epsScale_comp_algebraMap c))
  have eact : ∀ (a : O) (v : epsPt x ⟶ G'), e (v ≫ act'.act a) = e v ≫ act.act a := by
    intro a v
    refine Over.OverMorphism.ext ?_
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc]
  have eig : ∀ v : epsPt x ⟶ G', IsLieEigen act' x τ v ↔ IsLieEigen act (x ≫ f) τ (e v) := by
    intro v
    refine and_congr ?_ (forall_congr' fun a => by rw [scale, eact])
    rw [he, one, ← Category.assoc]
    refine ⟨fun hv => by rw [hv], fun hv => h.1.hom_ext hv ?_⟩
    refine Eq.trans ?_ (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ x) spMap_fstHom_comp_algebraMap).trans (Category.id_comp _))
  have prod : ∀ u : Fin n → (epsPt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := by
    intro u
    rw [map_list_prod, List.map_ofFn]
    rfl
  have key : ∀ (v : Fin n → (epsPt x ⟶ G')) (w : epsPt x ⟶ G') (c : Fin n → k),
      (∃ u : Fin n → (epsPt x ⟶ G'),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔
      ∃ u : Fin n → (epsPt (x ≫ f) ⟶ G),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (e (v i)).left) ∧ e w = (List.ofFn u).prod := by
    intro v w c
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (scale _ _ _).1 (hu i), prod u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (scale _ _ _).2 ?_, e.injective ?_⟩
      · rw [e.apply_symm_apply]; exact hu i
      · rw [prod, hw]
        simp only [e.apply_symm_apply]
  constructor
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun i => e (v i), fun i => (eig _).1 (hv i), fun w hw' => ?_⟩
    obtain ⟨w, rfl⟩ := e.surjective w
    exact (existsUnique_congr (key v w)).1 (hw w ((eig w).2 hw'))
  · rintro ⟨v, hv, hw⟩
    obtain ⟨v, rfl⟩ : ∃ v' : Fin n → (epsPt x ⟶ G'), v = fun i => e (v' i) :=
      ⟨fun i => e.symm (v i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, fun i => (eig _).2 (hv i), fun w hw' => (existsUnique_congr (key v w)).2 (hw _ ((eig w).1 hw'))⟩

end

/- English proof (translation)
Introduce and unpack `E _ _ _ H D S S' t t' f ⟨m⟩ k _ x ρ`. Use `forall_congr' fun τ => ?_` and prove the remaining obligations. Rewrite using `[lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.p, lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.q]`.
-/
theorem detCond_iff_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), Nonempty (SABMap t' t f) →
    ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (ρ : k), DetCond D t'.act x ρ ↔ DetCond D t.act (x ≫ f) ρ := by
  rintro E _ _ _ H D S S' t t' f ⟨m⟩ k _ x ρ
  refine forall_congr' fun τ => ?_
  rw [lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.p,
    lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.q]

end GlobalTheory
