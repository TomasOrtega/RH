import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquaresStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace GaloisDescent

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

/- English proof (translation)
Unfold `act`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := by
  unfold act
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Unfold `act`. Conclude with `pullback.lift_snd _ _ _`.
-/
theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := by
  unfold act
  exact pullback.lift_snd _ _ _

/- English proof (translation)
Establish `hpb : IsPullback (pullback.snd T.hom π) (pullback.fst T.hom π) π T.hom` using `(IsPullback.of_hasPullback T.hom π).flip`. Conclude with `((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 (pullback T.hom π) T.left (pullback.fst T.hom π) (act hc T) (pullback.snd T.hom π) T.hom (fun a => act_snd hc T a) pullback.condition.symm).2 hpb (fun a => act_fst hc T a)`.
-/
theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) := by
  have hpb : IsPullback (pullback.snd T.hom π) (pullback.fst T.hom π) π T.hom :=
    (IsPullback.of_hasPullback T.hom π).flip
  exact ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 (pullback T.hom π) T.left (pullback.fst T.hom π) (act hc T)
    (pullback.snd T.hom π) T.hom (fun a => act_snd hc T a) pullback.condition.symm).2 hpb
    (fun a => act_fst hc T a)

/- English proof (translation)
Take `⟨f', -, huniq⟩` from `(GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ f) (fun a => by rw [← Category.assoc, hc.inv])`. Conclude with `(huniq f rfl).trans (huniq g h.symm).symm`.
-/
theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g := by
  obtain ⟨f', -, huniq⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ f)
    (fun a => by rw [← Category.assoc, hc.inv])
  exact (huniq f rfl).trans (huniq g h.symm).symm

/- English proof (translation)
Establish `h1` using `up_left H x`. Establish `h2` using `up_left H y`. Rewrite `h1` using `[e]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `cover_ext (isGaloisCover_act hc T) (h1.symm.trans h2)`.
-/
theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  have h1 := up_left H x
  have h2 := up_left H y
  rw [e] at h1
  apply Over.OverMorphism.ext
  exact cover_ext (isGaloisCover_act hc T) (h1.symm.trans h2)

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

/- English proof (translation)
Simplify using `only [equivariant, Subgroup.mem_iInf]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `preHom _ w = pushHom _ _ w ↔ _`. Rewrite using `[Over.OverMorphism.ext_iff]`. Unfold `preHom pushHom`.

Simplify using `only [MonoidHom.mk'_apply, Over.comp_left, Over.homMk_left]`. Unfold `pushPt`. Simplify using the standard rewrite rules.
-/
theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  refine forall_congr' fun a => ?_
  change preHom _ w = pushHom _ _ w ↔ _
  rw [Over.OverMorphism.ext_iff]
  unfold preHom pushHom
  simp only [MonoidHom.mk'_apply, Over.comp_left, Over.homMk_left]
  unfold pushPt
  simp

/- English proof (translation)
Establish `hinv : ∀ a, act hc T a ≫ (w.left ≫ φ) = w.left ≫ φ` using `fun a => by`. Rewrite using `[← Category.assoc, (mem_equivariant hc hν).1 hw a, Category.assoc, hφ]`. Take `⟨f', hf', -⟩` from `(GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ (isGaloisCover_act hc T)).1 G'.left (w.left ≫ φ) hinv`. Establish `hw' : w.left ≫ G.hom = pullback.snd T.hom π` using `by simpa using Over.w w`. Establish `hbase : f' ≫ G'.hom = T.hom`.

Apply `cover_ext (isGaloisCover_act hc T)` to reduce the goal to its premises. Rewrite using `[← Category.assoc, hf', Category.assoc, H.w, ← Category.assoc, hw', pullback.condition]`. Use `⟨Over.homMk f' hbase, GlobalTheory.QuotientDescent.hom_ext H ?_⟩` and prove the remaining obligations. Rewrite using `[up_left]`. Simplify using `[hf']`.
-/
theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hinv : ∀ a, act hc T a ≫ (w.left ≫ φ) = w.left ≫ φ := fun a => by
    rw [← Category.assoc, (mem_equivariant hc hν).1 hw a, Category.assoc, hφ]
  obtain ⟨f', hf', -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ (isGaloisCover_act hc T)).1 G'.left (w.left ≫ φ) hinv
  have hw' : w.left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w w
  have hbase : f' ≫ G'.hom = T.hom := by
    apply cover_ext (isGaloisCover_act hc T)
    rw [← Category.assoc, hf', Category.assoc, H.w, ← Category.assoc, hw', pullback.condition]
  refine ⟨Over.homMk f' hbase, GlobalTheory.QuotientDescent.hom_ext H ?_⟩
  rw [up_left]
  simp [hf']

/- English proof (translation)
Rewrite using `[mem_equivariant]`. Introduce `a`. Establish `hu : (up H z).left ≫ G.hom = pullback.snd T.hom π` using `by simpa using Over.w (up H z)`. Apply `H.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hφ, up_left, ← Category.assoc, act_fst]`.

Rewrite using `[Category.assoc, Category.assoc, (hν a).1.w, ← Category.assoc (up H z).left, hu]`. Conclude with `act_snd hc T a`.
-/
theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := by
  rw [mem_equivariant]
  intro a
  have hu : (up H z).left ≫ G.hom = pullback.snd T.hom π := by simpa using Over.w (up H z)
  apply H.hom_ext
  · rw [Category.assoc, Category.assoc, hφ, up_left, ← Category.assoc, act_fst]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, ← Category.assoc (up H z).left, hu]
    exact act_snd hc T a

/- English proof (translation)
Establish `hsurj : ∀ (T : Over Y) (w : equivariant hc hν T), ∃ z : T ⟶ G', up H z = w.1` using `fun T w => exists_up hc H hν hφ w.2`. Set `e : ∀ T : Over Y, (T ⟶ G') ≃ equivariant hc hν T` to `fun T => Equiv.ofBijective (fun z => ⟨up H z, up_mem hc H hν hφ z⟩) ⟨fun x y h => up_injective hc H (congrArg Subtype.val h), fun w => (hsurj T w).imp fun z hz => Subtype.ext hz⟩`. Establish `hmap : ∀ {T T' : Over Y} (u : T' ⟶ T) (w : equivariant hc hν T), (Over.pullback π).map u ≫ w.1 ∈ equivariant hc hν T'`. Introduce `T T' u w`. Take `⟨z, hz⟩` from `hsurj T w`.

Rewrite using `[← hz, ← up_comp]`. Conclude with `up_mem hc H hν hφ (u ≫ z)`. Set `F : (Over Y)ᵒᵖ ⥤ CommGrpCat` to `{ obj := fun T => CommGrpCat.of (equivariant hc hν T.unop) map := fun {T T'} u => CommGrpCat.ofHom { toFun := fun w => ⟨(Over.pullback π).map u.unop ≫ w.1, hmap u.unop w⟩ map_one' := Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_one) map_mul' := fun w w' => Subtype.ext …`. Use extensionality with `w`. Simplify using the standard rewrite rules.

Use `map_comp := fun u u' => by`. Use extensionality with `w`. Simplify using `}`. Set `α : (F ⋙ forget CommGrpCat).RepresentableBy G'` to `{ homEquiv := fun {T} => e T homEquiv_comp := fun {T T'} u z => Subtype.ext (up_comp H u z) }`. Set `inst : CommGrpObj G'` to `CommGrpObj.ofRepresentableBy G' F α`.

Use `⟨inferInstance, inferInstance, H, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `hmul : up H (x₀ * y₀) = up H x₀ * up H y₀` using `congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy G' (F ⋙ forget₂ CommGrpCat GrpCat) α).hom.app (Opposite.op (Over.mk (T.hom ≫ π)))).hom.map_mul x₀ y₀)`. Set `s₀ : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π))` to `Over.homMk (pullback.lift (𝟙 T.left) T.hom (by simp)) (pullback.lift_snd _ _ _)`. Establish `hs₀ : ∀ (z : Over.mk (T.hom ≫ π) ⟶ G') (t : T ⟶ G), z.left = t.left ≫ φ → s₀ ≫ up H z = t`.

Introduce `z t hz`. Apply `GlobalTheory.QuotientDescent.hom_ext H` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Category.assoc, up_left, hz]`. Conclude with `(pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)`. Establish `key : s₀ ≫ up H (x₀ * y₀) = x * y`.

Rewrite using `[hmul, ← hs₀ x₀ x hx, ← hs₀ y₀ y hy]`. Conclude with `(preHom s₀).map_mul (up H x₀) (up H y₀)`. Establish `hk` using `congrArg (fun t : T ⟶ G => t.left ≫ φ) key`. Rewrite using `[← hk, Over.comp_left, Category.assoc, up_left]`. Conclude with `((pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)).symm`.
-/
theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have hsurj : ∀ (T : Over Y) (w : equivariant hc hν T), ∃ z : T ⟶ G', up H z = w.1 :=
    fun T w => exists_up hc H hν hφ w.2
  let e : ∀ T : Over Y, (T ⟶ G') ≃ equivariant hc hν T := fun T =>
    Equiv.ofBijective (fun z => ⟨up H z, up_mem hc H hν hφ z⟩)
      ⟨fun x y h => up_injective hc H (congrArg Subtype.val h),
       fun w => (hsurj T w).imp fun z hz => Subtype.ext hz⟩
  have hmap : ∀ {T T' : Over Y} (u : T' ⟶ T) (w : equivariant hc hν T),
      (Over.pullback π).map u ≫ w.1 ∈ equivariant hc hν T' := by
    intro T T' u w
    obtain ⟨z, hz⟩ := hsurj T w
    rw [← hz, ← up_comp]
    exact up_mem hc H hν hφ (u ≫ z)
  let F : (Over Y)ᵒᵖ ⥤ CommGrpCat :=
    { obj := fun T => CommGrpCat.of (equivariant hc hν T.unop)
      map := fun {T T'} u => CommGrpCat.ofHom
        { toFun := fun w => ⟨(Over.pullback π).map u.unop ≫ w.1, hmap u.unop w⟩
          map_one' := Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_one)
          map_mul' := fun w w' => Subtype.ext ((preHom ((Over.pullback π).map u.unop)).map_mul w.1 w'.1) }
      map_id := fun T => by
        ext w
        simp
      map_comp := fun u u' => by
        ext w
        simp }
  let α : (F ⋙ forget CommGrpCat).RepresentableBy G' :=
    { homEquiv := fun {T} => e T
      homEquiv_comp := fun {T T'} u z => Subtype.ext (up_comp H u z) }
  let inst : CommGrpObj G' := CommGrpObj.ofRepresentableBy G' F α
  refine ⟨inferInstance, inferInstance, H, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hmul : up H (x₀ * y₀) = up H x₀ * up H y₀ :=
    congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy G' (F ⋙ forget₂ CommGrpCat GrpCat) α).hom.app
      (Opposite.op (Over.mk (T.hom ≫ π)))).hom.map_mul x₀ y₀)
  let s₀ : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)) :=
    Over.homMk (pullback.lift (𝟙 T.left) T.hom (by simp)) (pullback.lift_snd _ _ _)
  have hs₀ : ∀ (z : Over.mk (T.hom ≫ π) ⟶ G') (t : T ⟶ G), z.left = t.left ≫ φ → s₀ ≫ up H z = t := by
    intro z t hz
    apply GlobalTheory.QuotientDescent.hom_ext H
    rw [Over.comp_left, Category.assoc, up_left, hz]
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)
  have key : s₀ ≫ up H (x₀ * y₀) = x * y := by
    rw [hmul, ← hs₀ x₀ x hx, ← hs₀ y₀ y hy]
    exact (preHom s₀).map_mul (up H x₀) (up H y₀)
  have hk := congrArg (fun t : T ⟶ G => t.left ≫ φ) key
  rw [← hk, Over.comp_left, Category.assoc, up_left]
  exact ((pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)).symm

end GaloisDescent

open GaloisDescent

/- English proof (translation)
Introduce `K _ X Y π sY Ga _ ρ G _ ν hc hq hab hν hν1 hνmul`. Take `⟨hcomm, hsm, hpr, hgc⟩` from `hab`. Use `hc.finite` as an intermediate fact. Use `hc.fin` as an intermediate fact. Use `hc.etale` as an intermediate fact.

Use `hc.onto` as an intermediate fact. Establish `hdown : ∀ a, ν a ≫ G.hom = G.hom ≫ ρ a` using `fun a => (hν a).1.w`. Establish `hinvG : ∀ a, ν a ≫ G.hom ≫ π = G.hom ≫ π` using `fun a => by`. Rewrite using `[← Category.assoc, hdown, Category.assoc, hc.inv]`. Establish `hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ G.left) (a : Ga), y ≫ ν a = y → a = 1`.

Introduce `k _ _ y a hy`. Establish `hya : (y ≫ G.hom) ≫ ρ a = y ≫ G.hom`. Rewrite using `[Category.assoc, ← hdown, ← Category.assoc, hy]`. Establish `hy1 : (y ≫ G.hom) ≫ ρ 1 = y ≫ G.hom` using `by rw [hc.one, Category.comp_id]`. Conclude with `(hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique hya hy1`.

Take `⟨Y₀, π₀, sY₀, -, hc₀, -, -, -⟩` from `GlobalTheory.T.exists_separated_galoisCover_of_free_action K G.left (G.hom ≫ π ≫ sY) Ga ν hq hν1 hνmul (fun a => by rw [← Category.assoc G.hom π sY, ← Category.assoc, hinvG]) hfree`. Take `⟨v, hv, -⟩` from `(GlobalTheory.T.galoisCover_descent_and_cartesian_squares G.left Y₀ π₀ Ga ν hc₀).1 Y (G.hom ≫ π) hinvG`. Establish `hsq : IsPullback G.hom π₀ π v` using `((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 G.left Y₀ π₀ ν G.hom v hdown hv.symm).1 hc₀`. Establish `H : IsPullback π₀ G.hom (Over.mk v).hom π` using `hsq.flip`. Take `⟨inst, hcomm', hgp⟩` from `exists_grpObj (G' := Over.mk v) (φ := π₀) hc H hν (fun a => hc₀.inv a)`.

Establish `hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) π` using `⟨⟨inferInstance, inferInstance⟩, inferInstance⟩`. Establish `hsm' : Smooth v` using `MorphismProperty.of_isPullback_of_descendsAlong hsq hQ hsm`. Establish `huc : UniversallyClosed v` using `MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance`. Establish `hlft : LocallyOfFiniteType v` using `MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance`. Establish `: Surjective π₀` using `hc₀.onto`.

Establish `: IsFinite π₀` using `hc₀.fin`. Establish `: IsSeparated (π₀ ≫ v)` using `by rw [hv]; infer_instance`. Establish `hsep : IsSeparated v` using `GlobalTheory.SemiAbelianDescent.isSeparated_of_comp π₀ v`. Establish `hgc' : GeometricallyConnected v` using `GlobalTheory.SemiAbelianDescent.geometricallyConnected_of_isPullback H`. Conclude with `⟨Over.mk v, inst, π₀, ⟨hcomm', hsm', { toIsSeparated := hsep, toUniversallyClosed := huc, toLocallyOfFiniteType := hlft }, hgc'⟩, hgp, hc₀⟩`.
-/
theorem abelianScheme_descends_galoisCover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ X Y π sY Ga _ ρ G _ ν hc hq hab hν hν1 hνmul
  obtain ⟨hcomm, hsm, hpr, hgc⟩ := hab
  have := hc.finite
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have hdown : ∀ a, ν a ≫ G.hom = G.hom ≫ ρ a := fun a => (hν a).1.w
  have hinvG : ∀ a, ν a ≫ G.hom ≫ π = G.hom ≫ π := fun a => by
    rw [← Category.assoc, hdown, Category.assoc, hc.inv]
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ G.left) (a : Ga), y ≫ ν a = y → a = 1 := by
    intro k _ _ y a hy
    have hya : (y ≫ G.hom) ≫ ρ a = y ≫ G.hom := by
      rw [Category.assoc, ← hdown, ← Category.assoc, hy]
    have hy1 : (y ≫ G.hom) ≫ ρ 1 = y ≫ G.hom := by rw [hc.one, Category.comp_id]
    exact (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique hya hy1
  obtain ⟨Y₀, π₀, sY₀, -, hc₀, -, -, -⟩ := GlobalTheory.T.exists_separated_galoisCover_of_free_action K G.left (G.hom ≫ π ≫ sY) Ga ν hq hν1 hνmul
    (fun a => by rw [← Category.assoc G.hom π sY, ← Category.assoc, hinvG]) hfree
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares G.left Y₀ π₀ Ga ν hc₀).1 Y (G.hom ≫ π) hinvG
  have hsq : IsPullback G.hom π₀ π v :=
    ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 G.left Y₀ π₀ ν G.hom v hdown hv.symm).1 hc₀
  have H : IsPullback π₀ G.hom (Over.mk v).hom π := hsq.flip
  obtain ⟨inst, hcomm', hgp⟩ := exists_grpObj (G' := Over.mk v) (φ := π₀) hc H hν (fun a => hc₀.inv a)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) π :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hsm' : Smooth v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ hsm
  have huc : UniversallyClosed v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have hlft : LocallyOfFiniteType v := MorphismProperty.of_isPullback_of_descendsAlong hsq hQ inferInstance
  have : Surjective π₀ := hc₀.onto
  have : IsFinite π₀ := hc₀.fin
  have : IsSeparated (π₀ ≫ v) := by rw [hv]; infer_instance
  have hsep : IsSeparated v := GlobalTheory.SemiAbelianDescent.isSeparated_of_comp π₀ v
  have hgc' : GeometricallyConnected v := GlobalTheory.SemiAbelianDescent.geometricallyConnected_of_isPullback H
  exact ⟨Over.mk v, inst, π₀, ⟨hcomm', hsm', { toIsSeparated := hsep, toUniversallyClosed := huc, toLocallyOfFiniteType := hlft }, hgc'⟩, hgp, hc₀⟩

end GlobalTheory
