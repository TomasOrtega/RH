import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/- English proof (translation)
Substitute `hz` using the available equality. Use `letI := φ.toAlgebra`. Take `⟨j, h1, h2, h3⟩` from `GlobalTheory.T.lie_model_base_change_map S G A R x E F M N`. Conclude with `⟨j, h1, h2, fun hs n b => (h3 hs n b).2⟩`.
-/
theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        Submodule.span R (Set.range fun k => j (b k)) = ⊤) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.T.lie_model_base_change_map S G A R x E F M N
  exact ⟨j, h1, h2, fun hs n b => (h3 hs n b).2⟩

end GlobalTheory.CompanionTheory.Ar.LieVal

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/- English proof (translation)
Introduce `hξ hs`. Take `⟨EA, _, _, ⟨MA⟩⟩` from `lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))`. Take `⟨j, hj, hjs, hjb⟩` from `LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z (LieTangent.spec_centre z) MA MR`. Take `⟨i, hi, his, -⟩` from `LieVal.exists_base (genMap ξ ⟨centre z, h⟩) _ ξ (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M`. Establish `hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a)` using `fun a => ⟨MA.tan a, hi a⟩`.

Establish `hmem : ∀ a, i a ∈ M.lat ⟨centre z, h⟩` using `fun a => (M.mem_lat_iff _ _).2 ⟨_, hext a⟩`. Establish `hinj : ∀ a b, i a = i b → a = b` using `fun a b hab => MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))`. Establish `hsurj : ∀ e v, M.Extends ⟨centre z, h⟩ e v → ∃ a, i a = e ∧ MA.pt a = v`. Introduce `e v hv`. Take `⟨a, rfl⟩` from `MA.onto v hv.1`.

Conclude with `⟨a, M.inj (Over.OverMorphism.ext ((hi a).trans hv.2.symm)), rfl⟩`. Set `i' : EA →+ M.lat ⟨centre z, h⟩` to `{ toFun := fun a => ⟨i a, hmem a⟩ map_zero' := Subtype.ext (map_zero i) map_add' := fun a b => Subtype.ext (map_add i a b) }`. Establish `hbij : Function.Bijective i'`. Use `⟨fun a b hab => hinj a b (congrArg Subtype.val hab), fun e => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `(M.mem_lat_iff _ _).1 e.2`.

Take `⟨a, ha, -⟩` from `hsurj _ _ hv`. Conclude with `⟨a, Subtype.ext ha⟩`. Set `q` to `AddEquiv.ofBijective i' hbij`. Establish `hq : ∀ a, q.symm ⟨i a, hmem a⟩ = a` using `fun a => q.symm_apply_apply a`. Use `⟨j.comp q.symm.toAddMonoidHom, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `e w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h', v, hv, hw⟩`. Take `⟨a, rfl, rfl⟩` from `hsurj _ _ hv`. Use `⟨hmem a, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `j (q.symm ⟨i a, hmem a⟩) = w`. Rewrite using `[hq]`. Conclude with `MR.inj (Over.OverMorphism.ext ((hj a).trans hw.symm))`. Introduce and unpack `⟨he, rfl⟩`. Take `⟨v, hv⟩` from `(M.mem_lat_iff _ _).1 he`.

Take `⟨a, rfl, rfl⟩` from `hsurj _ _ hv`. Express the relevant statement in the definitionally equal form `M.ValAt z (i a) (MR.pt (j (q.symm ⟨i a, hmem a⟩)))`. Rewrite using `[hq]`. Conclude with `⟨h, _, hext a, hj a⟩`. Introduce and unpack `a r e ⟨_, s, hsa, rfl⟩`.

Take `⟨b, rfl⟩` from `q.surjective e`. Establish `: a • q b = q (s • b)` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(a : Ω) • i b = i (s • b)`. Rewrite using `[his, hsa])`. Express the relevant statement in the definitionally equal form `j (q.symm (a • q b)) = _ • j (q.symm (q b))`.

Rewrite using `[this, q.symm_apply_apply, q.symm_apply_apply]`. Conclude with `hjs s b`. Take `⟨n, ⟨b⟩⟩` from `GlobalTheory.T.lie_model_free_over_local_ring X G hs (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA`. Use `top_le_iff.1 ((hjb hs n b).symm.le.trans (Submodule.span_mono ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Use `⟨q (b k), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `j (q.symm (q (b k))) = _`. Rewrite using `[q.symm_apply_apply]`.
-/
theorem lieLat_val (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type)
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type)
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    IsCptGen ξ → Smooth G.hom → ∃ ev : M.lat ⟨centre z, h⟩ →+ ER,
      (∀ (e : E) (w : ER), M.ValAt z e (MR.pt w) ↔ ∃ he : e ∈ M.lat ⟨centre z, h⟩, ev ⟨e, he⟩ = w) ∧
      (∀ (a : regAt ξ ⟨centre z, h⟩) (r : R) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) ∧
      Submodule.span R (Set.range ev) = ⊤ := by
  intro hξ hs
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, hjs, hjb⟩ := LieVal.exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := LieVal.exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M

  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  have hmem : ∀ a, i a ∈ M.lat ⟨centre z, h⟩ := fun a => (M.mem_lat_iff _ _).2 ⟨_, hext a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e v, M.Extends ⟨centre z, h⟩ e v → ∃ a, i a = e ∧ MA.pt a = v := by
    intro e v hv
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj (Over.OverMorphism.ext ((hi a).trans hv.2.symm)), rfl⟩
  let i' : EA →+ M.lat ⟨centre z, h⟩ :=
    { toFun := fun a => ⟨i a, hmem a⟩
      map_zero' := Subtype.ext (map_zero i)
      map_add' := fun a b => Subtype.ext (map_add i a b) }
  have hbij : Function.Bijective i' := by
    refine ⟨fun a b hab => hinj a b (congrArg Subtype.val hab), fun e => ?_⟩
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 e.2
    obtain ⟨a, ha, -⟩ := hsurj _ _ hv
    exact ⟨a, Subtype.ext ha⟩
  let q := AddEquiv.ofBijective i' hbij
  have hq : ∀ a, q.symm ⟨i a, hmem a⟩ = a := fun a => q.symm_apply_apply a
  refine ⟨j.comp q.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro e w
    constructor
    · rintro ⟨h', v, hv, hw⟩
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      refine ⟨hmem a, ?_⟩
      change j (q.symm ⟨i a, hmem a⟩) = w
      rw [hq]
      exact MR.inj (Over.OverMorphism.ext ((hj a).trans hw.symm))
    · rintro ⟨he, rfl⟩
      obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
      obtain ⟨a, rfl, rfl⟩ := hsurj _ _ hv
      change M.ValAt z (i a) (MR.pt (j (q.symm ⟨i a, hmem a⟩)))
      rw [hq]
      exact ⟨h, _, hext a, hj a⟩
  · rintro a r e ⟨_, s, hsa, rfl⟩
    obtain ⟨b, rfl⟩ := q.surjective e
    have : a • q b = q (s • b) := Subtype.ext (by
      change (a : Ω) • i b = i (s • b)
      rw [his, hsa])
    change j (q.symm (a • q b)) = _ • j (q.symm (q b))
    rw [this, q.symm_apply_apply, q.symm_apply_apply]
    exact hjs s b
  · obtain ⟨n, ⟨b⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring X G hs (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
    refine top_le_iff.1 ((hjb hs n b).symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨k, rfl⟩
    refine ⟨q (b k), ?_⟩
    change j (q.symm (q (b k))) = _
    rw [q.symm_apply_apply]

end GlobalTheory.CompanionTheory.Ar
