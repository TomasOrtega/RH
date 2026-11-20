import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

/- English proof (translation)
Substitute `hz` using the available equality. Use `letI := φ.toAlgebra`. Take `⟨j, h1, h2, h3⟩` from `PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N`. Use `⟨j, fun e => Over.OverMorphism.ext (h1 e), h2, fun hs n b => ?_⟩` and prove the remaining obligations. Conclude with `⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩`.
-/
theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, N.pt (j e) = LieTangent.epsBase φ hz ≫ M.pt e) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        ∃ b' : Module.Basis (Fin n) R F, ∀ k, b' k = j (b k)) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N
  refine ⟨j, fun e => Over.OverMorphism.ext (h1 e), h2, fun hs n b => ?_⟩
  exact ⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

/- English proof (translation)
Substitute `hz` using the available equality. Rewrite `h`, the goal using `[LieModel.valAt_iff]`. Take `⟨hc, v, hv, rfl⟩` from `h`. Establish `hsp` using `LieTangent.centre_specializes φ x`. Establish `hc'` using `LieTangent.specializes_of_injective (hξ.inj ⟨_, hc⟩) hsp`.

Establish `F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre x) = X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ x))` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp`. Establish `hd : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D), (dualMap g).comp (dualMap f) = dualMap (g.comp f)`. Introduce `A B D _ _ _ f g`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp`.

Rewrite `hv` using `[LieModel.extends_iff]`. Use `⟨hc', LieTangent.epsBase (X.presheaf.stalkSpecializes hsp).hom F1 ≫ v, (M.extends_iff _ _ _).2 ⟨LieTangent.isTanAt_base _ _ hv.1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hv.2, ← Category.assoc]`. Use `congr 1`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[LieTangent.spec_comp, hd]`. Use `congr 3`. Conclude with `RingHom.ext fun s => (LieTangent.genMap_specializes ⟨_, hc⟩ hc' hsp s).symm`. Rewrite using `[← Category.assoc, ← Category.assoc]`.

Use `congr 1`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[LieTangent.spec_comp, hd, LieTangent.spec_comp, hd]`. Use `congr 3`.

Conclude with `(congrArg CommRingCat.Hom.hom (LieTangent.stalk_base φ x)).symm`.
-/
theorem lieValAt_base (hξ : IsCptGen ξ) {M : LieModel G ξ V} {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (φ : R →+* R') {x : Spec (CommRingCat.of R) ⟶ X}
    {z : Spec (CommRingCat.of R') ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {e : V} {w : epsAt x ⟶ G}
    (h : M.ValAt x e w) : M.ValAt z e (LieTangent.epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at h ⊢
  obtain ⟨hc, v, hv, rfl⟩ := h
  have hsp := LieTangent.centre_specializes φ x
  have hc' := LieTangent.specializes_of_injective (hξ.inj ⟨_, hc⟩) hsp
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre x) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ x)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hd : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
    intro A B D _ _ _ f g
    refine RingHom.ext fun a => ?_
    ext <;> simp
  rw [LieModel.extends_iff] at hv
  refine ⟨hc', LieTangent.epsBase (X.presheaf.stalkSpecializes hsp).hom F1 ≫ v,
    (M.extends_iff _ _ _).2 ⟨LieTangent.isTanAt_base _ _ hv.1, ?_⟩, ?_⟩
  · rw [hv.2, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd]
    congr 3
    exact RingHom.ext fun s => (LieTangent.genMap_specializes ⟨_, hc⟩ hc' hsp s).symm
  · rw [← Category.assoc, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd, LieTangent.spec_comp, hd]
    congr 3
    exact (congrArg CommRingCat.Hom.hom (LieTangent.stalk_base φ x)).symm

/- English proof (translation)
Take `⟨EA, _, _, ⟨MA⟩⟩` from `lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))`. Take `⟨j, hj, -, hjb⟩` from `exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z (LieTangent.spec_centre z) MA MR`. Take `⟨i, hi, his, -⟩` from `exists_base (genMap ξ ⟨centre z, h⟩) _ ξ (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M`. Establish `hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a)` using `fun a => (M.extends_iff _ _ _).2 ⟨MA.tan a, hi a⟩`. Establish `hinj : ∀ a b, i a = i b → a = b` using `fun a b hab => MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))`.

Establish `hsurj : ∀ e ∈ M.lat ⟨centre z, h⟩, ∃ a, i a = e`. Introduce `e he`. Take `⟨v, hv⟩` from `(M.mem_lat_iff _ _).1 he`. Take `⟨a, rfl⟩` from `MA.onto v hv.1`. Conclude with `⟨a, M.inj ((hi a).trans ((M.extends_iff _ _ _).1 hv).2.symm)⟩`.

Use `choose a ha using fun q => hsurj (b q) (by rw [hb.2]; exact Submodule.subset_span ⟨q, rfl⟩)`. Establish `hsum : ∀ c : Fin n → X.presheaf.stalk (centre z), i (∑ q, c q • a q) = ∑ q, genMap ξ ⟨centre z, h⟩ (c q) • b q`. Introduce `c`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [his, ha]`.

Establish `li : LinearIndependent (X.presheaf.stalk (centre z)) a`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc q`. Establish `h1` using `hsum c`. Rewrite `h1` using `[hc, map_zero]`.

Conclude with `hξ.inj ⟨_, h⟩ ((Fintype.linearIndependent_iff.1 hb.1 _ h1.symm q).trans (map_zero _).symm)`. Establish `sp : ⊤ ≤ Submodule.span (X.presheaf.stalk (centre z)) (Set.range a)`. Introduce `e _`. Establish `h1 : i e ∈ M.lat ⟨centre z, h⟩` using `(M.mem_lat_iff _ _).2 ⟨_, hext e⟩`. Rewrite `h1` using `[hb.2, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨c, hc⟩` from `h1`. Use `choose s hs using fun q => (c q).2`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨s, hinj _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[hsum, ← hc]`.

Conclude with `Finset.sum_congr rfl fun q _ => by rw [hs]; rfl`. Take `⟨bz, hbz⟩` from `hjb hs n (Module.Basis.mk li sp)`. Use `⟨bz, fun q => (M.valAt_iff _ _ _).2 ⟨h, MA.pt (a q), ha q ▸ hext (a q), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hbz, hj, Module.Basis.mk_apply]`.
-/
theorem frame_basis [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) {n : ℕ} {b : Fin n → V}
    (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    ∃ bz : Module.Basis (Fin n) R ER, ∀ q, M.ValAt z (b q) (MR.pt (bz q)) := by
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a =>
    (M.extends_iff _ _ _).2 ⟨MA.tan a, hi a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e ∈ M.lat ⟨centre z, h⟩, ∃ a, i a = e := by
    intro e he
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj ((hi a).trans ((M.extends_iff _ _ _).1 hv).2.symm)⟩
  choose a ha using fun q => hsurj (b q) (by rw [hb.2]; exact Submodule.subset_span ⟨q, rfl⟩)
  have hsum : ∀ c : Fin n → X.presheaf.stalk (centre z),
      i (∑ q, c q • a q) = ∑ q, genMap ξ ⟨centre z, h⟩ (c q) • b q := by
    intro c
    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [his, ha]
  have li : LinearIndependent (X.presheaf.stalk (centre z)) a := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := hsum c
    rw [hc, map_zero] at h1
    exact hξ.inj ⟨_, h⟩ ((Fintype.linearIndependent_iff.1 hb.1 _ h1.symm q).trans (map_zero _).symm)
  have sp : ⊤ ≤ Submodule.span (X.presheaf.stalk (centre z)) (Set.range a) := by
    intro e _
    have h1 : i e ∈ M.lat ⟨centre z, h⟩ := (M.mem_lat_iff _ _).2 ⟨_, hext e⟩
    rw [hb.2, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    choose s hs using fun q => (c q).2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨s, hinj _ _ ?_⟩
    rw [hsum, ← hc]
    exact Finset.sum_congr rfl fun q _ => by rw [hs]; rfl
  obtain ⟨bz, hbz⟩ := hjb hs n (Module.Basis.mk li sp)
  refine ⟨bz, fun q => (M.valAt_iff _ _ _).2 ⟨h, MA.pt (a q), ha q ▸ hext (a q), ?_⟩⟩
  rw [hbz, hj, Module.Basis.mk_apply]

/- English proof (translation)
Take `⟨ER, _, _, ⟨MR⟩⟩` from `lieModel_exists X G _ (Y.x i)`. Take `⟨bR, hbR⟩` from `frame_basis hξ hs M (Y.x i) h MR hb`. Take `⟨j, hj, hjs, hjb⟩` from `exists_base (C.v i).valuationSubring.subtype _ z (Y.gen i) MR Mz`. Take `⟨bz, hbz⟩` from `hjb hs n bR`. Use `⟨bz, fun q => ?_, fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[hbz, hj]`. Conclude with `lieValAt_base hξ _ _ (hbR q)`. Establish `hr : Y.lieLat Mz i = j.range`. Use `le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_` and prove the remaining obligations. Introduce and unpack `e ⟨v, hv, he⟩`.

Take `⟨u, rfl⟩` from `MR.onto v hv`. Conclude with `⟨u, Mz.inj ((hj u).trans (Over.OverMorphism.ext he.symm))⟩`. Introduce and unpack `_ ⟨u, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨MR.pt u, MR.tan u, congrArg (fun q => q.left) (hj u)⟩`. Establish `hsum : ∀ c : Fin n → (C.v i).valuationSubring, j (∑ q, c q • bR q) = ∑ q, (c q : K) • bz q`.

Introduce `c`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [hjs, hbz]; rfl`. Rewrite using `[hr]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, rfl⟩ q`. Rewrite using `[← bR.sum_repr u, hsum, bz.repr_sum_self]`. Conclude with `(bR.repr u q).2`. Introduce `hx`. Conclude with `⟨∑ q, (⟨bz.repr x q, hx q⟩ : (C.v i).valuationSubring) • bR q, by rw [hsum]; exact bz.sum_repr x⟩`.
-/
theorem frame_lat [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {K : Type} [Field K]
    {C : ACurve K} {z : Spec (CommRingCat.of K) ⟶ X} (Y : CurveIn C z) {Vz : Type} [AddCommGroup Vz] [Module K Vz]
    (Mz : LieModel G z Vz) {n : ℕ} {b : Fin n → V} (i : C.I) (h : genPt ξ ⤳ centre (Y.x i))
    (hb : M.lat.IsFrameAt b ⟨centre (Y.x i), h⟩) :
    ∃ bz : Module.Basis (Fin n) K Vz, (∀ q, M.ValAt z (b q) (Mz.pt (bz q))) ∧ IsLatOf C i bz (Y.lieLat Mz i) := by
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G _ (Y.x i)
  obtain ⟨bR, hbR⟩ := frame_basis hξ hs M (Y.x i) h MR hb
  obtain ⟨j, hj, hjs, hjb⟩ := exists_base (C.v i).valuationSubring.subtype _ z (Y.gen i) MR Mz
  obtain ⟨bz, hbz⟩ := hjb hs n bR
  refine ⟨bz, fun q => ?_, fun x => ?_⟩
  · rw [hbz, hj]
    exact lieValAt_base hξ _ _ (hbR q)
  · have hr : Y.lieLat Mz i = j.range := by
      refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
      · rintro e ⟨v, hv, he⟩
        obtain ⟨u, rfl⟩ := MR.onto v hv
        exact ⟨u, Mz.inj ((hj u).trans (Over.OverMorphism.ext he.symm))⟩
      · rintro _ ⟨u, rfl⟩
        exact AddSubgroup.subset_closure ⟨MR.pt u, MR.tan u, congrArg (fun q => q.left) (hj u)⟩
    have hsum : ∀ c : Fin n → (C.v i).valuationSubring, j (∑ q, c q • bR q) = ∑ q, (c q : K) • bz q := by
      intro c
      rw [map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [hjs, hbz]; rfl
    rw [hr]
    constructor
    · rintro ⟨u, rfl⟩ q
      rw [← bR.sum_repr u, hsum, bz.repr_sum_self]
      exact (bR.repr u q).2
    · intro hx
      exact ⟨∑ q, (⟨bz.repr x q, hx q⟩ : (C.v i).valuationSubring) • bR q, by rw [hsum]; exact bz.sum_repr x⟩

end PositivityTheory.HtPt.Ci
