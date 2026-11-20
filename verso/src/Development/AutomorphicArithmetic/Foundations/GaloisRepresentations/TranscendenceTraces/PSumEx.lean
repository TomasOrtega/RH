import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RingSec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh66.ring_sec Ω C φ h`.
-/
private theorem ring_sec (Ω C : Type) [Field Ω] [IsAlgClosed Ω] [CommRing C] [Nontrivial C] (φ : Ω →+* C)
    (h : φ.FiniteType) : ∃ ρ : C →+* Ω, ρ.comp φ = RingHom.id Ω :=
  _root_.UpperTheory.Reformulated.B.Qh66.ring_sec Ω C φ h

/- English proof (translation)
Establish `hl : LocallyOfFiniteType g` using `inferInstance`. Establish `hft : g.appTop.hom.FiniteType` using `(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hl`. Set `e` to `Scheme.ΓSpecIso (CommRingCat.of Ω)`. Use `haveI : Nontrivial Γ(V, ⊤) := by haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩`. Conclude with `Scheme.component_nontrivial V ⊤`.

Establish `hft' : (e.inv ≫ g.appTop).hom.FiniteType`. Rewrite using `[CommRingCat.hom_comp]`. Conclude with `RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)`. Take `⟨ρ, hρ⟩` from `ring_sec Ω Γ(V, ⊤) (e.inv ≫ g.appTop).hom hft'`. Use `⟨Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv, ?_⟩` and prove the remaining obligations.

Establish `he : (gp Ω).isoSpec.hom ≫ Spec.map e.inv = 𝟙 _`. Rewrite using `[Scheme.isoSpec_Spec_hom, ← Spec.map_comp]`. Simplify using `[e]`. Establish `h1 : g = V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop)`. Rewrite using `[Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, he, Category.comp_id]`.

Establish `h2 : (e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ = 𝟙 _` using `CommRingCat.hom_ext hρ`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem etale_sec (Ω : Type) [Field Ω] [IsAlgClosed Ω] {V : Scheme.{0}} [IsAffine V] (g : V ⟶ gp Ω) [Etale g]
    [Nonempty V] : ∃ σ : gp Ω ⟶ V, σ ≫ g = 𝟙 _ := by
  have hl : LocallyOfFiniteType g := inferInstance
  have hft : g.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hl
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  haveI : Nontrivial Γ(V, ⊤) := by
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
    exact Scheme.component_nontrivial V ⊤
  have hft' : (e.inv ≫ g.appTop).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
  obtain ⟨ρ, hρ⟩ := ring_sec Ω Γ(V, ⊤) (e.inv ≫ g.appTop).hom hft'
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv, ?_⟩
  have he : (gp Ω).isoSpec.hom ≫ Spec.map e.inv = 𝟙 _ := by
    rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
    simp [e]
  have h1 : g = V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, he, Category.comp_id]
  have h2 : (e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ = 𝟙 _ := CommRingCat.hom_ext hρ
  calc (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ g
      = (Spec.map (CommRingCat.ofHom ρ) ≫ V.isoSpec.inv) ≫ V.isoSpec.hom ≫ Spec.map (e.inv ≫ g.appTop) := by rw [← h1]
    _ = Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (e.inv ≫ g.appTop) := by simp
    _ = Spec.map ((e.inv ≫ g.appTop) ≫ CommRingCat.ofHom ρ) := (Spec.map_comp _ _).symm
    _ = 𝟙 _ := by rw [h2, Spec.map_id]

/- English proof (translation)
Take `⟨V, g, hV, hg, ⟨v, -⟩, hPg⟩` from `(GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (gp Ω) P hP).1 h (IsLocalRing.closedPoint Ω)`. Use `haveI : Nonempty V := ⟨v⟩`. Take `⟨σ, hσ⟩` from `etale_sec Ω g`. Simplify `hP _ _ g σ hPg` using `[hσ]`.
-/
private theorem loc_gp (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : ∀ V : Scheme.{0}, (V ⟶ gp Ω) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ gp Ω) (k : W ⟶ V), P V g → P W (k ≫ g)) (h : Loc (gp Ω) P) : P (gp Ω) (𝟙 _) := by
  obtain ⟨V, g, hV, hg, ⟨v, -⟩, hPg⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (gp Ω) P hP).1 h (IsLocalRing.closedPoint Ω)
  haveI : Nonempty V := ⟨v⟩
  obtain ⟨σ, hσ⟩ := etale_sec Ω g
  simpa [hσ] using hP _ _ g σ hPg

@[reducible] private noncomputable def bcSq {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) {V : Scheme.{0}} (g : V ⟶ A.U) : Sq p :=
  ⟨V, pullback A.r g, g ≫ A.u, pullback.fst A.r g ≫ A.v, pullback.snd A.r g,
    (IsPullback.of_hasPullback A.r g).paste_horiz A.pb⟩

/- English proof (translation)
Introduce `hLoc hNat hInj q _ i Z S p _ w hw hq A a`. Establish `hqU : IsUnit (q : Γ(A.U, ⊤))`. Simplify using `using hq.map A.u.appTop.hom`. Take `⟨T, hT, hTp⟩` from `(GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q A.U).1 hqU`. Establish `hex : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g → ∃ b : Sec (tw q i) V, IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) b` using `fun V g hg => hLoc q i p w hw (bcSq A g) (hTp V g hg) _`.

Establish `huniq : ∀ (B : Sq p) (a' : Sec (tw q i) B.V) (b b' : Sec (tw q i) B.U), IsSum w B a' b → IsSum w B a' b' → b = b'` using `fun B a' b b' h h' => hInj q i B.U b b' fun Ω _ _ x => (h Ω x).trans (h' Ω x).symm`. Set `s : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g → Sec (tw q i) V` to `fun V g hg => (hex V g hg).choose`. Establish `hs : ∀ (V : Scheme.{0}) (g : V ⟶ A.U) (hg : T.arrows g), IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) (s V g hg)` using `fun V g hg => (hex V g hg).choose_spec`. Establish `hcomp : ∀ (V W : Scheme.{0}) (g : V ⟶ A.U) (k : W ⟶ V) (hg : T.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k)`. Introduce `V W g k hg`.

Take `⟨L, hLf, hLs⟩ : ∃ L : pullback A.r (k ≫ g) ⟶ pullback A.r g, L ≫ pullback.fst A.r g = pullback.fst A.r (k ≫ g) ∧ L ≫ pullback.snd A.r g = pullback.snd A.r (k ≫ g) ≫ k` from `⟨pullback.lift (pullback.fst A.r (k ≫ g)) (pullback.snd A.r (k ≫ g) ≫ k) (by rw [pullback.condition, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Set `t : (bcSq A (k ≫ g)).To (bcSq A g)` to `{ g := k k := L hu := by simp hv := by`. Express the relevant statement in the definitionally equal form `L ≫ pullback.fst A.r g ≫ A.v = pullback.fst A.r (k ≫ g) ≫ A.v`. Rewrite using `[← Category.assoc, hLf]`. Use `hr := hLs }`.

Establish `h1` using `hNat (ZMod q) (tw q i) w t _ _ (hs V g hg)`. Establish `h2 : Sec.res t.k (Sec.res (pullback.fst A.r g) a) = Sec.res (pullback.fst A.r (k ≫ g)) a`. Rewrite using `[res_res]`. Express the relevant statement in the definitionally equal form `Sec.res (L ≫ pullback.fst A.r g) a = _`. Rewrite using `[hLf]`.

Rewrite `h1` using `[h2]`. Conclude with `huniq _ _ _ _ h1 (hs W (k ≫ g) (T.downward_closed hg k))`. Take `⟨b, hb⟩` from `(GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) A.U).2 T hT s hcomp`. Use `⟨b, fun Ω _ _ x => ?_⟩` and prove the remaining obligations. Establish `hx : T.arrows x`.

Establish `hl : Loc (gp Ω) fun V g => T.arrows (g ≫ x)` using `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 A.U (gp Ω) x (fun V g => T.arrows g) ⟨T, hT, fun _ _ h => h⟩`. Establish `h0` using `loc_gp Ω (fun V g => T.arrows (g ≫ x)) (fun V W g k h => by simpa using T.downward_closed h k) hl`. Simplify using `using h0`. Establish `h1` using `(res_id _).symm.trans (hs _ x hx Ω (𝟙 _))`. Rewrite using `[hb _ x hx, h1]`.

Establish `hbij` using `fib_bijOn (IsPullback.of_hasPullback A.r x) (𝟙 (gp Ω))`. Rewrite `hbij` using `[Category.id_comp]`. Use `finsum_mem_eq_of_bijOn _ hbij fun z hz => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `w Ω (z ≫ pullback.fst A.r x ≫ A.v) • Sec.res z (Sec.res (pullback.fst A.r x) a) = w Ω ((z ≫ pullback.fst A.r x) ≫ A.v) • Sec.res (z ≫ pullback.fst A.r x) a`. Rewrite using `[res_res, Category.assoc]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.sumEx_of :
    SumExLoc → SumNat → PtInj → SumEx := by
  intro hLoc hNat hInj q _ i Z S p _ w hw hq A a
  have hqU : IsUnit (q : Γ(A.U, ⊤)) := by
    simpa using hq.map A.u.appTop.hom
  obtain ⟨T, hT, hTp⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q A.U).1 hqU
  have hex : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g →
      ∃ b : Sec (tw q i) V, IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) b :=
    fun V g hg => hLoc q i p w hw (bcSq A g) (hTp V g hg) _
  have huniq : ∀ (B : Sq p) (a' : Sec (tw q i) B.V) (b b' : Sec (tw q i) B.U), IsSum w B a' b → IsSum w B a' b' → b = b' :=
    fun B a' b b' h h' => hInj q i B.U b b' fun Ω _ _ x => (h Ω x).trans (h' Ω x).symm
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ A.U), T.arrows g → Sec (tw q i) V := fun V g hg => (hex V g hg).choose
  have hs : ∀ (V : Scheme.{0}) (g : V ⟶ A.U) (hg : T.arrows g),
      IsSum w (bcSq A g) (Sec.res (pullback.fst A.r g) a) (s V g hg) := fun V g hg => (hex V g hg).choose_spec
  have hcomp : ∀ (V W : Scheme.{0}) (g : V ⟶ A.U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    obtain ⟨L, hLf, hLs⟩ : ∃ L : pullback A.r (k ≫ g) ⟶ pullback A.r g,
        L ≫ pullback.fst A.r g = pullback.fst A.r (k ≫ g) ∧ L ≫ pullback.snd A.r g = pullback.snd A.r (k ≫ g) ≫ k :=
      ⟨pullback.lift (pullback.fst A.r (k ≫ g)) (pullback.snd A.r (k ≫ g) ≫ k)
        (by rw [pullback.condition, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let t : (bcSq A (k ≫ g)).To (bcSq A g) :=
      { g := k
        k := L
        hu := by simp
        hv := by
          change L ≫ pullback.fst A.r g ≫ A.v = pullback.fst A.r (k ≫ g) ≫ A.v
          rw [← Category.assoc, hLf]
        hr := hLs }
    have h1 := hNat (ZMod q) (tw q i) w t _ _ (hs V g hg)
    have h2 : Sec.res t.k (Sec.res (pullback.fst A.r g) a) = Sec.res (pullback.fst A.r (k ≫ g)) a := by
      rw [res_res]
      change Sec.res (L ≫ pullback.fst A.r g) a = _
      rw [hLf]
    rw [h2] at h1
    exact huniq _ _ _ _ h1 (hs W (k ≫ g) (T.downward_closed hg k))
  obtain ⟨b, hb⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) (tw q i) A.U).2 T hT s hcomp
  refine ⟨b, fun Ω _ _ x => ?_⟩
  have hx : T.arrows x := by
    have hl : Loc (gp Ω) fun V g => T.arrows (g ≫ x) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 A.U (gp Ω) x (fun V g => T.arrows g) ⟨T, hT, fun _ _ h => h⟩
    have h0 := loc_gp Ω (fun V g => T.arrows (g ≫ x))
      (fun V W g k h => by simpa using T.downward_closed h k) hl
    simpa using h0
  have h1 := (res_id _).symm.trans (hs _ x hx Ω (𝟙 _))
  rw [hb _ x hx, h1]
  have hbij := fib_bijOn (IsPullback.of_hasPullback A.r x) (𝟙 (gp Ω))
  rw [Category.id_comp] at hbij
  refine finsum_mem_eq_of_bijOn _ hbij fun z hz => ?_
  change w Ω (z ≫ pullback.fst A.r x ≫ A.v) • Sec.res z (Sec.res (pullback.fst A.r x) a) =
    w Ω ((z ≫ pullback.fst A.r x) ≫ A.v) • Sec.res (z ≫ pullback.fst A.r x) a
  rw [res_res, Category.assoc]
