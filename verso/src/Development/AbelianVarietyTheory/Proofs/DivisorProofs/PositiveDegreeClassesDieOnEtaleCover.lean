import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)`. Rewrite using `[← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]`.
-/
theorem secMap_secRes_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  change (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(F.obj.map k.op).hom ((F.obj.map g.op).hom x) = (F.obj.map (k ≫ g).op).hom x`. Rewrite using `[op_comp, Functor.map_comp, ModuleCat.comp_apply]`.
-/
theorem secRes_secRes {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom x) = (F.obj.map (k ≫ g).op).hom x
  rw [op_comp, Functor.map_comp, ModuleCat.comp_apply]

/- English proof (translation)
Introduce `R _ X F n hn x`. Take `⟨α, rfl⟩` from `x.mk_surjective`. Establish `hsch` using `GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by omega) rfl`. Establish `hres` using `GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X`. Use `set z := ev α.1 0 n (by simp) X (𝟙 X) with hz`.

Establish `hdz : Sec.map ((res R F).d n (n + 1)) z = 0` using `(hsch.2 α).1`. Establish `hloc` using `hres.2.2.1 (n - 1) n (n + 1) hn (by omega) z rfl hdz`. Rewrite `hloc` using `[loc_iff_etale_affine_points]`. Use `swap`. Introduce and unpack `V W g k ⟨y, hy⟩`.

Use `⟨Sec.res k y, ?_⟩` and prove the remaining obligations. Rewrite using `[secMap_secRes_comm, hy, secRes_secRes]`. Use `choose V g _ hg hmem y hy using hloc`. Set `f : (∐ V) ⟶ X` to `Sigma.desc g`. Establish `hιf : ∀ i, Sigma.ι V i ≫ f = g i` using `fun i => Sigma.ι_desc g i`.

Use `⟨∐ V, f, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: IsZariskiLocalAtSource @Etale` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Conclude with `IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hg`. Use `⟨fun p => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `hmem p`.

Use `⟨Sigma.ι V p q, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hιf, hq]`. Take `⟨a, ha⟩` from `(sec_sigma_bijective R ((res R F).X (n - 1)) V).2 y`. Establish `hda : Sec.map ((res R F).d (n - 1) n) a = Sec.res f z`. Apply `(sec_sigma_bijective R ((res R F).X n) V).1` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Establish `hai : Sec.res (Sigma.ι V i) a = y i` using `congrFun ha i`. Express the relevant statement in the definitionally equal form `Sec.res (Sigma.ι V i) (Sec.map _ a) = Sec.res (Sigma.ι V i) (Sec.res f z)`. Rewrite using `[← secMap_secRes_comm, hai, hy, secRes_secRes, hιf]`. Establish `hY` using `GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (∐ V) (res R F) (n - 1) n (n + 1) (by omega) rfl`.

Establish `hev` using `GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := n)`. Set `α' : Cocycle ((chains R).obj (sch.obj (∐ V))) (res R F) n` to `zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk α' = 0`. Rewrite using `[(hY.2 α').2]`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[hda]`. Establish `h1` using `(hev.2.2.2.1 (sch.map f) α.1 0 n (by simp) (∐ V) (𝟙 (∐ V)))`. Establish `h2` using `(hev.2.1 α.1 0 n (by simp) (∐ V) X f (𝟙 X))`. Express the relevant statement in the definitionally equal form `_ = ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ (∐ V) (𝟙 (∐ V))`. Rewrite using `[h1, hz, h2]`.

Both sides reduce to the same expression.
-/
theorem classes_die_on_etale_cover : A5 := by
  intro R _ X F n hn x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hsch := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (n - 1) n (n + 1) (by omega) rfl
  have hres := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X
  set z := ev α.1 0 n (by simp) X (𝟙 X) with hz
  have hdz : Sec.map ((res R F).d n (n + 1)) z = 0 := (hsch.2 α).1
  have hloc := hres.2.2.1 (n - 1) n (n + 1) hn (by omega) z rfl hdz
  rw [loc_iff_etale_affine_points] at hloc
  swap
  · rintro V W g k ⟨y, hy⟩
    refine ⟨Sec.res k y, ?_⟩
    rw [secMap_secRes_comm, hy, secRes_secRes]
  choose V g _ hg hmem y hy using hloc
  let f : (∐ V) ⟶ X := Sigma.desc g
  have hιf : ∀ i, Sigma.ι V i ≫ f = g i := fun i => Sigma.ι_desc g i
  refine ⟨∐ V, f, ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hg
  · refine ⟨fun p => ?_⟩
    obtain ⟨q, hq⟩ := hmem p
    refine ⟨Sigma.ι V p q, ?_⟩
    rw [← Scheme.Hom.comp_apply, hιf, hq]
  · obtain ⟨a, ha⟩ := (sec_sigma_bijective R ((res R F).X (n - 1)) V).2 y
    have hda : Sec.map ((res R F).d (n - 1) n) a = Sec.res f z := by
      apply (sec_sigma_bijective R ((res R F).X n) V).1
      funext i
      have hai : Sec.res (Sigma.ι V i) a = y i := congrFun ha i
      change Sec.res (Sigma.ι V i) (Sec.map _ a) = Sec.res (Sigma.ι V i) (Sec.res f z)
      rw [← secMap_secRes_comm, hai, hy, secRes_secRes, hιf]
    have hY := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (∐ V) (res R F) (n - 1) n (n + 1) (by omega) rfl
    have hev := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := n)
    let α' : Cocycle ((chains R).obj (sch.obj (∐ V))) (res R F) n :=
      zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n)
    change CohomologyClass.mk α' = 0
    rw [(hY.2 α').2]
    refine ⟨a, ?_⟩
    rw [hda]
    have h1 := (hev.2.2.2.1 (sch.map f) α.1 0 n (by simp) (∐ V) (𝟙 (∐ V)))
    have h2 := (hev.2.1 α.1 0 n (by simp) (∐ V) X f (𝟙 X))
    change _ = ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ (∐ V) (𝟙 (∐ V))
    rw [h1, hz, h2]
    rfl

end GlobalTheory.EtC
