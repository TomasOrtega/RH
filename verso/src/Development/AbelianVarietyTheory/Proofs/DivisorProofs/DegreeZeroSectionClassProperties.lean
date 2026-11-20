import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SectionClass

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

/- English proof (translation)
Establish `hz : Sec.map ((res R F).d 0 1) (Sec.map (resι R F) s) = 0` using `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).2 ⟨s, rfl⟩`. Take `⟨α, h0, -⟩` from `(GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 _ hz`. Use `⟨α, (h0 X (𝟙 X)).trans ?_⟩` and prove the remaining obligations. Simplify using `[Sec.res]`.
-/
theorem exists_cocycle (s : Sec F X) :
    ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0, ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  have hz : Sec.map ((res R F).d 0 1) (Sec.map (resι R F) s) = 0 :=
    ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).2 ⟨s, rfl⟩
  obtain ⟨α, h0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 _ hz
  refine ⟨α, (h0 X (𝟙 X)).trans ?_⟩
  simp [Sec.res]

/- English proof (translation)
Establish `h2` using `((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 (α - β)).2`. Establish `hsub : ev (α - β).1 0 0 (by simp) X (𝟙 X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X)`. Use `((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).2.1` as an intermediate fact. Simplify using `using this`. Establish `hss : Subsingleton (Sec ((res R F).X (-1)) X)` using `(GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.2.2 (-1) (by norm_num)`.

Rewrite using `[← sub_eq_zero, ← CohomologyClass.mk_sub, h2, hsub]`. Establish `hz : Sec.map ((res R F).d (-1) 0) (0 : Sec ((res R F).X (-1)) X) = 0` using `map_zero _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Establish `hy' : (0 : Sec ((res R F).X 0) X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X)`.

Rewrite using `[← hz, ← Subsingleton.elim y 0]`. Conclude with `hy`. Conclude with `(sub_eq_zero.1 hy'.symm)`. Introduce `h`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hz, h, sub_self]`.
-/
theorem mk_eq_iff (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    CohomologyClass.mk α = CohomologyClass.mk β ↔
      ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) := by
  have h2 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 (α - β)).2
  have hsub : ev (α - β).1 0 0 (by simp) X (𝟙 X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).2.1
    simpa using this
  have hss : Subsingleton (Sec ((res R F).X (-1)) X) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.2.2 (-1) (by norm_num)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, h2, hsub]
  have hz : Sec.map ((res R F).d (-1) 0) (0 : Sec ((res R F).X (-1)) X) = 0 := map_zero _
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (0 : Sec ((res R F).X 0) X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
      rw [← hz, ← Subsingleton.elim y 0]; exact hy
    exact (sub_eq_zero.1 hy'.symm)
  · intro h
    refine ⟨0, ?_⟩
    rw [hz, h, sub_self]

/- English proof (translation)
Take `⟨α, h⟩` from `exists_cocycle R F X s`. Conclude with `pick_spec (P := fun c => ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0, CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s) ⟨_, α, rfl, h⟩`.
-/
theorem secClass_spec (s : Sec F X) : ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = secClass F s ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  obtain ⟨α, h⟩ := exists_cocycle R F X s
  exact pick_spec (P := fun c => ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s) ⟨_, α, rfl, h⟩

/- English proof (translation)
Take `⟨α₀, h1, h2⟩` from `secClass_spec R F X s`. Rewrite using `[← h1, mk_eq_iff, h2]`.
-/
theorem spec_iff (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s := by
  obtain ⟨α₀, h1, h2⟩ := secClass_spec R F X s
  rw [← h1, mk_eq_iff, h2]

end GlobalTheory.EtC.SectionClass

open GlobalTheory.EtC.SectionClass in

/- English proof (translation)
Introduce `R _ F X`. Use `⟨spec_iff R F X, ⟨?_, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s t hst`. Take `⟨α, h1, h2⟩` from `secClass_spec R F X s`. Establish `h3` using `(spec_iff R F X t α).2 (h1.trans hst)`.

Conclude with `(GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.1 (h2.symm.trans h3)`. Introduce `c`. Take `⟨α, rfl⟩` from `c.mk_surjective`. Establish `hd` using `((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1`. Take `⟨a, ha⟩` from `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).1 hd`.

Conclude with `⟨a, ((spec_iff R F X a α).1 ha.symm).symm⟩`. Introduce `s t`. Take `⟨α, h1, h2⟩` from `secClass_spec R F X s`. Take `⟨β, h3, h4⟩` from `secClass_spec R F X t`. Rewrite using `[← h1, ← h3, ← CohomologyClass.mk_add]`.

Use `symm`. Use `(spec_iff R F X (s + t) (α + β)).1 ?_` and prove the remaining obligations. Use `((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).1` as an intermediate fact. Simplify using `only [Cocycle.coe_add] at this ⊢`. Rewrite using `[this, h2, h4]`.

Conclude with `(map_add ((resι R F).hom.app (op X)).hom s t).symm`. Introduce `Y f s`. Take `⟨α, h1, h2⟩` from `secClass_spec R F X s`. Rewrite using `[← h1]`. Use `(spec_iff R F Y _ _).1 ?_` and prove the remaining obligations.

Establish `e4` using `(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.1 (sch.map f) α.1 0 0 (by simp) Y (𝟙 Y)`. Establish `e2` using `(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.1 α.1 0 0 (by simp) Y X f (𝟙 X)`. Establish `hx1 : Sx.map (p` using `0) (sch.map f) (𝟙 Y : Sx (sch.obj Y) 0 Y) = (show Sx (sch.obj X) 0 Y from f) := by`. Simplify using `[Sx.map, sch]`. Conclude with `Category.id_comp f`.

Establish `hx2 : Sx.res f (𝟙 X : Sx (sch.obj X) 0 X) = (show Sx (sch.obj X) 0 Y from f)`. Simplify using `[Sx.res, sch]`. Conclude with `Category.comp_id f`. Express the relevant statement in the definitionally equal form `ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add 0)) 0 0 _ Y (𝟙 Y) = _`. Rewrite using `[e4, hx1, ← hx2, ← e2, h2]`.

Conclude with `(NatTrans.naturality_apply (resι R F).hom f.op s).symm`. Introduce `G φ s`. Take `⟨α, h1, h2⟩` from `secClass_spec R F X s`. Rewrite using `[← h1]`. Use `(spec_iff R G X _ _).1 ?_` and prove the remaining obligations.

Establish `e5` using `(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.2 (resMap R φ) α.1 0 0 (by simp) X (𝟙 X)`. Establish `hc` using `((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.2 G φ).2`. Express the relevant statement in the definitionally equal form `ev (α.1.comp (Cochain.ofHom (resMap R φ)) (add_zero 0)) 0 0 _ X (𝟙 X) = _`. Rewrite using `[e5, h2]`. Express the relevant statement in the definitionally equal form `((resι R F ≫ (resMap R φ).f 0).hom.app (op X)).hom s = _`.

Rewrite using `[hc]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.EtC.secClass_props : ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), (∀ (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0), ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s) ∧ Function.Bijective (secClass F (X := X)) ∧ (∀ s t : Sec F X, secClass F (s + t) = secClass F s + secClass F t) ∧ (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (secClass F s) = secClass F (Sec.res f s)) ∧ ∀ {G : Shv R} (φ : F ⟶ G) (s : Sec F X), HK.post R _ φ 0 (secClass F s) = secClass G (Sec.map φ s) := by
  intro R _ F X
  refine ⟨spec_iff R F X, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s t hst
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    have h3 := (spec_iff R F X t α).2 (h1.trans hst)
    exact (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.1 (h2.symm.trans h3)
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    have hd := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
    obtain ⟨a, ha⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).1 hd
    exact ⟨a, ((spec_iff R F X a α).1 ha.symm).symm⟩
  · intro s t
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    obtain ⟨β, h3, h4⟩ := secClass_spec R F X t
    rw [← h1, ← h3, ← CohomologyClass.mk_add]
    symm
    refine (spec_iff R F X (s + t) (α + β)).1 ?_
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).1
    simp only [Cocycle.coe_add] at this ⊢
    rw [this, h2, h4]
    exact (map_add ((resι R F).hom.app (op X)).hom s t).symm
  · intro Y f s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R F Y _ _).1 ?_
    have e4 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.1 (sch.map f) α.1 0 0 (by simp) Y (𝟙 Y)
    have e2 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.1 α.1 0 0 (by simp) Y X f (𝟙 X)
    have hx1 : Sx.map (p := 0) (sch.map f) (𝟙 Y : Sx (sch.obj Y) 0 Y) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.map, sch]
      exact Category.id_comp f
    have hx2 : Sx.res f (𝟙 X : Sx (sch.obj X) 0 X) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.res, sch]
      exact Category.comp_id f
    change ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add 0)) 0 0 _ Y (𝟙 Y) = _
    rw [e4, hx1, ← hx2, ← e2, h2]
    exact (NatTrans.naturality_apply (resι R F).hom f.op s).symm
  · intro G φ s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R G X _ _).1 ?_
    have e5 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.2 (resMap R φ) α.1 0 0 (by simp) X (𝟙 X)
    have hc := ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.2 G φ).2
    change ev (α.1.comp (Cochain.ofHom (resMap R φ)) (add_zero 0)) 0 0 _ X (𝟙 X) = _
    rw [e5, h2]
    change ((resι R F ≫ (resMap R φ).f 0).hom.app (op X)).hom s = _
    rw [hc]
    rfl
