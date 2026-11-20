import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.WeilBound.CoreStatements.HodgeTatePoints.MgLevel

noncomputable section

namespace PositivityTheory.HtPt.Mg

section Pairing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

/- English proof (translation)
Establish `h : f.inv.appTop ≫ f.hom.appTop = 𝟙 _`. Rewrite using `[← Scheme.Hom.comp_appTop]`. Simplify using the standard rewrite rules. Introduce `x`. Use `⟨f.inv.appTop.hom x, ?_⟩` and prove the remaining obligations.

Establish `hx` using `congrArg (fun g => g.hom x) h`. Simplify using `using hx`.
-/
private theorem surjective_appTop_of_iso' {X Y : Scheme.{0}} (f : X ≅ Y) : Function.Surjective f.hom.appTop.hom := by
  have h : f.inv.appTop ≫ f.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  intro x
  refine ⟨f.inv.appTop.hom x, ?_⟩
  have hx := congrArg (fun g => g.hom x) h
  simpa using hx

/- English proof (translation)
Use `haveI := hA.comm`. Use `haveI := hA.smooth`. Use `haveI := hA.geomConnected`. Use `haveI hAb : IsAbelianScheme ((Over.pullback T.hom).obj A) := ⟨inferInstance, (inferInstance : Smooth (pullback.snd A.hom T.hom)), hT, (inferInstance : GeometricallyConnected (pullback.snd A.hom T.hom))⟩`. Establish `hb` using `(GlobalTheory.ExpansionTotal.globalFns T.left ((Over.pullback T.hom).obj A) hAb).2`.

Apply the tactic sequence `have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom := by`. Simplify using the standard rewrite rules. Rewrite using `[e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]`. Conclude with `Function.Surjective.comp (surjective_appTop_of_iso' _) hb`.
-/
theorem surj_fst_of_proper (hA : IsSemiAbelian A) (T : Over S) (hT : IsProper (pullback.snd A.hom T.hom)) :
    Function.Surjective (fst T A).left.appTop.hom := by
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI hAb : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    ⟨inferInstance, (inferInstance : Smooth (pullback.snd A.hom T.hom)), hT,
      (inferInstance : GeometricallyConnected (pullback.snd A.hom T.hom))⟩
  have hb := (GlobalTheory.ExpansionTotal.globalFns T.left ((Over.pullback T.hom).obj A) hAb).2
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom := by
    simp
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Surjective.comp (surjective_appTop_of_iso' _) hb

omit [GrpObj A] in
/- English proof (translation)
Establish `e : h.left ≫ T.hom = T'.hom` using `Over.w h`. Establish `q : pullback.snd A.hom (h.left ≫ T.hom) = (pullbackLeftPullbackSndIso A.hom T.hom h.left).inv ≫ pullback.snd (pullback.snd A.hom T.hom) h.left`. Rewrite using `[Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]`. Establish `hp : IsProper (pullback.snd A.hom (h.left ≫ T.hom))`. Rewrite using `[q]`.

Use `infer_instance`. Rewrite `hp` using `[e]`. Then use the resulting hypothesis.
-/
theorem proper_of_hom {T T' : Over S} (h : T' ⟶ T) (hT : IsProper (pullback.snd A.hom T.hom)) :
    IsProper (pullback.snd A.hom T'.hom) := by
  have e : h.left ≫ T.hom = T'.hom := Over.w h
  have q : pullback.snd A.hom (h.left ≫ T.hom) =
      (pullbackLeftPullbackSndIso A.hom T.hom h.left).inv ≫ pullback.snd (pullback.snd A.hom T.hom) h.left := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  have hp : IsProper (pullback.snd A.hom (h.left ≫ T.hom)) := by
    rw [q]
    infer_instance
  rwa [e] at hp

/- English proof (translation)
Take `⟨a, u, hu⟩` from `θ`. Take `⟨a', u', hu'⟩` from `θ'`. Take `rfl : a = a'` from `h`. Conclude with `val_div_eq hL (fst T A).left hT hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ`.
-/
theorem tval_div' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (x : T ⟶ A) (z : Z) (J)
    (hJ : Good L z J) :
    tval θ r z J * (tval θ' r z J)⁻¹ =
      tval θ (r ≫ (translT A x).left) z J * (tval θ' (r ≫ (translT A x).left) z J)⁻¹ := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  exact val_div_eq hL (fst T A).left hT hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ

/- English proof (translation)
Establish `hb : b' = a' * a⁻¹ * b` using `by rw [h1]; group`. Establish `hd : d' = c' * c⁻¹ * d` using `by rw [h2]; group`. Establish `hd0 : d = a⁻¹ * (c * b * u)` using `by rw [← h0]; group`. Rewrite using `[hb, hd, hd0]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
private theorem mul_eq_mul_mul_of_ratio_eq {G : Type*} [CommGroup G] {a a' b b' c c' d d' u : G}
    (h1 : a' * a⁻¹ = b' * b⁻¹) (h2 : c' * c⁻¹ = d' * d⁻¹) (h0 : a * d = c * b * u) :
    a' * d' = c' * b' * u := by
  have hb : b' = a' * a⁻¹ * b := by rw [h1]; group
  have hd : d' = c' * c⁻¹ * d := by rw [h2]; group
  have hd0 : d = a⁻¹ * (c * b * u) := by rw [← h0]; group
  rw [hb, hd, hd0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Rewrite `H`, the goal using `[commIsOf_iff hL]`. Introduce `Z r z J hJ`. Establish `h1` using `tval_div' hL hT θx' θx hx r θy.pt z J hJ`. Establish `h2` using `tval_div' hL hT θy' θy hy r θx.pt z J hJ`. Establish `h0` using `H Z r z J hJ`.

Rewrite using `[hx, hy]`. Conclude with `mul_eq_mul_mul_of_ratio_eq h1 h2 h0`.
-/
theorem commIsOf_change' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have h1 := tval_div' hL hT θx' θx hx r θy.pt z J hJ
  have h2 := tval_div' hL hT θy' θy hy r θx.pt z J hJ
  have h0 := H Z r z J hJ
  rw [hx, hy]
  exact mul_eq_mul_mul_of_ratio_eq h1 h2 h0

/- English proof (translation)
Introduce `p`. Take `⟨V, hpV, ⟨θx0, θy0, hx0, hy0⟩, hall⟩` from `H (h.left p)`. Set `V' : T'.left.Opens` to `h.left ⁻¹ᵁ V`. Set `g : overRes V' ⟶ overRes V` to `Over.homMk (h.left ∣_ V) (by`. Simplify using `only [overRes, Over.mk_hom]`.

Rewrite using `[← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w h])`. Establish `key : g ≫ overResι V = overResι V' ≫ h`. Use `ext`. Simplify using `[g, overResι, morphismRestrict_ι, V']`. Establish `hsurj : Function.Surjective (fst (overRes V') A).left.appTop.hom` using `surj_fst_of_proper hA _ (proper_of_hom (overResι V') hT)`.

Establish `hc : unitRes V' (Units.map h.left.appTop.hom.toMonoidHom c) = Units.map g.left.appTop.hom.toMonoidHom (unitRes V c)`. Establish `hl` using `congrArg Over.Hom.left key`. Simplify using `only [Over.comp_left, overResι, Over.homMk_left] at hl`. Use `ext`. Simplify using `only [unitRes, Units.coe_map, MonoidHom.coe_coe]`.

Establish `hv` using `congrArg (fun f => f.appTop.hom (c : Γ(T.left, ⊤))) hl`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hv`. Conclude with `hv.symm`. Take `⟨θx', θy', hx', hy', hcc⟩` from `exists_commIsOf_pull hL g (hall θx0 θy0 hx0 hy0)`. Use `⟨V', hpV, ⟨θx', θy', ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx', hx0, ← Category.assoc, key, Category.assoc]`. Rewrite using `[hy', hy0, ← Category.assoc, key, Category.assoc]`. Introduce `θx θy hx hy`. Rewrite using `[hc]`. Use `commIsOf_change' hL hsurj ?_ ?_ hcc` and prove the remaining obligations.

Rewrite using `[hx, hx', hx0, ← Category.assoc, ← key, Category.assoc]`. Rewrite using `[hy, hy', hy0, ← Category.assoc, ← key, Category.assoc]`.
-/
theorem weilIs_pull_of_proper (hA : IsSemiAbelian A) (hL : L.IsLB) {T T' : Over S}
    (hT : IsProper (pullback.snd A.hom T'.hom)) (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hpV, ⟨θx0, θy0, hx0, hy0⟩, hall⟩ := H (h.left p)
  let V' : T'.left.Opens := h.left ⁻¹ᵁ V
  let g : overRes V' ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    simp only [overRes, Over.mk_hom]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w h])
  have key : g ≫ overResι V = overResι V' ≫ h := by
    ext
    simp [g, overResι, morphismRestrict_ι, V']
  have hsurj : Function.Surjective (fst (overRes V') A).left.appTop.hom :=
    surj_fst_of_proper hA _ (proper_of_hom (overResι V') hT)
  have hc : unitRes V' (Units.map h.left.appTop.hom.toMonoidHom c) =
      Units.map g.left.appTop.hom.toMonoidHom (unitRes V c) := by
    have hl := congrArg Over.Hom.left key
    simp only [Over.comp_left, overResι, Over.homMk_left] at hl
    ext
    simp only [unitRes, Units.coe_map, MonoidHom.coe_coe]
    have hv := congrArg (fun f => f.appTop.hom (c : Γ(T.left, ⊤))) hl
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hv
    exact hv.symm
  obtain ⟨θx', θy', hx', hy', hcc⟩ := exists_commIsOf_pull hL g (hall θx0 θy0 hx0 hy0)
  refine ⟨V', hpV, ⟨θx', θy', ?_, ?_⟩, ?_⟩
  · rw [hx', hx0, ← Category.assoc, key, Category.assoc]
  · rw [hy', hy0, ← Category.assoc, key, Category.assoc]
  · intro θx θy hx hy
    rw [hc]
    refine commIsOf_change' hL hsurj ?_ ?_ hcc
    · rw [hx, hx', hx0, ← Category.assoc, ← key, Category.assoc]
    · rw [hy, hy', hy0, ← Category.assoc, ← key, Category.assoc]

end Pairing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

/- English proof (translation)
Use `haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace f`. Use `haveI : Finite (closedPoints Z) := Finite.of_equiv _ (pointEquivClosedPoint f)`. Establish `hz : IsClosed ({w (IsLocalRing.closedPoint K)} : Set Z)` using `by set z := w (IsLocalRing.closedPoint K)`. Establish `h1` using `JacobsonSpace.closure_inter_closedPoints_eq_closure (isClosed_closure (s := ({z} : Set Z))).isLocallyClosed`. Establish `hfin : (closure ({z} : Set Z) ∩ closedPoints Z).Finite` using `(Set.toFinite (closedPoints Z)).subset Set.inter_subset_right`.

Establish `hcl : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z)`. Rewrite using `[← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]`. Conclude with `hfin.isClosed_biUnion (fun c hc => hc.2)`. Rewrite `h1` using `[hcl.closure_eq]`. Establish `hm : z ∈ closure ({z} : Set Z) ∩ closedPoints Z`.

Rewrite using `[h1]`. Use `first`. Consider the case `exact subset_closure (Set.mem_singleton z)`. Consider the case `exact subset_closure (subset_closure (Set.mem_singleton z))`. Conclude with `hm.2`.

Use `⟨pointOfClosedPoint f _ hz, pointOfClosedPoint_comp f _ hz, ?_⟩` and prove the remaining obligations. Establish `hdesc` using `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z w`. Use `set φ := Z.descResidueField (Scheme.stalkClosedPointTo w)`. Establish `hφ : Spec.map φ = spMap i ≫ Spec.map (residueFieldIsoBase f _ hz).hom`. Establish `e1 : w ≫ f = Spec.map φ ≫ Spec.map (residueFieldIsoBase f _ hz).inv`.

Rewrite using `[SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdesc]`. Rewrite using `[← hw, e1, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.comp_id]`. Rewrite using `[pointOfClosedPoint, ← Category.assoc, ← hφ, hdesc]`.
-/
theorem exists_section_of_finite {Z : Scheme.{0}} {k K : Type} [Field k] [IsAlgClosed k] [Field K] (i : k →+* K)
    (f : Z ⟶ Sp k) [LocallyOfFiniteType f] (hf : Finite {p : Sp k ⟶ Z // p ≫ f = 𝟙 _}) (w : Sp K ⟶ Z)
    (hw : w ≫ f = spMap i) : ∃ p : Sp k ⟶ Z, p ≫ f = 𝟙 _ ∧ w = spMap i ≫ p := by
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace f
  haveI : Finite (closedPoints Z) := Finite.of_equiv _ (pointEquivClosedPoint f)
  have hz : IsClosed ({w (IsLocalRing.closedPoint K)} : Set Z) := by
    set z := w (IsLocalRing.closedPoint K)
    have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (isClosed_closure (s := ({z} : Set Z))).isLocallyClosed
    have hfin : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
      (Set.toFinite (closedPoints Z)).subset Set.inter_subset_right
    have hcl : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
      rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
      exact hfin.isClosed_biUnion (fun c hc => hc.2)
    rw [hcl.closure_eq] at h1
    have hm : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
      rw [h1]
      first
        | exact subset_closure (Set.mem_singleton z)
        | exact subset_closure (subset_closure (Set.mem_singleton z))
    exact hm.2
  refine ⟨pointOfClosedPoint f _ hz, pointOfClosedPoint_comp f _ hz, ?_⟩
  have hdesc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z w
  set φ := Z.descResidueField (Scheme.stalkClosedPointTo w)
  have hφ : Spec.map φ = spMap i ≫ Spec.map (residueFieldIsoBase f _ hz).hom := by
    have e1 : w ≫ f = Spec.map φ ≫ Spec.map (residueFieldIsoBase f _ hz).inv := by
      rw [SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdesc]
    rw [← hw, e1, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.comp_id]
  rw [pointOfClosedPoint, ← Category.assoc, ← hφ, hdesc]

/- English proof (translation)
Set `Kn : Over X` to `pullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)`. Set `π : Kn ⟶ G` to `pullback.fst _ _`. Establish `hπ0 : π ≫ (𝟙 G) ^ n = 1`. Rewrite using `[pullback.condition, comp_one]`. Establish `hπ : ∀ {Y : Over X} (q : Y ⟶ Kn), (q ≫ π) ^ n = 1`.

Introduce `Y q`. Rewrite using `[← Category.comp_id (q ≫ π), ← comp_pow, Category.assoc, hπ0, comp_one]`. Establish `hmk : ∀ {Y : Over X} (a : Y ⟶ G), a ^ n = 1 → a ≫ (𝟙 G) ^ n = toUnit Y ≫ (1 : 𝟙_ (Over X) ⟶ G)`. Introduce `Y a ha`. Rewrite using `[comp_pow, Category.comp_id, ha, comp_one]`.

Establish `hfac : ∀ {Y : Over X} (a : Y ⟶ G) (ha : a ^ n = 1) (q : Y ⟶ Kn), q ≫ π = a → q = pullback.lift a (toUnit Y) (hmk a ha)`. Introduce `Y a ha q hq`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst]`. Conclude with `hq`.

Conclude with `Subsingleton.elim _ _`. Use `haveI h1lft : LocallyOfFiniteType (1 : 𝟙_ (Over X) ⟶ G).left := by`. Establish `hc : (1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom = 𝟙 _` using `Over.w _`. Use `haveI : LocallyOfFiniteType ((1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom) := by`. Rewrite using `[hc]`.

Use `infer_instance`. Conclude with `locallyOfFiniteType_of_comp _ G.hom`. Use `haveI hπlft : LocallyOfFiniteType π.left := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) ((IsPullback.of_hasPullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)).map (Over.forget X)).flip h1lft`. Use `haveI : LocallyOfFiniteType Kn.hom := by`. Rewrite using `[← Over.w π]`.

Use `infer_instance`. Set `fZ : pullback Kn.hom x ⟶ Sp k` to `pullback.snd Kn.hom x`. Establish `hq : ∀ p : Sp k ⟶ pullback Kn.hom x, p ≫ fZ = 𝟙 _ → (p ≫ pullback.fst Kn.hom x) ≫ Kn.hom = (Over.mk x).hom`. Introduce `p hp`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`.

Express the relevant statement in the definitionally equal form `(p ≫ fZ) ≫ x = x`. Rewrite using `[hp, Category.id_comp]`. Establish `hfin : Finite {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _}`. Use `Finite.of_surjective (fun a : {a : Over.mk x ⟶ G // a ^ n = 1} => (⟨pullback.lift (pullback.lift a.1 (toUnit _) (hmk a.1 a.2)).left (𝟙 _) (by rw [Over.w, Category.id_comp]; rfl), pullback.lift_snd _ _ _⟩ : {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _})) ?_` and prove the remaining obligations. Introduce and unpack `⟨p, hp⟩`.

Set `q : Over.mk x ⟶ Kn` to `Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)`. Use `⟨⟨q ≫ π, hπ q⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, ← hfac (q ≫ π) (hπ q) q rfl]`.

Both sides reduce to the same expression. Rewrite using `[pullback.lift_snd]`. Conclude with `hp.symm`. Set `w : Sp K ⟶ pullback Kn.hom x` to `pullback.lift (pullback.lift g (toUnit _) (hmk g hg)).left (spMap i) (by rw [Over.w]; rfl)`. Take `⟨p, hp, hwp⟩` from `exists_section_of_finite i fZ hfin w (pullback.lift_snd _ _ _)`.

Set `q : Over.mk x ⟶ Kn` to `Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)`. Use `⟨q ≫ π, hπ q, ?_⟩` and prove the remaining obligations. Use `ext`. Establish `e1 : w ≫ pullback.fst Kn.hom x = (pullback.lift g (toUnit _) (hmk g hg)).left` using `pullback.lift_fst _ _ _`. Establish `e2` using `congrArg Over.Hom.left (pullback.lift_fst g (toUnit _) (hmk g hg))`.

Rewrite `e2` using `[Over.comp_left]`. Rewrite using `[← e2, ← e1, hwp]`. Simplify using `[q, extPt, π]`.
-/
theorem torsion_desc {X : Scheme.{0}} (G : Over X) [GrpObj G] [LocallyOfFiniteType G.hom] {k K : Type} [Field k]
    [IsAlgClosed k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) (n : ℕ) (hf : Finite {g : Over.mk x ⟶ G // g ^ n = 1})
    (g : Over.mk (spMap i ≫ x) ⟶ G) (hg : g ^ n = 1) : ∃ y : Over.mk x ⟶ G, y ^ n = 1 ∧ extPt i x ≫ y = g := by
  let Kn : Over X := pullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)
  let π : Kn ⟶ G := pullback.fst _ _
  have hπ0 : π ≫ (𝟙 G) ^ n = 1 := by
    rw [pullback.condition, comp_one]
  have hπ : ∀ {Y : Over X} (q : Y ⟶ Kn), (q ≫ π) ^ n = 1 := by
    intro Y q
    rw [← Category.comp_id (q ≫ π), ← comp_pow, Category.assoc, hπ0, comp_one]
  have hmk : ∀ {Y : Over X} (a : Y ⟶ G), a ^ n = 1 → a ≫ (𝟙 G) ^ n = toUnit Y ≫ (1 : 𝟙_ (Over X) ⟶ G) := by
    intro Y a ha
    rw [comp_pow, Category.comp_id, ha, comp_one]
  have hfac : ∀ {Y : Over X} (a : Y ⟶ G) (ha : a ^ n = 1) (q : Y ⟶ Kn), q ≫ π = a →
      q = pullback.lift a (toUnit Y) (hmk a ha) := by
    intro Y a ha q hq
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hq
    · exact Subsingleton.elim _ _
  haveI h1lft : LocallyOfFiniteType (1 : 𝟙_ (Over X) ⟶ G).left := by
    have hc : (1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom = 𝟙 _ := Over.w _
    haveI : LocallyOfFiniteType ((1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  haveI hπlft : LocallyOfFiniteType π.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      ((IsPullback.of_hasPullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)).map (Over.forget X)).flip h1lft
  haveI : LocallyOfFiniteType Kn.hom := by
    rw [← Over.w π]
    infer_instance
  let fZ : pullback Kn.hom x ⟶ Sp k := pullback.snd Kn.hom x
  have hq : ∀ p : Sp k ⟶ pullback Kn.hom x, p ≫ fZ = 𝟙 _ →
      (p ≫ pullback.fst Kn.hom x) ≫ Kn.hom = (Over.mk x).hom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ fZ) ≫ x = x
    rw [hp, Category.id_comp]
  have hfin : Finite {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _} := by
    refine Finite.of_surjective (fun a : {a : Over.mk x ⟶ G // a ^ n = 1} =>
      (⟨pullback.lift (pullback.lift a.1 (toUnit _) (hmk a.1 a.2)).left (𝟙 _)
        (by rw [Over.w, Category.id_comp]; rfl), pullback.lift_snd _ _ _⟩ :
        {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _})) ?_
    rintro ⟨p, hp⟩
    let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
    refine ⟨⟨q ≫ π, hπ q⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hfac (q ≫ π) (hπ q) q rfl]
      rfl
    · rw [pullback.lift_snd]
      exact hp.symm
  let w : Sp K ⟶ pullback Kn.hom x := pullback.lift (pullback.lift g (toUnit _) (hmk g hg)).left (spMap i)
    (by rw [Over.w]; rfl)
  obtain ⟨p, hp, hwp⟩ := exists_section_of_finite i fZ hfin w (pullback.lift_snd _ _ _)
  let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
  refine ⟨q ≫ π, hπ q, ?_⟩
  ext
  have e1 : w ≫ pullback.fst Kn.hom x = (pullback.lift g (toUnit _) (hmk g hg)).left := pullback.lift_fst _ _ _
  have e2 := congrArg Over.Hom.left (pullback.lift_fst g (toUnit _) (hmk g hg))
  rw [Over.comp_left] at e2
  rw [← e2, ← e1, hwp]
  simp [q, extPt, π]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun q => q.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))` as an intermediate fact. Conclude with `this.symm`.
-/
theorem unitOn_map {k K : Type} [Field k] [Field K] (i : k →+* K) (c : kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  have := congrArg (fun q => q.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))
  exact this.symm

end PositivityTheory.HtPt.Mg
