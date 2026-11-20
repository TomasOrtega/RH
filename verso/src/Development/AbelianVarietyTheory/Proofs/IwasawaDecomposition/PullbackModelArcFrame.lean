import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolArcData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {W : ValuationSubring ℂ}

/- English proof (translation)
Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Establish `hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F)` using `⟨⟨inferInstance, inferInstance⟩, inferInstance, (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩`. Conclude with `GlobalTheory.ModelRelCompare.mono_spMap_of_overring (β' := (c.V W).subtype) hβ Subtype.val_injective bV (RingHom.ext fun x => hbV x)`.
-/
theorem mono_spMap_incl (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) :
    Mono (spMap bV) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  have hβ : IsDedFrac (algebraMap (𝓞 c.F) c.F) := ⟨⟨inferInstance, inferInstance⟩, inferInstance,
    (inferInstance : IsFractionRing (𝓞 c.F) c.F)⟩
  exact GlobalTheory.ModelRelCompare.mono_spMap_of_overring (β' := (c.V W).subtype) hβ Subtype.val_injective bV
    (RingHom.ext fun x => hbV x)

/- English proof (translation)
Rewrite using `[← spMap_comp]`. Use `congr 1`. Conclude with `(RingHom.ext hbV).symm`.
-/
theorem spMap_algebraMap_eq (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) :
    spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
  rw [← spMap_comp]
  congr 1
  exact (RingHom.ext hbV).symm

/- English proof (translation)
Use `haveI := mono_spMap_incl bV hbV`. Establish `hYj : Mono Y.j` using `GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)`. Establish `hw : (χ' ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s = (y ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[Category.assoc, pullback.condition, ← hf, spMap_algebraMap_eq bV hbV]`. Simplify using `only [← Category.assoc]`.

Rewrite using `[← h]`. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc Y.j, Model.j_s]`. Simplify using `only [Category.assoc]`. Establish `hr : Set.range (pullback.lift _ _ hw) ⊆ Set.range Z.jQ`.

Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[← Z.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]`. Use `(abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 _).2 ?_` and prove the remaining obligations. Use `(abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 _).1 ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]`.

Conclude with `GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _`. Use `Z.jQ_open` as an intermediate fact. Establish `hg` using `IsOpenImmersion.lift_fac Z.jQ _ hr`. Establish `e1 : χ' = IsOpenImmersion.lift Z.jQ _ hr ≫ a₀`. Rewrite using `[← cancel_mono (pullback.fst Z.s (spMap bV)), Category.assoc, ha₀, Model.j, ← Category.assoc, hg, pullback.lift_fst]`.

Establish `e2 : IsOpenImmersion.lift Z.jQ _ hr = y`. Rewrite using `[← cancel_mono Y.j, ← ha₀f, ← Category.assoc, ← e1, ← h, ha₀f]`. Rewrite using `[e1, e2]`.
-/
theorem eq_comp_of_comp (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f)
    (hf : f ≫ Y.s = pullback.snd Z.s (spMap bV)) (a₀ : Xo.XF c ⟶ pullback Z.s (spMap bV))
    (ha₀ : a₀ ≫ pullback.fst Z.s (spMap bV) = Z.j) (ha₀f : a₀ ≫ f = Y.j) {T : Scheme.{0}}
    (χ' : T ⟶ pullback Z.s (spMap bV)) (y : T ⟶ Xo.XF c) (h : y ≫ Y.j = χ' ≫ f) : χ' = y ≫ a₀ := by
  haveI := mono_spMap_incl bV hbV
  have hYj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hw : (χ' ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s =
      (y ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, pullback.condition, ← hf, spMap_algebraMap_eq bV hbV]
    simp only [← Category.assoc]
    rw [← h]
    simp only [Category.assoc]
    rw [← Category.assoc Y.j, Model.j_s]
    simp only [Category.assoc]
  have hr : Set.range (pullback.lift _ _ hw) ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Z.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    refine (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 _).2 ?_
    refine (abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 _).1 ?_
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _
  have := Z.jQ_open
  have hg := IsOpenImmersion.lift_fac Z.jQ _ hr
  have e1 : χ' = IsOpenImmersion.lift Z.jQ _ hr ≫ a₀ := by
    rw [← cancel_mono (pullback.fst Z.s (spMap bV)), Category.assoc, ha₀, Model.j, ← Category.assoc, hg,
      pullback.lift_fst]
  have e2 : IsOpenImmersion.lift Z.jQ _ hr = y := by
    rw [← cancel_mono Y.j, ← ha₀f, ← Category.assoc, ← e1, ← h, ha₀f]
  rw [e1, e2]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj hc O' _ _ b' a R _ _ I f₀ u χV _`. Use `haveI := mono_spMap_incl bV hbV`. Set `a₀ : Xo.XF c ⟶ pullback Z.s (spMap bV)` to `pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) (by rw [Model.j_s, spMap_algebraMap_eq bV hbV, Category.assoc])`. Establish `ha₀ : a₀ ≫ pullback.fst Z.s (spMap bV) = Z.j` using `pullback.lift_fst _ _ _`. Establish `ha₀f : a₀ ≫ f = Y.j` using `hj a₀ ha₀`.

Establish `tr : ∀ {T : Scheme.{0}} (g : T ⟶ t.G.left) (yF : T ⟶ Xo.XF c) (σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G) (σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), σZ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ → g ≫ t.G.hom = yF ≫ a₀ → (g ≫ m₁.φ = yF ≫ σZ.left ≫ Z.m.φ ↔ g ≫ m₂.φ = yF ≫ σY.left ≫ …`. Introduce `T g yF σZ σY h0 hb`. Establish `b₁ : σZ.left ≫ Z.oF.t.G.hom = 𝟙 _` using `Over.w σZ`. Establish `b₂ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _` using `Over.w σY`. Use `dom_iff m₁ m₂ hc a₀ ha₀ g (yF ≫ σZ.left) (yF ≫ σY.left) (by rw [Category.assoc, h0, Category.assoc]) (by rw [Category.assoc, b₁, Category.assoc, b₂]) (by rw [hb, Category.assoc, ← Category.assoc σZ.left, b₁, Category.id_comp])` as an intermediate fact.

Simplify `this` using `only [Category.assoc]`. Establish `base : ∀ (t' : SAB H (Sp R)) (P : PELUnif I t') (F : Type) [Field F] [Algebra (FractionRing R) F] (x : Out.TFK (R` using `R) F ⟶ P.A.A), (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R)) ≫ t'.G.hom = Out.jFK (R := R) F ≫ Out.jK R := by`. Introduce `t' P F _ _ x`. Establish `a₁ : P.U.gen.inv.left ≫ pullback.snd t'.G.hom (Out.jK R) = P.A.A.hom` using `Over.w P.U.gen.inv`. Establish `a₂ : x.left ≫ P.A.A.hom = Out.jFK (R` using `R) F := Over.w x`.

Rewrite using `[Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁, ← Category.assoc, a₂]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩`. Take `⟨n, hn⟩` from `GlobalTheory.ObjMaps.exists_sab_cancel m₁ m`. Take `⟨m', hm'⟩` from `GlobalTheory.ObjMaps.exists_sab_comp m₂ n`.

Use `⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu => ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩` and prove the remaining obligations. Establish `hχ : Out.jFK (R` using `R) F ≫ Out.jK R ≫ χV = yF ≫ a₀ := eq_comp_of_comp Z Y bV hbV f t m₁ m₂ hf a₀ ha₀ ha₀f _ yF (by rw [hyF]; simp only [Category.assoc])`. Establish `hyZ : yF ≫ Z.j = Out.jFK (R` using `R) F ≫ Out.jK R ≫ χV ≫ pullback.fst _ _ := by`. Rewrite using `[← ha₀, ← Category.assoc, ← hχ]`. Simplify using `only [Category.assoc]`.

Establish `hb : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom = yF ≫ a₀`. Establish `h₀` using `congrArg (· ≫ χV) (base t' P F x)`. Rewrite using `[← hχ]`. Simplify using `only [Category.assoc] at h₀ ⊢`. Rewrite using `[n.cart.1.w]`.

Conclude with `h₀`. Establish `go : ∀ σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G, σZ.left ≫ Z.m0.toSABMap.φ = σ.left ≫ Y.m0.toSABMap.φ → x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m.φ = yF ≫ σZ.left ≫ Z.m.φ`. Introduce `σZ h0`. Use `(tr _ yF σZ σ h0 hb).2 (by rw [hm'] at e4; simpa only [Category.assoc] using e4)` as an intermediate fact. Rewrite using `[hn]`.

Simplify `this` using `only [Category.assoc]`. Break down `hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩` into its components or cases. Conclude with `(s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3 (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))`. Conclude with `(s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3 (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))`. Introduce and unpack `⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩`.

Take `⟨n, hn⟩` from `GlobalTheory.ObjMaps.exists_sab_cancel m₂ m'`. Take `⟨m, hm⟩` from `GlobalTheory.ObjMaps.exists_sab_comp m₁ n`. Use `⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu => ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩` and prove the remaining obligations. Establish `hχ : Out.jFK (R` using `R) F ≫ Out.jK R ≫ χV = yF ≫ a₀ := by`. Rewrite using `[← cancel_mono (pullback.fst Z.s (spMap bV))]`.

Simplify using `only [Category.assoc]`. Rewrite using `[ha₀, hyF]`. Establish `hyY : yF ≫ Y.j = Out.jFK (R` using `R) F ≫ Out.jK R ≫ χV ≫ f := by`. Rewrite using `[← ha₀f, ← Category.assoc, ← hχ]`. Simplify using `only [Category.assoc]`.

Establish `hb : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom = yF ≫ a₀`. Establish `h₀` using `congrArg (· ≫ χV) (base t' P F x)`. Rewrite using `[← hχ]`. Simplify using `only [Category.assoc] at h₀ ⊢`. Rewrite using `[n.cart.1.w]`.

Conclude with `h₀`. Establish `go : ∀ σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ → x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m'.φ = yF ≫ σY.left ≫ Y.m.φ`. Introduce `σY h0`. Use `(tr _ yF σ σY h0 hb).1 (by rw [hm] at e4; simpa only [Category.assoc] using e4)` as an intermediate fact. Rewrite using `[hn]`.

Simplify `this` using `only [Category.assoc]`. Break down `hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩` into its components or cases. Conclude with `(s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3 (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))`. Conclude with `(s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3 (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))`.
-/
theorem hasArcData_iff_moveV : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] (b' : c.V W →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV))
      (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (f₀ : O' →+* R) (u : R) (χV : Sp R ⟶ pullback Z.s (spMap bV)),
      χV ≫ pullback.snd Z.s (spMap bV) = spMap f₀ ≫ spMap b' →
      (Z.HasArcData a I f₀ u (χV ≫ pullback.fst Z.s (spMap bV)) ↔
        Y.HasArcData (GlobalTheory.PolArc.moveV bV hbV b' a) I f₀ u (χV ≫ f)) := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hf hj hc O' _ _ b' a R _ _ I f₀ u χV _
  haveI := mono_spMap_incl bV hbV
  let a₀ : Xo.XF c ⟶ pullback Z.s (spMap bV) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype)
      (by rw [Model.j_s, spMap_algebraMap_eq bV hbV, Category.assoc])
  have ha₀ : a₀ ≫ pullback.fst Z.s (spMap bV) = Z.j := pullback.lift_fst _ _ _
  have ha₀f : a₀ ≫ f = Y.j := hj a₀ ha₀

  have tr : ∀ {T : Scheme.{0}} (g : T ⟶ t.G.left) (yF : T ⟶ Xo.XF c) (σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G)
      (σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), σZ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ →
      g ≫ t.G.hom = yF ≫ a₀ → (g ≫ m₁.φ = yF ≫ σZ.left ≫ Z.m.φ ↔ g ≫ m₂.φ = yF ≫ σY.left ≫ Y.m.φ) := by
    intro T g yF σZ σY h0 hb
    have b₁ : σZ.left ≫ Z.oF.t.G.hom = 𝟙 _ := Over.w σZ
    have b₂ : σY.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σY
    have := dom_iff m₁ m₂ hc a₀ ha₀ g (yF ≫ σZ.left) (yF ≫ σY.left) (by rw [Category.assoc, h0, Category.assoc])
      (by rw [Category.assoc, b₁, Category.assoc, b₂]) (by rw [hb, Category.assoc, ← Category.assoc σZ.left, b₁,
        Category.id_comp])
    simpa only [Category.assoc] using this

  have base : ∀ (t' : SAB H (Sp R)) (P : PELUnif I t') (F : Type) [Field F] [Algebra (FractionRing R) F]
      (x : Out.TFK (R := R) F ⟶ P.A.A),
      (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R)) ≫ t'.G.hom = Out.jFK (R := R) F ≫ Out.jK R := by
    intro t' P F _ _ x
    have a₁ : P.U.gen.inv.left ≫ pullback.snd t'.G.hom (Out.jK R) = P.A.A.hom := Over.w P.U.gen.inv
    have a₂ : x.left ≫ P.A.A.hom = Out.jFK (R := R) F := Over.w x
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd _ _), a₁,
      ← Category.assoc, a₂]
  constructor
  · rintro ⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩
    obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m₁ m
    obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ n
    refine ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
      ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
    have hχ : Out.jFK (R := R) F ≫ Out.jK R ≫ χV = yF ≫ a₀ :=
      eq_comp_of_comp Z Y bV hbV f t m₁ m₂ hf a₀ ha₀ ha₀f _ yF (by rw [hyF]; simp only [Category.assoc])
    have hyZ : yF ≫ Z.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χV ≫ pullback.fst _ _ := by
      rw [← ha₀, ← Category.assoc, ← hχ]; simp only [Category.assoc]
    have hb : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom = yF ≫ a₀ := by
      have h₀ := congrArg (· ≫ χV) (base t' P F x)
      rw [← hχ]
      simp only [Category.assoc] at h₀ ⊢
      rw [n.cart.1.w]
      exact h₀
    have go : ∀ σZ : 𝟙_ (Over (Xo.XF c)) ⟶ Z.oF.t.G, σZ.left ≫ Z.m0.toSABMap.φ = σ.left ≫ Y.m0.toSABMap.φ →
        x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m.φ = yF ≫ σZ.left ≫ Z.m.φ := by
      intro σZ h0
      have := (tr _ yF σZ σ h0 hb).2 (by rw [hm'] at e4; simpa only [Category.assoc] using e4)
      rw [hn]; simpa only [Category.assoc] using this
    rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
    · exact (s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
    · exact (s6 F uF ha hu).2 yF hyZ k p₀ (Z.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))
  · rintro ⟨t', m', P, φ, he, w, e, s1, s2, s3, s4, s5, s6⟩
    obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m₂ m'
    obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ n
    refine ⟨t', m, P, φ, he, w, e, s1, s2, s3, s4, s5, fun F _ _ _ _ uF ha hu =>
      ⟨(s6 F uF ha hu).1, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => ?_⟩⟩
    have hχ : Out.jFK (R := R) F ≫ Out.jK R ≫ χV = yF ≫ a₀ := by
      rw [← cancel_mono (pullback.fst Z.s (spMap bV))]
      simp only [Category.assoc]
      rw [ha₀, hyF]
    have hyY : yF ≫ Y.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χV ≫ f := by
      rw [← ha₀f, ← Category.assoc, ← hχ]; simp only [Category.assoc]
    have hb : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ n.φ) ≫ t.G.hom = yF ≫ a₀ := by
      have h₀ := congrArg (· ≫ χV) (base t' P F x)
      rw [← hχ]
      simp only [Category.assoc] at h₀ ⊢
      rw [n.cart.1.w]
      exact h₀
    have go : ∀ σY : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G, σ.left ≫ Z.m0.toSABMap.φ = σY.left ≫ Y.m0.toSABMap.φ →
        x.left ≫ P.U.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R) ≫ m'.φ = yF ≫ σY.left ≫ Y.m.φ := by
      intro σY h0
      have := (tr _ yF σ σY h0 hb).1 (by rw [hm] at e4; simpa only [Category.assoc] using e4)
      rw [hn]; simpa only [Category.assoc] using this
    rcases hσ with ⟨hk, v, hv, rfl⟩ | ⟨hk, v, hvm, hv, rfl⟩
    · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.etaA v) (Or.inl ⟨hk, v, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.etaA v).trans (Y.m0.etaA v).symm))
    · exact (s6 F uF ha hu).2 yF hyY k p₀ (Y.oF.eta v) (Or.inr ⟨hk, v, hvm, hv, rfl⟩) q₀ q x e1 e2 e3
        (go _ ((Z.m0.eta v).trans (Y.m0.eta v).symm))

end GlobalTheory.PolArcData
