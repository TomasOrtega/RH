import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.OpenReg

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Transfer

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {x : Sp R ⟶ S'} {x' : Sp R ⟶ S}

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (h : A →+* B) :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[spMap_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsMul_over (s : R) : spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) =
    spMap (algebraMap R (DualNumber R)) := by
  rw [spMap_comp]
  congr 1
  ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Assemble the required witnesses or components as `⟨m.cart.1.lift v q hv, m.cart.1.lift_snd _ _ _, m.cart.1.lift_fst _ _ _⟩`.
-/
theorem exists_lift {T : Scheme.{0}} (q : T ⟶ S') (v : T ⟶ t.G.left) (hv : v ≫ t.G.hom = q ≫ f) :
    ∃ w : T ⟶ t'.G.left, w ≫ t'.G.hom = q ∧ w ≫ m.φ = v :=
  ⟨m.cart.1.lift v q hv, m.cart.1.lift_snd _ _ _, m.cart.1.lift_fst _ _ _⟩

/- English proof (translation)
Substitute `hx` using the available equality. Establish `e : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ f) ⟶ t.G).left` using `congrArg (fun z => z.left) (map_one (pushHom m.cart (Over.mk x)))`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨hw, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc]`. Conclude with `h.2.trans e.symm`. Establish `hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R` using `RingHom.ext fun r => by simp`. Rewrite using `[Category.assoc, hw, ← Category.assoc, spMap_comp, hid, Over.w]`. Conclude with `(congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)`.

Introduce `h`. Use `⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw, Category.assoc], ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc]`. Conclude with `(congrArg (· ≫ m.φ) h.2).trans e`.
-/
theorem tan_iff (hx : x ≫ f = x') {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsTanAtG t x' (w ≫ m.φ) ↔ IsTanAtG t' x w := by
  subst hx
  have e : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ f) ⟶ t.G).left :=
    congrArg (fun z => z.left) (map_one (pushHom m.cart (Over.mk x)))
  constructor
  · intro h
    refine ⟨hw, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h.2.trans e.symm
    · have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
        RingHom.ext fun r => by simp
      rw [Category.assoc, hw, ← Category.assoc, spMap_comp, hid, Over.w]
      exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw, Category.assoc], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h.2).trans e

/- English proof (translation)
Establish `e : (w ≫ m.φ) ≫ (t.act.act a).left = (w ≫ (t'.act.act a).left) ≫ m.φ`. Rewrite using `[Category.assoc, Category.assoc, m.act]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc (spMap _)]`. Conclude with `h`. Rewrite using `[Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, epsMul_over]`. Introduce `h`.

Rewrite using `[h, Category.assoc]`.
-/
theorem eig_iff {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : 𝓞 E) (s : R) :
    (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul s) ≫ w ≫ m.φ ↔
      w ≫ (t'.act.act a).left = spMap (epsMul s) ≫ w := by
  have e : (w ≫ m.φ) ≫ (t.act.act a).left = (w ≫ (t'.act.act a).left) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc (spMap _)]; exact h
    · rw [Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, epsMul_over]
  · intro h
    rw [h, Category.assoc]

/- English proof (translation)
Substitute `hq` using the available equality. Establish `push : ∀ u : Fin n → (Over.mk q ⟶ t'.G), ((List.ofFn u).prod).left ≫ m.φ = ((List.ofFn fun i => pushHom m.cart (Over.mk q) (u i)).prod).left` using `fun u => by`. Use `map_list_prod (pushHom m.cart (Over.mk q)) (List.ofFn u)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Conclude with `congrArg (fun z => z.left) this`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hw'⟩`. Set `u' : Fin n → (Over.mk q ⟶ t'.G)` to `fun i => Over.homMk (v i) (hv i)`. Establish `e : u = fun i => pushHom m.cart (Over.mk q) (u' i)` using `funext fun i => Over.OverMorphism.ext (hu i)`. Use `⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations.

Rewrite `hw'` using `[e]`. Conclude with `(push u').trans hw'`. Rewrite using `[Over.w, hw]`. Both sides reduce to the same expression. Introduce and unpack `⟨u, hu, rfl⟩`.

Use `⟨fun i => pushHom m.cart (Over.mk q) (u i), fun i => ?_, (push u).symm⟩` and prove the remaining obligations. Use `show (u i).left ≫ m.φ = _`. Rewrite using `[hu]`.
-/
theorem prod_iff {q : Sp (DualNumber R) ⟶ S'} {q' : Sp (DualNumber R) ⟶ S} (hq : q ≫ f = q') {n : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (hv : ∀ i, v i ≫ t'.G.hom = q)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = q) :
    (∃ u : Fin n → (Over.mk q' ⟶ t.G), (∀ i, (u i).left = v i ≫ m.φ) ∧ ((List.ofFn u).prod).left = w ≫ m.φ) ↔
      ∃ u : Fin n → (Over.mk q ⟶ t'.G), (∀ i, (u i).left = v i) ∧ ((List.ofFn u).prod).left = w := by
  subst hq
  have push : ∀ u : Fin n → (Over.mk q ⟶ t'.G), ((List.ofFn u).prod).left ≫ m.φ =
      ((List.ofFn fun i => pushHom m.cart (Over.mk q) (u i)).prod).left := fun u => by
    have := map_list_prod (pushHom m.cart (Over.mk q)) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact congrArg (fun z => z.left) this
  constructor
  · rintro ⟨u, hu, hw'⟩
    let u' : Fin n → (Over.mk q ⟶ t'.G) := fun i => Over.homMk (v i) (hv i)
    have e : u = fun i => pushHom m.cart (Over.mk q) (u' i) := funext fun i => Over.OverMorphism.ext (hu i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · rw [e] at hw'
      exact (push u').trans hw'
    · rw [Over.w, hw]; rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (Over.mk q) (u i), fun i => ?_, (push u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu]

/- English proof (translation)
Use `prod_iff m (q := spMap (algebraMap R (DualNumber R)) ≫ x) (q' := spMap (algebraMap R (DualNumber R)) ≫ x') (by rw [Category.assoc, hx]) (v := fun i => spMap (epsMul (cf i)) ≫ v i) (fun i => by rw [Category.assoc, hv, ← Category.assoc, epsMul_over]) hw` as an intermediate fact. Simplify using `only [Category.assoc] at this`. Conclude with `this`.
-/
theorem comb_iff (hx : x ≫ f = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (cf : Fin n → R)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsCombAtG t x' (fun i => v i ≫ m.φ) cf (w ≫ m.φ) ↔ IsCombAtG t' x v cf w := by
  have := prod_iff m (q := spMap (algebraMap R (DualNumber R)) ≫ x) (q' := spMap (algebraMap R (DualNumber R)) ≫ x')
    (by rw [Category.assoc, hx]) (v := fun i => spMap (epsMul (cf i)) ≫ v i)
    (fun i => by rw [Category.assoc, hv, ← Category.assoc, epsMul_over]) hw
  simp only [Category.assoc] at this
  exact this

end Transfer

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

/- English proof (translation)
Establish `hover : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c R`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp]`. Both sides reduce to the same expression. Take `⟨z, hz⟩` from `GlobalTheory.FlagTan.exists_frPt (c := c) _ hover`. Use `choose w hw1 hw2 using fun τ i => exists_lift Z.m (spMap (algebraMap R (DualNumber R)) ≫ xF) (f.v τ i) (by rw [(f.tan τ i).1, ← hx, Category.assoc])`.

Use `⟨⟨z.x, z.x_over, fun τ i => w τ i ≫ Z.m0.toSABMap.φ, fun τ i => ?_, fun τ i a => ?_, fun τ v hv he => ?_, z.s, z.gen⟩, w, hz, fun τ i => ⟨hw1 τ i, rfl, hw2 τ i⟩⟩` and prove the remaining obligations. Conclude with `(tan_iff Z.m0.toSABMap hz.symm (hw1 τ i)).2 ((tan_iff Z.m hx (hw1 τ i)).1 (hw2 τ i ▸ f.tan τ i))`. Conclude with `(eig_iff Z.m0.toSABMap (hw1 τ i) a _).2 ((eig_iff Z.m (hw1 τ i) a _).1 (hw2 τ i ▸ f.eig τ i a))`. Take `⟨v', h1, rfl⟩` from `exists_lift Z.m0.toSABMap (spMap (algebraMap R (DualNumber R)) ≫ xF) v (by rw [hv.1, hz, Category.assoc])`. Establish `hb` using `f.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hz.symm h1).1 hv)) fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))`.

Establish `e : f.v τ = fun i => w τ i ≫ Z.m.φ` using `funext fun i => (hw2 τ i).symm`. Rewrite `hb` using `[e]`. Conclude with `(existsUnique_congr fun cf => (comb_iff Z.m0.toSABMap hz.symm (hw1 τ) cf h1).trans (comb_iff Z.m hx (hw1 τ) cf h1).symm).2 hb`.
-/
theorem exists_frPt_of_eigFrame {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) :
    ∃ (y : FrPt Xo c R) (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.oF.t.G.left)),
      y.x = xF ≫ pullback.fst _ _ ∧ ∀ τ i, w τ i ≫ Z.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ xF ∧
        w τ i ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w τ i ≫ Z.m.φ = f.v τ i := by
  have hover : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp]; rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frPt (c := c) _ hover
  choose w hw1 hw2 using fun τ i => exists_lift Z.m (spMap (algebraMap R (DualNumber R)) ≫ xF) (f.v τ i)
    (by rw [(f.tan τ i).1, ← hx, Category.assoc])
  refine ⟨⟨z.x, z.x_over, fun τ i => w τ i ≫ Z.m0.toSABMap.φ, fun τ i => ?_, fun τ i a => ?_, fun τ v hv he => ?_,
    z.s, z.gen⟩, w, hz, fun τ i => ⟨hw1 τ i, rfl, hw2 τ i⟩⟩
  · exact (tan_iff Z.m0.toSABMap hz.symm (hw1 τ i)).2 ((tan_iff Z.m hx (hw1 τ i)).1 (hw2 τ i ▸ f.tan τ i))
  · exact (eig_iff Z.m0.toSABMap (hw1 τ i) a _).2 ((eig_iff Z.m (hw1 τ i) a _).1 (hw2 τ i ▸ f.eig τ i a))
  · obtain ⟨v', h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap R (DualNumber R)) ≫ xF) v
      (by rw [hv.1, hz, Category.assoc])
    have hb := f.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hz.symm h1).1 hv))
      fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
    have e : f.v τ = fun i => w τ i ≫ Z.m.φ := funext fun i => (hw2 τ i).symm
    rw [e] at hb
    exact (existsUnique_congr fun cf => (comb_iff Z.m0.toSABMap hz.symm (hw1 τ) cf h1).trans
      (comb_iff Z.m hx (hw1 τ) cf h1).symm).2 hb

/- English proof (translation)
Take `⟨y, w, hyx, hw⟩` from `exists_frPt_of_eigFrame xF hs hx f`. Take `⟨z, hz⟩` from `GlobalTheory.FlagTan.exists_frMap ψ y`. Establish `h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = y0.x` using `pullback.lift_fst _ _ _`. Establish `h1 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = z.x` using `by rw [hz.1, hyx, hy, Category.assoc]`. Establish `h2 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ ≫ pullback.fst _ _ = x'` using `by rw [hT.1, hy, ← hx, Category.assoc]`.

Take `⟨g0, a, -, hc⟩` from `(GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c K z y0).1 (h0.symm.trans h1)`. Use `choose cf hcf1 hcf2 hcf3 using hT.2.2`. Establish `hcomb : ∀ τ i, IsCombAt z.x (z.u τ) (cf τ i) (y0.u τ i)` using `fun τ i => by`. Take `⟨w0, a1, a2, a3⟩` from `hu τ i`. Establish `hv : ∀ k, (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0` using `fun k => by`.

Rewrite using `[Category.assoc, (hw τ k).1, hy, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]`. Establish `e1 : z.u τ = fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m0.toSABMap.φ` using `funext fun k => by`. Rewrite using `[hz.2.1, Category.assoc, (hw τ k).2.1]`. Establish `e2 : (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) = fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m.φ` using `funext fun k => by`. Rewrite using `[Category.assoc, (hw τ k).2.2]`.

Establish `b` using `hcf3 τ i`. Rewrite `b` using `[e2, ← a3]`. Rewrite using `[e1, ← a2]`. Conclude with `(comb_iff Z.m0.toSABMap h1 hv _ a1).2 ((comb_iff Z.m h2 hv _ a1).1 b)`. Set `T : Ix Dw → Kˣ` to `fun k => k.elim a fun k => t k.1 k.2`.

Establish `hb : FrBor T z y0` using `((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).2.2.2 T z y0).2 ⟨fun τ => Matrix.of (cf τ), fun τ i => hcf1 τ i, fun τ i j hij => hcf2 τ i j hij, hc.1, hcomb, hc.2.2⟩`. Use `⟨evR Xo c g y, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.FlagTan.evR_frBor hg hb, GlobalTheory.FlagTan.evR_frMap hg.1 hz, Fintype.prod_option, hex, zpow_zero, _root_.one_mul]`. Both sides reduce to the same expression.
-/
theorem evR_eq_of_tri {R K : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] [CommRing K] [IsLocalRing K]
    [Algebra c.F K] (ψ : R →ₐ[c.F] K) (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) {φ' : c.F →+* K} {x' : Sp K ⟶ Z.X} (f0 : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (hT : f.Tri ψ.toRingHom f0 t) (y0 : FrPt Xo c K)
    (hy : GlobalTheory.AllWt.ptF y0 = spMap ψ.toRingHom ≫ xF)
    (hu : ∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 ∧
        w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) :
    ∃ a : R, evR Xo c g y0 =
      ((∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k) : Kˣ) : K) * ψ a := by
  obtain ⟨y, w, hyx, hw⟩ := exists_frPt_of_eigFrame xF hs hx f
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap ψ y
  have h0 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = y0.x := pullback.lift_fst _ _ _
  have h1 : GlobalTheory.AllWt.ptF y0 ≫ pullback.fst _ _ = z.x := by rw [hz.1, hyx, hy, Category.assoc]
  have h2 : GlobalTheory.AllWt.ptF y0 ≫ Z.jQ ≫ pullback.fst _ _ = x' := by rw [hT.1, hy, ← hx, Category.assoc]
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c K z y0).1 (h0.symm.trans h1)
  choose cf hcf1 hcf2 hcf3 using hT.2.2
  have hcomb : ∀ τ i, IsCombAt z.x (z.u τ) (cf τ i) (y0.u τ i) := fun τ i => by
    obtain ⟨w0, a1, a2, a3⟩ := hu τ i
    have hv : ∀ k, (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.oF.t.G.hom =
        spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y0 := fun k => by
      rw [Category.assoc, (hw τ k).1, hy, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp,
        GlobalTheory.Frames.FramedBaseChange.dualMap_comp_alg]
    have e1 : z.u τ = fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m0.toSABMap.φ := funext fun k => by
      rw [hz.2.1, Category.assoc, (hw τ k).2.1]
    have e2 : (fun k => spMap (dualMap ψ.toRingHom) ≫ f.v τ k) =
        fun k => (spMap (dualMap ψ.toRingHom) ≫ w τ k) ≫ Z.m.φ := funext fun k => by
      rw [Category.assoc, (hw τ k).2.2]
    have b := hcf3 τ i
    rw [e2, ← a3] at b
    rw [e1, ← a2]
    exact (comb_iff Z.m0.toSABMap h1 hv _ a1).2 ((comb_iff Z.m h2 hv _ a1).1 b)
  let T : Ix Dw → Kˣ := fun k => k.elim a fun k => t k.1 k.2
  have hb : FrBor T z y0 := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).2.2.2 T z y0).2
    ⟨fun τ => Matrix.of (cf τ), fun τ i => hcf1 τ i, fun τ i j hij => hcf2 τ i j hij, hc.1, hcomb, hc.2.2⟩
  refine ⟨evR Xo c g y, ?_⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, GlobalTheory.FlagTan.evR_frMap hg.1 hz, Fintype.prod_option, hex, zpow_zero,
    _root_.one_mul]
  rfl

variable {F : Type} [Field F] {e : F ≃+* c.F}

/- English proof (translation)
Take `⟨φ, f, t, hT, ht⟩` from `C.gr_spec y`. Use `letI := (constF e C.Y).toAlgebra`. Use `letI := φ.toAlgebra`. Use `haveI := Z.jQ_open`. Set `ψ : C.Y.X.presheaf.stalk y →ₐ[c.F] C.Y.Fn` to `{ algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField with commutes' := fun r => (RingHom.congr_fun hT.2.1 r).symm }`.

Establish `hgen : spMap ψ.toRingHom ≫ stalkPt C.Y y = genericPt C.Y` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)`. Establish `hr : Set.range (stalkPt C.Y y ≫ C.π) ⊆ Set.range Z.jQ`. Introduce and unpack `_ ⟨p, rfl⟩`. Establish `h1 : stalkPt C.Y y p ⤳ y`. Establish `: stalkPt C.Y y p ∈ Set.range (C.Y.X.fromSpecStalk y)` using `⟨p, rfl⟩`.

Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Conclude with `(h1.map C.π.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range (not_not.1 hy)`. Set `xF` to `IsOpenImmersion.lift Z.jQ _ hr`. Establish `hxF : xF ≫ Z.jQ = stalkPt C.Y y ≫ C.π` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hpt : GlobalTheory.AllWt.ptF C.y0 = spMap ψ.toRingHom ≫ xF`.

Rewrite using `[← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, hgen]`. Conclude with `C.y0_x`. Establish `hs : xF ≫ pullback.snd _ _ = spMap φ`. Take `⟨φ₁, h⟩` from `Spec.map_surjective (xF ≫ pullback.snd _ _)`. Establish `h1 : spMap ψ.toRingHom ≫ spMap φ₁.hom = spMap (constF e C.Y)`.

Establish `h0 : GlobalTheory.AllWt.ptF C.y0 ≫ pullback.snd _ _ = spMap (constF e C.Y)` using `pullback.lift_snd _ _ _`. Rewrite using `[← h0, hpt, Category.assoc, ← h]`. Both sides reduce to the same expression. Rewrite `h1` using `[spMap_comp]`. Establish `h2 : ψ.toRingHom.comp φ₁.hom = constF e C.Y` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`.

Establish `h3 : φ₁.hom = φ` using `RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))`. Rewrite using `[← h, ← h3]`. Both sides reduce to the same expression. Take `⟨a, ha⟩` from `evR_eq_of_tri ψ xF hs (by rw [← Category.assoc, hxF, Category.assoc]) f C.f0 t hT C.y0 hpt hu hex hg`. Establish `hE : ∀ s : Finset (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∑ k ∈ s, ex (some k) • C.gr k.1 k.2).IsEqn y (∏ k ∈ s, t k.1 k.2 ^ ex (some k))` using `fun s => by classical`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using CartierDiv.isEqn_zero y`. Consider the case `insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk]`. Conclude with `((ht _ _).zsmul _).add ih`. Use `⟨_, (hE Finset.univ).neg, a, ?_⟩` and prove the remaining obligations.

Use `show ψ a = evR Xo c g C.y0 * _`. Rewrite using `[ha, mul_right_comm, Units.mul_inv, _root_.one_mul]`.
-/
theorem regularAt_of_lift (C : FlagCpt Z e)
    (hu : letI := (constF e C.Y).toAlgebra; ∀ τ i, ∃ w : Sp (DualNumber C.Y.Fn) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap C.Y.Fn (DualNumber C.Y.Fn)) ≫ GlobalTheory.AllWt.ptF C.y0 ∧
        w ≫ Z.m0.toSABMap.φ = C.y0.u τ i ∧ w ≫ Z.m.φ = C.f0.v τ i)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) (y : C.Y.X)
    (hy : C.π y ∉ genBd Z) : (C.LEx ex).RegularAt y (C.val g) := by
  obtain ⟨φ, f, t, hT, ht⟩ := C.gr_spec y
  letI := (constF e C.Y).toAlgebra
  letI := φ.toAlgebra
  haveI := Z.jQ_open
  let ψ : C.Y.X.presheaf.stalk y →ₐ[c.F] C.Y.Fn :=
    { algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField with
      commutes' := fun r => (RingHom.congr_fun hT.2.1 r).symm }
  have hgen : spMap ψ.toRingHom ≫ stalkPt C.Y y = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
  have hr : Set.range (stalkPt C.Y y ≫ C.π) ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have h1 : stalkPt C.Y y p ⤳ y := by
      have : stalkPt C.Y y p ∈ Set.range (C.Y.X.fromSpecStalk y) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact (h1.map C.π.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range (not_not.1 hy)
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = stalkPt C.Y y ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hpt : GlobalTheory.AllWt.ptF C.y0 = spMap ψ.toRingHom ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, hgen]
    exact C.y0_x
  have hs : xF ≫ pullback.snd _ _ = spMap φ := by
    obtain ⟨φ₁, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have h1 : spMap ψ.toRingHom ≫ spMap φ₁.hom = spMap (constF e C.Y) := by
      have h0 : GlobalTheory.AllWt.ptF C.y0 ≫ pullback.snd _ _ = spMap (constF e C.Y) := pullback.lift_snd _ _ _
      rw [← h0, hpt, Category.assoc, ← h]
      rfl
    rw [spMap_comp] at h1
    have h2 : ψ.toRingHom.comp φ₁.hom = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : φ₁.hom = φ := RingHom.ext fun r =>
      IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField
        ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hT.2.1 r))
    rw [← h, ← h3]
    rfl
  obtain ⟨a, ha⟩ := evR_eq_of_tri ψ xF hs (by rw [← Category.assoc, hxF, Category.assoc]) f C.f0 t hT C.y0 hpt hu hex hg
  have hE : ∀ s : Finset (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      (∑ k ∈ s, ex (some k) • C.gr k.1 k.2).IsEqn y (∏ k ∈ s, t k.1 k.2 ^ ex (some k)) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk]; exact ((ht _ _).zsmul _).add ih
  refine ⟨_, (hE Finset.univ).neg, a, ?_⟩
  show ψ a = evR Xo c g C.y0 * _
  rw [ha, mul_right_comm, Units.mul_inv, _root_.one_mul]

/- English proof (translation)
Establish `: IsPreimmersion (spMap (algebraMap A K))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors A)`. Use `infer_instance`.
-/
theorem mono_spMap_algebraMap (A K : Type) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Mono (spMap (algebraMap A K)) := by
  have : IsPreimmersion (spMap (algebraMap A K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  infer_instance

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C _ hex _ hf y hy` and use `regularAt_of_lift C C.flagComponentFramedPoint_frame hex hf y hy`.
-/
theorem regularAt_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (ex : Ix Dw → ℤ), ex none = 0 → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c ex, ∀ y : C.Y.X, C.π y ∉ genBd Z → (C.LEx ex).RegularAt y (C.val f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C _ hex _ hf y hy => regularAt_of_lift C C.flagComponentFramedPoint_frame hex hf y hy

end GlobalTheory.ShFam.OpenReg
