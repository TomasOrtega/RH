import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.MVnatPf

open LateralTheory.KummerTheory.ContCut

/- English proof (translation)
Use `show _ = (F.obj.map (g₁ ≫ g₂).op).hom x`. Rewrite using `[op_comp, Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {R : Type} [CommRing R] {F : Shv R} {A B C : Scheme.{0}} (g₁ : A ⟶ B) (g₂ : B ⟶ C) (x : Sec F C) :
    Sec.res g₁ (Sec.res g₂ x) = Sec.res (g₁ ≫ g₂) x := by
  show _ = (F.obj.map (g₁ ≫ g₂).op).hom x
  rw [op_comp, Functor.map_comp]
  rfl

/- English proof (translation)
Use `show ((F.obj.map g.op) ≫ φ.hom.app (op A)).hom x = (φ.hom.app (op B) ≫ G.obj.map g.op).hom x`. Rewrite using `[φ.hom.naturality]`.
-/
theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {A B : Scheme.{0}} (g : A ⟶ B) (x : Sec F B) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show ((F.obj.map g.op) ≫ φ.hom.app (op A)).hom x = (φ.hom.app (op B) ≫ G.obj.map g.op).hom x
  rw [φ.hom.naturality]

/- English proof (translation)
Take `⟨s, z, hs, hz, e1, e2⟩` from `h`. Use `⟨Sec.res hu s, Sec.res hx z, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(hD R (res R F) W n).2.2.2.2 hw w _ hs` as an intermediate fact. Rewrite using `[res_res, ea, ← res_res]`. Conclude with `this`.

Conclude with `(hD R (res R F) X (n + 1)).2.2.2.2 hx x _ hz`. Rewrite using `[res_res, ef, ← res_res, e1, map_res]`. Rewrite using `[res_res, eg, ← res_res, e2]`. Conclude with `map_zero _`.
-/
theorem conn_pull (hD : Dict) {R : Type} [CommRing R] (F : Shv R) {W U V X W' U' V' X' : Scheme.{0}}
    (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (a' : W' ⟶ U') (f' : U' ⟶ X') (g' : V' ⟶ X')
    (hw : W' ⟶ W) (hu : U' ⟶ U) (hv : V' ⟶ V) (hx : X' ⟶ X)
    (ea : a' ≫ hu = hw ≫ a) (ef : f' ≫ hx = hu ≫ f) (eg : g' ≫ hx = hv ≫ g) (n : ℤ) w x
    (h : Conn F a f g n w x) :
    Conn F a' f' g' n (pull R (sch.map hw) F n w) (pull R (sch.map hx) F (n + 1) x) := by
  obtain ⟨s, z, hs, hz, e1, e2⟩ := h
  refine ⟨Sec.res hu s, Sec.res hx z, ?_, ?_, ?_, ?_⟩
  · have := (hD R (res R F) W n).2.2.2.2 hw w _ hs
    rw [res_res, ea, ← res_res]
    exact this
  · exact (hD R (res R F) X (n + 1)).2.2.2.2 hx x _ hz
  · rw [res_res, ef, ← res_res, e1, map_res]
  · rw [res_res, eg, ← res_res, e2]
    exact map_zero _

/- English proof (translation)
Use `congrArg Quiver.Hom.unop (φ.naturality h)` as an intermediate fact. Rewrite `this` using `[unop_comp, unop_comp]`. Conclude with `this`.
-/
theorem unop_nat {K : Type 1} [Category.{0} K] {A B : K ⥤ Scheme.{0}ᵒᵖ} (φ : A ⟶ B) {k k' : K} (h : k ⟶ k') :
    (φ.app k').unop ≫ (A.map h).unop = (B.map h).unop ≫ (φ.app k).unop := by
  have := congrArg Quiver.Hom.unop (φ.naturality h)
  rw [unop_comp, unop_comp] at this
  exact this

/- English proof (translation)
Introduce `R _ F K _ X U V W f g a b hM`. Establish `dk : ∀ (n : ℤ) (k : K), ∃ δ : H R (sch.obj (W.obj k).unop) F n →+ H R (sch.obj (X.obj k).unop) F (n + 1), ∀ w x, Conn F (a.app k).unop (f.app k).unop (g.app k).unop n w x ↔ δ w = x` using `fun n k => hΔ R F _ _ _ _ (hM k) n`. Use `choose δ hδ using dk`. Use `⟨{ f := fun n => Functor.whiskerRight f (Hf F n) g := fun n => Functor.whiskerRight g (Hf F n) a := fun n => Functor.whiskerRight a (Hf F n) b := fun n => Functor.whiskerRight b (Hf F n) δ := fun n => { app := fun k => AddCommGrpCat.ofHom (δ n k) naturality := fun k k' h => by` and prove the remaining obligations. Apply `AddCommGrpCat.hom_ext` to reduce the goal to its premises.

Use extensionality with `w`. Use `show δ n k' (pull R (sch.map (W.map h).unop) F n w) = pull R (sch.map (X.map h).unop) F (n + 1) (δ n k w)`. Conclude with `(hδ n k' _ _).1 (conn_pull hD F _ _ _ _ _ _ _ _ _ _ (unop_nat a h) (unop_nat f h) (unop_nat g h) n _ _ ((hδ n k _ _).2 rfl)) }`. Use `comm := fun n => by`. Use extensionality with `k : 2`.

Simplify using `only [NatTrans.comp_app, Functor.whiskerRight_app]`. Rewrite using `[← Functor.map_comp, ← Functor.map_comp]`. Use `congr 1`. Apply `Quiver.Hom.unop_inj` to reduce the goal to its premises. Rewrite using `[unop_comp, unop_comp]`.

Conclude with `(hM k).2.2.1.w`. Use `exUV := fun n k u v h => (hE R F _ _ _ _ (hM k) n).1 u v h`. Use `exX := fun n k x h1 h2 => by`. Take `⟨w, hw⟩` from `(hE R F _ _ _ _ (hM k) n).2.1 x h1 h2`. Conclude with `⟨w, (hδ n k w x).1 hw⟩`.

Use `exW := fun n k w => (hδ n k w 0).symm.trans ((hE R F _ _ _ _ (hM k) n).2.2 w) }⟩`.
-/
theorem MVnat_of (hD : Dict) (hΔ : Delta) (hE : Exact) : MVnat := by
  intro R _ F K _ X U V W f g a b hM
  have dk : ∀ (n : ℤ) (k : K), ∃ δ : H R (sch.obj (W.obj k).unop) F n →+ H R (sch.obj (X.obj k).unop) F (n + 1),
      ∀ w x, Conn F (a.app k).unop (f.app k).unop (g.app k).unop n w x ↔ δ w = x :=
    fun n k => hΔ R F _ _ _ _ (hM k) n
  choose δ hδ using dk
  refine ⟨{
    f := fun n => Functor.whiskerRight f (Hf F n)
    g := fun n => Functor.whiskerRight g (Hf F n)
    a := fun n => Functor.whiskerRight a (Hf F n)
    b := fun n => Functor.whiskerRight b (Hf F n)
    δ := fun n =>
      { app := fun k => AddCommGrpCat.ofHom (δ n k)
        naturality := fun k k' h => by
          apply AddCommGrpCat.hom_ext
          ext w
          show δ n k' (pull R (sch.map (W.map h).unop) F n w) = pull R (sch.map (X.map h).unop) F (n + 1) (δ n k w)
          exact (hδ n k' _ _).1 (conn_pull hD F _ _ _ _ _ _ _ _ _ _ (unop_nat a h) (unop_nat f h) (unop_nat g h) n _ _
            ((hδ n k _ _).2 rfl)) }
    comm := fun n => by
      ext k : 2
      simp only [NatTrans.comp_app, Functor.whiskerRight_app]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      rw [unop_comp, unop_comp]
      exact (hM k).2.2.1.w
    exUV := fun n k u v h => (hE R F _ _ _ _ (hM k) n).1 u v h
    exX := fun n k x h1 h2 => by
      obtain ⟨w, hw⟩ := (hE R F _ _ _ _ (hM k) n).2.1 x h1 h2
      exact ⟨w, (hδ n k w x).1 hw⟩
    exW := fun n k w => (hδ n k w 0).symm.trans ((hE R F _ _ _ _ (hM k) n).2.2 w) }⟩

end LateralTheory.KummerTheory.MVnatPf

end
