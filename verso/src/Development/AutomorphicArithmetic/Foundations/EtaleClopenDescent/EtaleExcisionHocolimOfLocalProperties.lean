import Mathlib
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

namespace UpperTheory.Cb

/- English proof (translation)
Apply the tactic sequence `apply pushout.hom_ext <;> simp [dbl.map] <;> rfl`.
-/
private theorem dbl_map_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  apply pushout.hom_ext <;> simp [dbl.map] <;> rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1`. Rewrite using `[dbl_map_id, pull_id]`.
-/
private theorem hs_pull_id (q : ℕ) (P : Arrow Spc) (n i : ℤ) (x : Hs q P n i) : Hs.pull q (𝟙 P) n i x = x := by
  apply Subtype.ext
  change pull _ (dbl.map (𝟙 P)) _ _ x.1 = x.1
  rw [dbl_map_id, pull_id]

/- English proof (translation)
Introduce `n i` and use `Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i, fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id], fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩`.
-/
private theorem exc_iso (q : ℕ) {P' P : Arrow Spc} (e : P' ≅ P) : Exc q e.hom := fun n i =>
  Function.bijective_iff_has_inverse.2 ⟨Hs.pull q e.inv n i,
    fun x => by rw [← hs_pull_comp, e.inv_hom_id, hs_pull_id],
    fun x => by rw [← hs_pull_comp, e.hom_inv_id, hs_pull_id]⟩

/- English proof (translation)
Establish `h` using `(IsPullback.of_hasPullback π (sch.map U.ι)).map ((evaluation _ _).obj n)`. Conclude with `IsPullback.of_forall_isPullback_app fun _ => h`.
-/
private theorem pb_app {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    IsPullback (P := disc.obj ((pullback π (sch.map U.ι)).obj n)) (X := disc.obj (E.obj n)) (Y := sch.obj U.toScheme) (Z := sch.obj X)
      (disc.map ((pullback.fst π (sch.map U.ι)).app n))
      (disc.map ((pullback.snd π (sch.map U.ι)).app n)) (disc.map (π.app n)) (sch.map U.ι) := by
  have h := (IsPullback.of_hasPullback π (sch.map U.ι)).map ((evaluation _ _).obj n)
  exact IsPullback.of_forall_isPullback_app fun _ => h

private def levIso {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) (n : SimplexCategoryᵒᵖ) :
    (lev n).obj (abv U π) ≅ abv U (E := disc.obj (E.obj n)) (disc.map (π.app n)) :=
  Arrow.isoMk (pb_app U π n).isoPullback (Iso.refl _)
    ((pb_app U π n).isoPullback_hom_fst.trans (Category.comp_id _).symm)

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
private theorem pbRel_fst {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.fst π g = pullback.fst π' g ≫ a := pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`.
-/
private theorem pbRel_snd {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pbRel g a π' π h ≫ pullback.snd π g = pullback.snd π' g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Apply `Arrow.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `pbRel _ a _ _ h1 ≫ pbRel _ b _ _ h2 = pbRel _ c _ _ h3 ≫ pbRel _ d _ _ h4`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pbRel_fst]`. Rewrite using `[← Category.assoc, pbRel_fst, ← Category.assoc, pbRel_fst, Category.assoc, Category.assoc, w]`.

Simplify using `only [Category.assoc, pbRel_snd]`. Conclude with `w`.
-/
private theorem abvRel_square {X : Scheme.{0}} (U : X.Opens) {A B C D : Spc} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (pA : A ⟶ sch.obj X) (pB : B ⟶ sch.obj X) (pC : C ⟶ sch.obj X) (pD : D ⟶ sch.obj X) (h1 : a ≫ pB = pA) (h2 : b ≫ pD = pB)
    (h3 : c ≫ pC = pA) (h4 : d ≫ pD = pC) (w : a ≫ b = c ≫ d) :
    abvRel U a pA pB h1 ≫ abvRel U b pB pD h2 = abvRel U c pA pC h3 ≫ abvRel U d pC pD h4 := by
  apply Arrow.hom_ext
  · change pbRel _ a _ _ h1 ≫ pbRel _ b _ _ h2 = pbRel _ c _ _ h3 ≫ pbRel _ d _ _ h4
    apply pullback.hom_ext
    · simp only [Category.assoc, pbRel_fst]
      rw [← Category.assoc, pbRel_fst, ← Category.assoc, pbRel_fst, Category.assoc, Category.assoc, w]
    · simp only [Category.assoc, pbRel_snd]
  · exact w

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, pbRel_fst, hp.isoPullback_hom_fst, ← Category.assoc _ (pullback.fst _ _), hp'.isoPullback_hom_fst, h1]`. Rewrite using `[Category.assoc, Category.assoc, pbRel_snd, hp.isoPullback_hom_snd, hp'.isoPullback_hom_snd, h2]`.
-/
private theorem iso_gen {B G E' E P' P : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π')
    (f' : P' ⟶ E') (s' : P' ⟶ G) (f : P ⟶ E) (s : P ⟶ G) (hp' : IsPullback f' s' π' g) (hp : IsPullback f s π g)
    (t : P' ⟶ P) (h1 : t ≫ f = f' ≫ a) (h2 : t ≫ s = s') :
    t ≫ hp.isoPullback.hom = hp'.isoPullback.hom ≫ pbRel g a π' π h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pbRel_fst, hp.isoPullback_hom_fst, ← Category.assoc _ (pullback.fst _ _),
      hp'.isoPullback_hom_fst, h1]
  · rw [Category.assoc, Category.assoc, pbRel_snd, hp.isoPullback_hom_snd, hp'.isoPullback_hom_snd, h2]

/- English proof (translation)
Establish `f1` using `pbRel_fst (sch.map U.ι) a π' π h`. Establish `f2` using `pbRel_snd (sch.map U.ι) a π' π h`. Apply `Arrow.hom_ext` to reduce the goal to its premises. Conclude with `iso_gen _ _ _ _ hn _ _ _ _ (pb_app U π' n) (pb_app U π n) (disc.map ((pbRel _ a _ _ h).app n)) ((disc.map_comp _ _).symm.trans ((congrArg (fun t => disc.map (NatTrans.app t n)) f1).trans (disc.map_comp _ _))) ((disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (NatTrans. …`. Both sides reduce to the same expression.
-/
private theorem lev_abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') (n : SimplexCategoryᵒᵖ) (hn) :
    (lev n).map (abvRel U a π' π h) ≫ (levIso U π n).hom =
      (levIso U π' n).hom ≫ abvRel U (E' := disc.obj (E'.obj n)) (E := disc.obj (E.obj n)) (disc.map (a.app n))
        (disc.map (π'.app n)) (disc.map (π.app n)) hn := by
  have f1 := pbRel_fst (sch.map U.ι) a π' π h
  have f2 := pbRel_snd (sch.map U.ι) a π' π h
  apply Arrow.hom_ext
  · exact iso_gen _ _ _ _ hn _ _ _ _ (pb_app U π' n) (pb_app U π n) (disc.map ((pbRel _ a _ _ h).app n))
      ((disc.map_comp _ _).symm.trans ((congrArg (fun t => disc.map (NatTrans.app t n)) f1).trans (disc.map_comp _ _)))
      ((disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (NatTrans.app t n)) f2))
  · rfl

section
variable {J : Type} [SmallCategory J]

/- English proof (translation)
Establish `e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _` using `σ.map_id _`. Use extensionality with `U x`. Express the relevant statement in the definitionally equal form `(c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))))).app U x) = _`. Rewrite using `[e]`. Simplify using the standard rewrite rules.
-/
private theorem inj_aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) (n : SimplexCategoryᵒᵖ)
    (σ : Fin (n.unop.len + 1) ⥤ J) : inj D n σ ≫ (aug c hc).app n = c (σ.obj 0) := by
  have e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := σ.map_id _
  ext U x
  change (c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))))).app U x) = _
  rw [e]
  simp

/- English proof (translation)
Use extensionality with `U x`. Establish `e : (fun i => (α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) = fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U ((α.app (σ.obj 0)).app U x)`. Use function extensionality and compare the values at `fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x`. Establish `hk : ∀ i k (g : i ⟶ k), (D.flip.obj U).map (σ.map g) ((α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) = (α.app (σ.obj k)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le k)))).app U x)` using `fun i k g => by`. Establish `a` using `congrFun e i`.

Establish `b` using `congrFun e k`. Simplify using `only at a b`. Rewrite using `[a, b]`. Conclude with `ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _`. Conclude with `mkChn_congr (F := D.flip.obj U) σ e hk (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _)`.
-/
private theorem inj_nat {D' D : J ⥤ PSh} (α : D' ⟶ D) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) :
    inj D' n σ ≫ ((hocF J).map α).app n = α.app (σ.obj 0) ≫ inj D n σ := by
  ext U x
  have e : (fun i => (α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U ((α.app (σ.obj 0)).app U x) :=
    funext fun i => ConcreteCategory.congr_hom (NatTrans.congr_app (α.naturality (σ.map (homOfLE (Fin.zero_le i)))) U) x
  have hk : ∀ i k (g : i ⟶ k), (D.flip.obj U).map (σ.map g) ((α.app (σ.obj i)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)) =
      (α.app (σ.obj k)).app U ((D'.map (σ.map (homOfLE (Fin.zero_le k)))).app U x) := fun i k g => by
    have a := congrFun e i
    have b := congrFun e k
    dsimp only at a b
    rw [a, b]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _
  exact mkChn_congr (F := D.flip.obj U) σ e hk
    (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) _)

end

/- English proof (translation)
Introduce `n i`. Use `(Function.Bijective.of_comp_iff' (B' n i) _).1 ?_` and prove the remaining obligations. Establish `T : Function.Bijective (Pi.map fun a => Hs.pull q (t a) n i)` using `Function.Bijective.piMap fun a => ht a n i`. Use `T.comp (B n i) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x a`.

Express the relevant statement in the definitionally equal form `Hs.pull q (r' a) n i (Hs.pull q f n i x) = Hs.pull q (t a) n i (Hs.pull q (r a) n i x)`. Rewrite using `[← hs_pull_comp, ← hs_pull_comp, w]`.
-/
private theorem sum_transfer (q : ℕ) {P' P : Arrow Spc} (f : P' ⟶ P) {A : Type} (Q' Q : A → Arrow Spc)
    (r' : ∀ a, Q' a ⟶ P') (r : ∀ a, Q a ⟶ P) (t : ∀ a, Q' a ⟶ Q a) (w : ∀ a, r' a ≫ f = t a ≫ r a) (ht : ∀ a, Exc q (t a))
    (B : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P n i) a => Hs.pull q (r a) n i x)
    (B' : ∀ n i : ℤ, Function.Bijective fun (x : Hs q P' n i) a => Hs.pull q (r' a) n i x) : Exc q f := by
  intro n i
  refine (Function.Bijective.of_comp_iff' (B' n i) _).1 ?_
  have T : Function.Bijective (Pi.map fun a => Hs.pull q (t a) n i) := Function.Bijective.piMap fun a => ht a n i
  convert T.comp (B n i) using 1
  funext x a
  change Hs.pull q (r' a) n i (Hs.pull q f n i x) = Hs.pull q (t a) n i (Hs.pull q (r a) n i x)
  rw [← hs_pull_comp, ← hs_pull_comp, w]

/- English proof (translation)
Take `⟨cD⟩` from `hL J D n`. Take `⟨cD'⟩` from `hL J D' n`. Establish `hp : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D n σ) ≫ disc.map π = disc.map (c (σ.obj 0))` using `fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e ▸ inj_aug c hc n σ))`. Establish `hp' : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D' n σ) ≫ disc.map π' = disc.map (c' (σ.obj 0))` using `fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e' ▸ inj_aug c' hc' n σ))`. Use `sum_transfer q _ (fun σ : Fin (n.unop.len + 1) ⥤ J => abv U (E := disc.obj (D'.obj (σ.obj 0))) (disc.map (c' (σ.obj 0)))) (fun σ => abv U (E := disc.obj (D.obj (σ.obj 0))) (disc.map (c (σ.obj 0)))) (fun σ => abvRel U (disc.map (inj D' n σ)) _ _ (hp' σ)) (fun σ => abvRel U (disc.m …` and prove the remaining obligations.

Conclude with `abvRel_square U _ _ _ _ _ _ _ _ _ _ _ _ ((disc.map_comp _ _).symm.trans ((congrArg disc.map (inj_nat α n σ)).trans (disc.map_comp _ _)))`. Conclude with `fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) (Cofan.mk _ (inj D n)) ⟨cD⟩ π (fun σ => c (σ.obj 0)) hp m i`. Conclude with `fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D'.obj (σ.obj 0)) (Cofan.mk _ (inj D' n)) ⟨cD'⟩ π' (fun σ => c' (σ.obj 0)) hp' m i`.
-/
private theorem exc_lvl (hL : LeafLevel) (hS : LeafHsSum) (q : ℕ) {J : Type} [SmallCategory J] {D' D : J ⥤ PSh} (α : D' ⟶ D)
    {X : Scheme.{0}} (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc' : Coc D' c') (hc : Coc D c) (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j))
    (ht : ∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)))
    (n : SimplexCategoryᵒᵖ) (π' : (hoc D').obj n ⟶ yoneda.obj X) (π : (hoc D).obj n ⟶ yoneda.obj X)
    (e' : π' = (aug c' hc').app n) (e : π = (aug c hc).app n) (hn) :
    Exc q (abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n)) (disc.map (((hocF J).map α).app n))
      (disc.map π') (disc.map π) hn) := by
  obtain ⟨cD⟩ := hL J D n
  obtain ⟨cD'⟩ := hL J D' n
  have hp : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D n σ) ≫ disc.map π = disc.map (c (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e ▸ inj_aug c hc n σ))
  have hp' : ∀ σ : Fin (n.unop.len + 1) ⥤ J, disc.map (inj D' n σ) ≫ disc.map π' = disc.map (c' (σ.obj 0)) :=
    fun σ => (disc.map_comp _ _).symm.trans (congrArg disc.map (e' ▸ inj_aug c' hc' n σ))
  refine sum_transfer q _ (fun σ : Fin (n.unop.len + 1) ⥤ J => abv U (E := disc.obj (D'.obj (σ.obj 0))) (disc.map (c' (σ.obj 0))))
    (fun σ => abv U (E := disc.obj (D.obj (σ.obj 0))) (disc.map (c (σ.obj 0))))
    (fun σ => abvRel U (disc.map (inj D' n σ)) _ _ (hp' σ)) (fun σ => abvRel U (disc.map (inj D n σ)) _ _ (hp σ))
    (fun σ => abvRel U (disc.map (α.app (σ.obj 0))) _ _ (h _)) (fun σ => ?_) (fun σ => ht _) ?_ ?_
  · exact abvRel_square U _ _ _ _ _ _ _ _ _ _ _ _
      ((disc.map_comp _ _).symm.trans ((congrArg disc.map (inj_nat α n σ)).trans (disc.map_comp _ _)))
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) (Cofan.mk _ (inj D n)) ⟨cD⟩
      π (fun σ => c (σ.obj 0)) hp m i
  · exact fun m i => hS q X U _ (fun σ : Fin (n.unop.len + 1) ⥤ J => D'.obj (σ.obj 0)) (Cofan.mk _ (inj D' n)) ⟨cD'⟩
      π' (fun σ => c' (σ.obj 0)) hp' m i

/- English proof (translation)
Introduce `hE hL hS _ _ _ _ _ a3 q J _ D' D α X U c' c hc' hc h h' ht`. Use `hE a3 q _ _ _ fun n => ?_` and prove the remaining obligations. Establish `hn : disc.map (((hocF J).map α).app n) ≫ disc.map ((aug c hc).app n) = disc.map ((aug c' hc').app n)` using `(disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (t.app n)) h')`. Establish `e` using `lev_abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h' n hn`. Establish `k` using `exc_lvl hL hS q α U c' c hc' hc h ht n _ _ rfl rfl hn`.

Establish `e' : (lev n).map (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h') = (levIso U (aug c' hc') n).hom ≫ abvRel U (E'` using `disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n)) (disc.map (((hocF J).map α).app n)) (disc.map ((aug c' hc').app n)) (disc.map ((aug c hc).app n)) hn ≫ (levIso U (aug c hc) n).inv := by`. Rewrite using `[← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[e']`. Conclude with `exc_comp q (exc_iso q _) (exc_comp q k (exc_iso q (levIso U (aug c hc) n).symm))`.
-/
theorem etale_excision_hocolim_of_local_properties :
    LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafLevel → LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum → LateralTheory.CohomologicalPurity.LeafAW → LateralTheory.CohomologicalPurity.LeafBd → LateralTheory.CohomologicalPurity.LeafExc → LateralTheory.CohomologicalPurity.LeafHens → LateralTheory.CohomologicalPurity.LeafIndExc → LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by
  intro hE hL hS _ _ _ _ _ a3 q J _ D' D α X U c' c hc' hc h h' ht
  refine hE a3 q _ _ _ fun n => ?_
  have hn : disc.map (((hocF J).map α).app n) ≫ disc.map ((aug c hc).app n) = disc.map ((aug c' hc').app n) :=
    (disc.map_comp _ _).symm.trans (congrArg (fun t => disc.map (t.app n)) h')
  have e := lev_abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h' n hn
  have k := exc_lvl hL hS q α U c' c hc' hc h ht n _ _ rfl rfl hn
  have e' : (lev n).map (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h') =
      (levIso U (aug c' hc') n).hom ≫ abvRel U (E' := disc.obj ((hoc D').obj n)) (E := disc.obj ((hoc D).obj n))
        (disc.map (((hocF J).map α).app n)) (disc.map ((aug c' hc').app n)) (disc.map ((aug c hc).app n)) hn ≫
        (levIso U (aug c hc) n).inv := by
    rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e']
  exact exc_comp q (exc_iso q _) (exc_comp q k (exc_iso q (levIso U (aug c hc) n).symm))

end UpperTheory.Cb
