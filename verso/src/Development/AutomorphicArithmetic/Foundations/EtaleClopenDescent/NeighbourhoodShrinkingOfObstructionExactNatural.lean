import Mathlib
import Development.EtaleCohomology.EtaleSheaves.GeoProof

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.MorphismProjectionLaws
open LateralTheory.E.E4 LateralTheory.E.EtaleTopologySheaves LateralTheory.E.SecondDegreeKilling LateralTheory.E.Bridge_yfiPf

variable {B W Y S T T' T'' : Scheme.{0}}

private def mY (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    pullback p u ⟶ pullback p u' :=
  pullback.map p u p u' (𝟙 Y) f (𝟙 B) (by simp) (by simp [h])

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
private lemma mY_snd (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mY p u u' f h ≫ pullback.snd p u' = pullback.snd p u ≫ f :=
  pullback.lift_snd _ _ _

/- English proof (translation)
Unfold `mY pullback.map`. Use `erw [pullback.lift_fst]`. Conclude with `Category.comp_id _`.
-/
private lemma mY_fst (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mY p u u' f h ≫ pullback.fst p u' = pullback.fst p u := by
  unfold mY pullback.map
  erw [pullback.lift_fst]
  exact Category.comp_id _

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, mY_fst, mY_fst, mY_fst]`. Rewrite using `[Category.assoc, mY_snd, reassoc_of% mY_snd, mY_snd, e]`.
-/
private lemma mY_comp (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (u'' : T'' ⟶ B) (f : T ⟶ T') (g : T' ⟶ T'')
    (k : T ⟶ T'') (h : f ≫ u' = u) (h' : g ≫ u'' = u') (hk : k ≫ u'' = u) (e : f ≫ g = k) :
    mY p u u' f h ≫ mY p u' u'' g h' = mY p u u'' k hk := by
  apply pullback.hom_ext
  · rw [Category.assoc, mY_fst, mY_fst, mY_fst]
  · rw [Category.assoc, mY_snd, reassoc_of% mY_snd, mY_snd, e]

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[mY_fst, Category.id_comp]`. Rewrite using `[mY_snd, Category.comp_id, Category.id_comp]`.
-/
private lemma mY_id (p : Y ⟶ B) (u : T ⟶ B) (h : 𝟙 T ≫ u = u) : mY p u u (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mY_fst, Category.id_comp]
  · rw [mY_snd, Category.comp_id, Category.id_comp]

private def mW (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    pullback (pullback.snd p u ≫ u) ι ⟶ pullback (pullback.snd p u' ≫ u') ι :=
  pullback.map _ _ _ _ (mY p u u' f h) (𝟙 W) (𝟙 B)
    (by rw [Category.comp_id, reassoc_of% (mY_snd p u u' f h), h]) (by simp)

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
private lemma mW_fst (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mW p ι u u' f h ≫ pullback.fst _ ι = pullback.fst _ ι ≫ mY p u u' f h :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`.
-/
private lemma mW_snd (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mW p ι u u' f h ≫ pullback.snd _ ι = pullback.snd _ ι :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, mW_fst, reassoc_of% mW_fst]`. Rewrite using `[mY_comp p u u' u'' f g k h h' hk e]`. Simplify using `only [Category.assoc, mW_snd]`.
-/
private lemma mW_comp (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (u'' : T'' ⟶ B) (f : T ⟶ T')
    (g : T' ⟶ T'') (k : T ⟶ T'') (h : f ≫ u' = u) (h' : g ≫ u'' = u') (hk : k ≫ u'' = u) (e : f ≫ g = k) :
    mW p ι u u' f h ≫ mW p ι u' u'' g h' = mW p ι u u'' k hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mW_fst, reassoc_of% mW_fst]
    rw [mY_comp p u u' u'' f g k h h' hk e]
  · simp only [Category.assoc, mW_snd]

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[mW_fst, mY_id, Category.id_comp, Category.comp_id]`. Rewrite using `[mW_snd, Category.id_comp]`.
-/
private lemma mW_id (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (h : 𝟙 T ≫ u = u) : mW p ι u u (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mW_fst, mY_id, Category.id_comp, Category.comp_id]
  · rw [mW_snd, Category.id_comp]

/- English proof (translation)
Simplify using `using a.w`.
-/
private lemma a_w {U U' : B.Etale} (a : U' ⟶ U) : a.left ≫ U.hom = U'.hom := by
  simpa using a.w

/- English proof (translation)
Establish `hY : ∀ {V V' : B.Etale} (c : V' ⟶ V), resY p c = mY p _ _ c.left (a_w c)` using `fun _ => rfl`. Rewrite using `[hY (b ≫ a), hY b, hY a]`. Conclude with `(mY_comp p _ _ _ _ _ _ _ _ _ rfl).symm`.
-/
private lemma resY_comp (p : Y ⟶ B) {U U' U'' : B.Etale} (b : U'' ⟶ U') (a : U' ⟶ U) :
    resY p (b ≫ a) = resY p b ≫ resY p a := by
  have hY : ∀ {V V' : B.Etale} (c : V' ⟶ V), resY p c = mY p _ _ c.left (a_w c) := fun _ => rfl
  rw [hY (b ≫ a), hY b, hY a]
  exact (mY_comp p _ _ _ _ _ _ _ _ _ rfl).symm

/- English proof (translation)
Establish `hW : ∀ {V V' : B.Etale} (c : V' ⟶ V), resYW p ι c = mW p ι _ _ c.left (a_w c)` using `fun _ => rfl`. Rewrite using `[hW (b ≫ a), hW b, hW a]`. Conclude with `(mW_comp p ι _ _ _ _ _ _ _ _ _ rfl).symm`.
-/
private lemma resYW_comp (p : Y ⟶ B) (ι : W ⟶ B) {U U' U'' : B.Etale} (b : U'' ⟶ U') (a : U' ⟶ U) :
    resYW p ι (b ≫ a) = resYW p ι b ≫ resYW p ι a := by
  have hW : ∀ {V V' : B.Etale} (c : V' ⟶ V), resYW p ι c = mW p ι _ _ c.left (a_w c) := fun _ => rfl
  rw [hW (b ≫ a), hW b, hW a]
  exact (mW_comp p ι _ _ _ _ _ _ _ _ _ rfl).symm

/- English proof (translation)
Establish `hY : resY p a = mY p _ _ a.left (a_w a)` using `rfl`. Establish `hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tY p V s = mY p _ _ s rfl` using `fun _ => rfl`. Establish `h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom` using `by rw [Category.assoc, a_w]`. Rewrite using `[hY, hT, hT, mY_comp p _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl, mY_comp p _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]`.
-/
private lemma tY_res (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (t : S ⟶ U'.left)
    (h : 𝟙 S ≫ t ≫ U'.hom = (t ≫ a.left) ≫ U.hom) :
    mY p _ _ (𝟙 S) h ≫ tY p U' t ≫ resY p a = tY p U (t ≫ a.left) := by
  have hY : resY p a = mY p _ _ a.left (a_w a) := rfl
  have hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tY p V s = mY p _ _ s rfl := fun _ => rfl
  have h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom := by rw [Category.assoc, a_w]
  rw [hY, hT, hT, mY_comp p _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl,
    mY_comp p _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]

/- English proof (translation)
Establish `hW : resYW p ι a = mW p ι _ _ a.left (a_w a)` using `rfl`. Establish `hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tW p ι V s = mW p ι _ _ s rfl` using `fun _ => rfl`. Establish `h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom` using `by rw [Category.assoc, a_w]`. Rewrite using `[hW, hT, hT, mW_comp p ι _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl, mW_comp p ι _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]`.
-/
private lemma tW_res (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (t : S ⟶ U'.left)
    (h : 𝟙 S ≫ t ≫ U'.hom = (t ≫ a.left) ≫ U.hom) :
    mW p ι _ _ (𝟙 S) h ≫ tW p ι U' t ≫ resYW p ι a = tW p ι U (t ≫ a.left) := by
  have hW : resYW p ι a = mW p ι _ _ a.left (a_w a) := rfl
  have hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tW p ι V s = mW p ι _ _ s rfl := fun _ => rfl
  have h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom := by rw [Category.assoc, a_w]
  rw [hW, hT, hT, mW_comp p ι _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl,
    mW_comp p ι _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]

/- English proof (translation)
Rewrite using `[← pull_comp, ← sch.map_comp, h, sch.map_id, pull_id]`.
-/
private lemma pull_left (q : ℕ) (i n : ℤ) {X Z : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ X) (h : f ≫ g = 𝟙 X)
    (y : Ht q (sch.obj X) n i) :
    pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y) = y := by
  rw [← pull_comp, ← sch.map_comp, h, sch.map_id, pull_id]

/- English proof (translation)
Rewrite using `[← pull_left q i n g f h y, hy, map_zero]`.
-/
private lemma pull_zero (q : ℕ) (i n : ℤ) {X Z : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ X) (h : g ≫ f = 𝟙 Z)
    (y : Ht q (sch.obj Z) n i) (hy : pull (ZMod q) (sch.map f) (tw q i) n y = 0) : y = 0 := by
  rw [← pull_left q i n g f h y, hy, map_zero]

/- English proof (translation)
Establish `hu : 𝟙 _ ≫ S.t ≫ U'.hom = (S.t ≫ a.left) ≫ U.hom`. Rewrite using `[Category.id_comp, Category.assoc, a_w]`. Establish `hu' : 𝟙 _ ≫ (S.t ≫ a.left) ≫ U.hom = S.t ≫ U'.hom`. Rewrite using `[Category.id_comp, Category.assoc, a_w]`. Establish `eY1 : mY p _ _ (𝟙 _) hu ≫ mY p _ _ (𝟙 _) hu' = 𝟙 _`.

Rewrite using `[mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]`. Establish `eY2 : mY p _ _ (𝟙 _) hu' ≫ mY p _ _ (𝟙 _) hu = 𝟙 _`. Rewrite using `[mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]`. Establish `eW1 : mW p ι _ _ (𝟙 _) hu ≫ mW p ι _ _ (𝟙 _) hu' = 𝟙 _`. Rewrite using `[mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]`.

Establish `eW2 : mW p ι _ _ (𝟙 _) hu' ≫ mW p ι _ _ (𝟙 _) hu = 𝟙 _`. Rewrite using `[mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]`. Establish `pc : ∀ {X1 X2 X3 : Scheme.{0}} (f : X1 ⟶ X2) (g : X2 ⟶ X3) (n : ℤ) (y : Ht q (sch.obj X3) n i), pull (ZMod q) (sch.map (f ≫ g)) (tw q i) n y = pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y)`. Introduce `X1 X2 X3 f g n y`. Rewrite using `[CategoryTheory.Functor.map_comp, pull_comp]`.

Use `letI := S.cat`. Use `letI := S.ring`. Use `haveI := S.filt`. Use `⟨Sys.mk S.J S.V (fun j => S.a j ≫ a) ?_ S.tr S.tr_id S.tr_comp ?_ S.A S.sh (S.t ≫ a.left) (fun j => mY p _ _ (𝟙 _) hu ≫ S.gY j) (fun j => mW p ι _ _ (𝟙 _) hu ≫ S.gW j) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩` and prove the remaining obligations. Introduce `j`.

Take `⟨v, hv⟩` from `S.mem j`. Conclude with `⟨v, congrArg (fun z => a.left z) hv⟩`. Introduce `j k f`. Rewrite using `[← Category.assoc, S.tr_a]`. Introduce `j show pullback.fst _ ι ≫ mY p _ _ (𝟙 _) hu ≫ S.gY j = (mW p ι _ _ (𝟙 _) hu ≫ S.gW j) ≫ _`.

Rewrite using `[← reassoc_of% (mW_fst p ι _ _ (𝟙 _) hu)]`. Conclude with `(congrArg (fun z => mW p ι _ _ (𝟙 _) hu ≫ z) (S.sq j)).trans (Category.assoc _ _ _).symm`. Introduce `j`. Rewrite using `[resY_comp]`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[reassoc_of% (S.gY_a j)]`. Conclude with `tY_res p a S.t hu`. Introduce `j`. Rewrite using `[resYW_comp]`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[reassoc_of% (S.gW_a j)]`. Conclude with `tW_res p ι a S.t hu`. Introduce `j k f`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[S.gY_tr]`.

Introduce `j k f`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[S.gW_tr]`. Introduce `j y hy`. Apply `S.injY j y` to reduce the goal to its premises.

Conclude with `pull_zero q i m (mY p _ _ (𝟙 _) hu) (mY p _ _ (𝟙 _) hu') eY2 _ (by rw [← pc]; exact hy)`. Introduce `y`. Take `⟨j, y', hy'⟩` from `S.surY (pull (ZMod q) (sch.map (mY p _ _ (𝟙 _) hu')) (tw q i) (m - 1) y)`. Use `⟨j, y', ?_⟩` and prove the remaining obligations. Rewrite using `[pc, hy', pull_left q i (m - 1) _ _ eY1 y]`.

Introduce `j w hw`. Apply `S.injW j w` to reduce the goal to its premises. Conclude with `pull_zero q i (m - 1) (mW p ι _ _ (𝟙 _) hu) (mW p ι _ _ (𝟙 _) hu') eW2 _ (by rw [← pc]; exact hw)`.
-/
private lemma shrink (q : ℕ) (i : ℤ) (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale) (a : U' ⟶ U) (m : ℤ)
    (u' : U'.left) (S : Sys q i p ι U' m u') : Nonempty (Sys q i p ι U m (a.left u')) := by
  have hu : 𝟙 _ ≫ S.t ≫ U'.hom = (S.t ≫ a.left) ≫ U.hom := by
    rw [Category.id_comp, Category.assoc, a_w]
  have hu' : 𝟙 _ ≫ (S.t ≫ a.left) ≫ U.hom = S.t ≫ U'.hom := by
    rw [Category.id_comp, Category.assoc, a_w]
  have eY1 : mY p _ _ (𝟙 _) hu ≫ mY p _ _ (𝟙 _) hu' = 𝟙 _ := by
    rw [mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]
  have eY2 : mY p _ _ (𝟙 _) hu' ≫ mY p _ _ (𝟙 _) hu = 𝟙 _ := by
    rw [mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]
  have eW1 : mW p ι _ _ (𝟙 _) hu ≫ mW p ι _ _ (𝟙 _) hu' = 𝟙 _ := by
    rw [mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]
  have eW2 : mW p ι _ _ (𝟙 _) hu' ≫ mW p ι _ _ (𝟙 _) hu = 𝟙 _ := by
    rw [mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]
  have pc : ∀ {X1 X2 X3 : Scheme.{0}} (f : X1 ⟶ X2) (g : X2 ⟶ X3) (n : ℤ) (y : Ht q (sch.obj X3) n i),
      pull (ZMod q) (sch.map (f ≫ g)) (tw q i) n y =
        pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y) := by
    intro X1 X2 X3 f g n y
    rw [CategoryTheory.Functor.map_comp, pull_comp]
  letI := S.cat
  letI := S.ring
  haveI := S.filt
  refine ⟨Sys.mk S.J S.V (fun j => S.a j ≫ a) ?_ S.tr S.tr_id S.tr_comp ?_ S.A S.sh
    (S.t ≫ a.left) (fun j => mY p _ _ (𝟙 _) hu ≫ S.gY j) (fun j => mW p ι _ _ (𝟙 _) hu ≫ S.gW j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro j
    obtain ⟨v, hv⟩ := S.mem j
    exact ⟨v, congrArg (fun z => a.left z) hv⟩
  · intro j k f
    rw [← Category.assoc, S.tr_a]
  · intro j
    show pullback.fst _ ι ≫ mY p _ _ (𝟙 _) hu ≫ S.gY j = (mW p ι _ _ (𝟙 _) hu ≫ S.gW j) ≫ _
    rw [← reassoc_of% (mW_fst p ι _ _ (𝟙 _) hu)]
    exact (congrArg (fun z => mW p ι _ _ (𝟙 _) hu ≫ z) (S.sq j)).trans (Category.assoc _ _ _).symm
  · intro j
    rw [resY_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [reassoc_of% (S.gY_a j)]
    exact tY_res p a S.t hu
  · intro j
    rw [resYW_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [reassoc_of% (S.gW_a j)]
    exact tW_res p ι a S.t hu
  · intro j k f
    refine (Category.assoc _ _ _).trans ?_
    rw [S.gY_tr]
  · intro j k f
    refine (Category.assoc _ _ _).trans ?_
    rw [S.gW_tr]
  · intro j y hy
    apply S.injY j y
    exact pull_zero q i m (mY p _ _ (𝟙 _) hu) (mY p _ _ (𝟙 _) hu') eY2 _ (by rw [← pc]; exact hy)
  · intro y
    obtain ⟨j, y', hy'⟩ := S.surY (pull (ZMod q) (sch.map (mY p _ _ (𝟙 _) hu')) (tw q i) (m - 1) y)
    refine ⟨j, y', ?_⟩
    rw [pc, hy', pull_left q i (m - 1) _ _ eY1 y]
  · intro j w hw
    apply S.injW j w
    exact pull_zero q i (m - 1) (mW p ι _ _ (𝟙 _) hu) (mW p ι _ _ (𝟙 _) hu') eW2 _
      (by rw [← pc]; exact hw)

end UpperTheory.Cb.MorphismProjectionLaws

/- English proof (translation)
Introduce `_ _ q _ i B W Y p ι U U' a m u' S`. Conclude with `UpperTheory.Cb.MorphismProjectionLaws.shrink q i p ι U U' a m u' S`.
-/
theorem UpperTheory.Cb.neighbourhoodShrinking_of_obstructionExact_natural :
    LateralTheory.E.NeighbourhoodKilling.ObsExact → LateralTheory.E.NeighbourhoodKilling.ObsNat → LateralTheory.E.GeoProof.Shrink := by
  intro _ _ q _ i B W Y p ι U U' a m u' S
  exact UpperTheory.Cb.MorphismProjectionLaws.shrink q i p ι U U' a m u' S
