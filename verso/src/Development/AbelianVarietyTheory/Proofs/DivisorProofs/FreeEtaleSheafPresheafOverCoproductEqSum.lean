import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeCofan

/- English proof (translation)
Set `e : ∐ V ≅ U` to `(colimit.isColimit (Discrete.functor V)).coconePointUniqueUpToIso hc`. Establish `he : ∀ i, Sigma.ι V i ≫ e.hom = j i` using `fun i => (colimit.isColimit (Discrete.functor V)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩`. Establish `hinv : ∀ u : U, e.hom (e.inv u) = u` using `fun u => by`. Rewrite using `[← Scheme.Hom.comp_apply, e.inv_hom_id]`. Both sides reduce to the same expression.

Establish `hinv' : ∀ z : (∐ V : Scheme.{0}), e.inv (e.hom z) = z` using `fun z => by`. Rewrite using `[← Scheme.Hom.comp_apply, e.hom_inv_id]`. Both sides reduce to the same expression. Use `⟨fun i => ?_, fun u => ?_, fun i k v w h => ?_⟩` and prove the remaining obligations. Rewrite using `[← he i]`.

Use `infer_instance`. Take `⟨⟨i, v⟩, hv⟩` from `(sigmaMk V).surjective (e.inv u)`. Use `⟨i, v, ?_⟩` and prove the remaining obligations. Rewrite using `[← he i, Scheme.Hom.comp_apply, ← sigmaMk_mk, hv, hinv]`. Rewrite `h` using `[← he i, ← he k, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`.

Establish `h2` using `congrArg e.inv h`. Rewrite `h2` using `[hinv', hinv']`. Conclude with `congrArg Sigma.fst ((sigmaι_eq_iff V i k v w).1 h2)`.
-/
theorem pieces {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) :
    (∀ i, IsOpenImmersion (j i)) ∧ (∀ u : U, ∃ i, ∃ v : V i, j i v = u) ∧
      (∀ i k (v : V i) (w : V k), j i v = j k w → i = k) := by
  let e : ∐ V ≅ U := (colimit.isColimit (Discrete.functor V)).coconePointUniqueUpToIso hc
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (colimit.isColimit (Discrete.functor V)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hinv : ∀ u : U, e.hom (e.inv u) = u := fun u => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hinv' : ∀ z : (∐ V : Scheme.{0}), e.inv (e.hom z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  refine ⟨fun i => ?_, fun u => ?_, fun i k v w h => ?_⟩
  · rw [← he i]; infer_instance
  · obtain ⟨⟨i, v⟩, hv⟩ := (sigmaMk V).surjective (e.inv u)
    refine ⟨i, v, ?_⟩
    rw [← he i, Scheme.Hom.comp_apply, ← sigmaMk_mk, hv, hinv]
  · rw [← he i, ← he k, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    have h2 := congrArg e.inv h
    rw [hinv', hinv'] at h2
    exact congrArg Sigma.fst ((sigmaι_eq_iff V i k v w).1 h2)

/- English proof (translation)
Take `⟨ho, hcov, hdis⟩` from `pieces j hc`. Use `nonempty_isColimit_cofanMk_of _ ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨i, v, hv⟩` from `hcov (y z)`.

Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := y) (g := j i) z v hv.symm`. Conclude with `(TopologicalSpace.Opens.mem_iSup (s := fun i => (pullback.fst y (j i)).opensRange)).2 ⟨i, w, hw⟩`. Introduce `i k hik`. Rewrite using `[Function.onFun, disjoint_iff, eq_bot_iff]`. Introduce and unpack `z ⟨⟨p, hp⟩, ⟨q, hq⟩⟩`.

Apply `hik` to reduce the goal to its premises. Use `hdis i k (pullback.snd y (j i) p) (pullback.snd y (j k) q) ?_` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, ← pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `y ((pullback.fst y (j i)) p) = y ((pullback.fst y (j k)) q)`. Rewrite using `[hp, hq]`.
-/
theorem pullback_isColimit {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) {T : Scheme.{0}} (y : T ⟶ U) :
    Nonempty (IsColimit (Cofan.mk T (fun i => pullback.fst y (j i)))) := by
  obtain ⟨ho, hcov, hdis⟩ := pieces j hc
  refine nonempty_isColimit_cofanMk_of _ ?_ ?_
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨i, v, hv⟩ := hcov (y z)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := j i) z v hv.symm
    exact (TopologicalSpace.Opens.mem_iSup (s := fun i => (pullback.fst y (j i)).opensRange)).2 ⟨i, w, hw⟩
  · intro i k hik
    rw [Function.onFun, disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    apply hik
    refine hdis i k (pullback.snd y (j i) p) (pullback.snd y (j k) q) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, ← pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change y ((pullback.fst y (j i)) p) = y ((pullback.fst y (j k)) q)
    rw [hp, hq]

/- English proof (translation)
Use `haveI : ∀ e : PEmpty.{1}, IsOpenImmersion (PEmpty.elim e : (PEmpty.elim e : Scheme.{0}) ⟶ W) := fun e => e.elim`. Take `⟨hc⟩` from `nonempty_isColimit_cofanMk_of (X := fun e : PEmpty.{1} => (PEmpty.elim e : Scheme.{0})) (S := W) (fun e => PEmpty.elim e) (by rw [eq_top_iff]; rintro z -; exact isEmptyElim z) (fun e => PEmpty.elim e)`. Establish `hb` using `GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G W PEmpty.{1} _ _ hc`. Conclude with `⟨fun x y => hb.1 (funext fun e => PEmpty.elim e)⟩`.
-/
theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (G : Shv R) (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton (Sec G W) := by
  haveI : ∀ e : PEmpty.{1}, IsOpenImmersion (PEmpty.elim e : (PEmpty.elim e : Scheme.{0}) ⟶ W) :=
    fun e => e.elim
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (X := fun e : PEmpty.{1} => (PEmpty.elim e : Scheme.{0})) (S := W)
    (fun e => PEmpty.elim e) (by rw [eq_top_iff]; rintro z -; exact isEmptyElim z) (fun e => PEmpty.elim e)
  have hb := GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G W PEmpty.{1} _ _ hc
  exact ⟨fun x y => hb.1 (funext fun e => PEmpty.elim e)⟩

end GlobalTheory.EtC.FreeCofan

namespace GlobalTheory.EtC.FreeCofan

/- English proof (translation)
Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem res_res {R : Type} [CommRing R] {G : Shv R} {W W' T : Scheme.{0}} (g : W ⟶ W') (f : W' ⟶ T)
    (z : Sec G T) : Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/- English proof (translation)
Introduce `R _ U ι V j hc P t Q a b hpb`. Take `⟨ho, -, hdis⟩` from `pieces j hc`. Establish `FH` using `fun (P' : PSh) (G : Shv R) => GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R P' G`. Set `y : ∀ T : Scheme.{0}, P.obj (op T) → (T ⟶ U)` to `fun T x => t.app (op T) x`. Establish `hy : ∀ (T T' : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)), y T' (P.map g.op x) = g ≫ y T x` using `fun T T' g x => FunctorToTypes.naturality t g.op x`.

Establish `hw : ∀ i (W : Scheme.{0}) (q0 : (Q i).obj (op W)), y W ((a i).app _ q0) = ((b i).app _ q0 : W ⟶ V i) ≫ j i` using `fun i W q0 => ConcreteCategory.congr_hom (congr_app (hpb i).w (op W)) q0`. Establish `hcol : ∀ (T : Scheme.{0}) (x : P.obj (op T)), IsColimit (Cofan.mk T (fun i => pullback.fst (y T x) (j i)))` using `fun T x => (pullback_isColimit j hc (y T x)).some`. Establish `SC` using `fun (G : Shv R) (T : Scheme.{0}) (x : P.obj (op T)) => GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G T ι _ _ (hcol T x)`. Establish `hex : ∀ i (W : Scheme.{0}) (x : P.obj (op W)) (σ : W ⟶ V i), y W x = σ ≫ j i → ∃ q : (Q i).obj (op W), (a i).app _ q = x ∧ (b i).app _ q = σ` using `fun i W x σ h => Types.exists_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) x σ h`. Establish `huq : ∀ i (W : Scheme.{0}) (q q' : (Q i).obj (op W)), (a i).app _ q = (a i).app _ q' → (b i).app _ q = (b i).app _ q' → q = q'` using `fun i W q q' h1 h2 => Types.ext_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) h1 h2`.

Establish `hq : ∀ (T : Scheme.{0}) (x : P.obj (op T)) i, ∃ q : (Q i).obj (op (pullback (y T x) (j i))), (a i).app _ q = P.map (pullback.fst (y T x) (j i)).op x ∧ (b i).app _ q = pullback.snd (y T x) (j i)` using `fun T x i => hex i _ _ _ (by rw [hy]; exact pullback.condition)`. Use `choose q hqa hqb using hq`. Establish `key : ∀ (G : Shv R) (m : (free R).obj P ⟶ G) T x i, Sec.res (pullback.fst (y T x) (j i)) (val m T x) = val ((free R).map (a i) ≫ m) _ (q T x i)`. Introduce `G m T x i`. Rewrite using `[(FH P G).2.2.2.1 (Q i) (a i) m, hqa, (FH P G).2.2.1 m]`.

Set `φ : ∀ (G : Shv R) (c : ∀ i, (free R).obj (Q i) ⟶ G) (T : Scheme.{0}), P.obj (op T) → Sec G T` to `fun G c T x => Function.surjInv (SC G T x).2 (fun i => val (c i) _ (q T x i))`. Establish `hφ : ∀ G c T x i, Sec.res (pullback.fst (y T x) (j i)) (φ G c T x) = val (c i) _ (q T x i)` using `fun G c T x i => congrFun (Function.surjInv_eq (SC G T x).2 _) i`. Establish `nat : ∀ G c (T' T : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)), φ G c T' (P.map g.op x) = Sec.res g (φ G c T x)`. Introduce `G c T' T g x`. Apply `(SC G T' (P.map g.op x)).1` to reduce the goal to its premises.

Use `funext fun i => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hφ, res_res]`. Establish `hw2 : (pullback.fst (y T' (P.map g.op x)) (j i) ≫ g) ≫ y T x = pullback.snd _ (j i) ≫ j i`. Rewrite using `[Category.assoc, ← hy, pullback.condition]`.

Establish `h1 : pullback.lift _ _ hw2 ≫ pullback.fst (y T x) (j i) = pullback.fst (y T' (P.map g.op x)) (j i) ≫ g` using `pullback.lift_fst _ _ _`. Establish `h2 : pullback.lift _ _ hw2 ≫ pullback.snd (y T x) (j i) = pullback.snd (y T' (P.map g.op x)) (j i)` using `pullback.lift_snd _ _ _`. Rewrite using `[← h1, ← res_res, hφ, ← (FH (Q i) G).2.2.1 (c i)]`. Use `congr 1`. Apply `huq` to reduce the goal to its premises.

Rewrite using `[hqa, FunctorToTypes.naturality, hqa, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, h1]`. Rewrite using `[hqb, FunctorToTypes.naturality, hqb]`. Conclude with `h2.symm`. Set `d : ∀ s : Cofan (fun i => (free R).obj (Q i)), (free R).obj P ⟶ s.pt` to `fun s => ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose`. Establish `hd : ∀ s T x, val (d s) T x = φ s.pt s.inj T x` using `fun s => ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose_spec`.

Use `⟨mkCofanColimit _ d ?_ ?_⟩` and prove the remaining obligations. Introduce `s i`. Express the relevant statement in the definitionally equal form `(free R).map (a i) ≫ d s = s.inj i`. Apply `(FH (Q i) s.pt).1` to reduce the goal to its premises. Introduce `W q0`.

Rewrite using `[(FH P s.pt).2.2.2.1 (Q i) (a i), hd]`. Take `⟨x, hx⟩ : ∃ x, x = (a i).app (op W) q0` from `⟨_, rfl⟩`. Establish `hwx : y W x = ((b i).app _ q0 : W ⟶ V i) ≫ j i` using `hx ▸ hw i W q0`. Rewrite using `[← hx]`. Apply `(SC s.pt W x).1` to reduce the goal to its premises.

Use `funext fun k => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hφ, ← (FH (Q i) s.pt).2.2.1]`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality.

Use `congr 1`. Apply `huq` to reduce the goal to its premises. Rewrite using `[hqa, FunctorToTypes.naturality, ← hx]`. Rewrite using `[hqb, FunctorToTypes.naturality]`. Express the relevant statement in the definitionally equal form `_ = pullback.fst (y W x) (j k) ≫ ((b k).app _ q0 : W ⟶ V k)`.

Use `haveI := ho k`. Rewrite using `[← cancel_mono (j k), Category.assoc, ← pullback.condition, hwx]`. Use `haveI : IsEmpty ((pullback (y W x) (j k) : Scheme.{0}) : Type) := by`. Use `⟨fun z => hki (hdis k i (pullback.snd (y W x) (j k) z) ((pullback.fst (y W x) (j k) ≫ ((b i).app _ q0 : W ⟶ V i)) z) ?_)⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, Category.assoc, ← hwx]`.

Conclude with `(sec_subsingleton_of_isEmpty s.pt _).elim _ _`. Introduce `s m hm`. Establish `hm' : ∀ i, (free R).map (a i) ≫ m = s.inj i` using `hm`. Apply `(FH P s.pt).1` to reduce the goal to its premises. Introduce `T x`.

Rewrite using `[hd]`. Apply `(SC s.pt T x).1` to reduce the goal to its premises. Use `funext fun i => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hφ, key, hm']`.
-/
theorem main : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ (P : PSh) (t : P ⟶ yoneda.obj U) (Q : ι → PSh) (a : ∀ i, Q i ⟶ P) (b : ∀ i, Q i ⟶ yoneda.obj (V i)), (∀ i, IsPullback (a i) (b i) t (yoneda.map (j i))) → Nonempty (IsColimit (Cofan.mk ((free R).obj P) (fun i ↦ (free R).map (a i)))) := by
  intro R _ U ι V j hc P t Q a b hpb
  obtain ⟨ho, -, hdis⟩ := pieces j hc
  have FH := fun (P' : PSh) (G : Shv R) => GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R P' G
  let y : ∀ T : Scheme.{0}, P.obj (op T) → (T ⟶ U) := fun T x => t.app (op T) x
  have hy : ∀ (T T' : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)), y T' (P.map g.op x) = g ≫ y T x :=
    fun T T' g x => FunctorToTypes.naturality t g.op x
  have hw : ∀ i (W : Scheme.{0}) (q0 : (Q i).obj (op W)), y W ((a i).app _ q0) = ((b i).app _ q0 : W ⟶ V i) ≫ j i :=
    fun i W q0 => ConcreteCategory.congr_hom (congr_app (hpb i).w (op W)) q0
  have hcol : ∀ (T : Scheme.{0}) (x : P.obj (op T)), IsColimit (Cofan.mk T (fun i => pullback.fst (y T x) (j i))) :=
    fun T x => (pullback_isColimit j hc (y T x)).some
  have SC := fun (G : Shv R) (T : Scheme.{0}) (x : P.obj (op T)) => GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G T ι _ _ (hcol T x)
  have hex : ∀ i (W : Scheme.{0}) (x : P.obj (op W)) (σ : W ⟶ V i), y W x = σ ≫ j i →
      ∃ q : (Q i).obj (op W), (a i).app _ q = x ∧ (b i).app _ q = σ := fun i W x σ h =>
    Types.exists_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) x σ h
  have huq : ∀ i (W : Scheme.{0}) (q q' : (Q i).obj (op W)), (a i).app _ q = (a i).app _ q' →
      (b i).app _ q = (b i).app _ q' → q = q' := fun i W q q' h1 h2 =>
    Types.ext_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) h1 h2
  have hq : ∀ (T : Scheme.{0}) (x : P.obj (op T)) i, ∃ q : (Q i).obj (op (pullback (y T x) (j i))),
      (a i).app _ q = P.map (pullback.fst (y T x) (j i)).op x ∧ (b i).app _ q = pullback.snd (y T x) (j i) :=
    fun T x i => hex i _ _ _ (by rw [hy]; exact pullback.condition)
  choose q hqa hqb using hq
  have key : ∀ (G : Shv R) (m : (free R).obj P ⟶ G) T x i,
      Sec.res (pullback.fst (y T x) (j i)) (val m T x) = val ((free R).map (a i) ≫ m) _ (q T x i) := by
    intro G m T x i
    rw [(FH P G).2.2.2.1 (Q i) (a i) m, hqa, (FH P G).2.2.1 m]
  let φ : ∀ (G : Shv R) (c : ∀ i, (free R).obj (Q i) ⟶ G) (T : Scheme.{0}), P.obj (op T) → Sec G T :=
    fun G c T x => Function.surjInv (SC G T x).2 (fun i => val (c i) _ (q T x i))
  have hφ : ∀ G c T x i, Sec.res (pullback.fst (y T x) (j i)) (φ G c T x) = val (c i) _ (q T x i) :=
    fun G c T x i => congrFun (Function.surjInv_eq (SC G T x).2 _) i
  have nat : ∀ G c (T' T : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)),
      φ G c T' (P.map g.op x) = Sec.res g (φ G c T x) := by
    intro G c T' T g x
    apply (SC G T' (P.map g.op x)).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, res_res]
    have hw2 : (pullback.fst (y T' (P.map g.op x)) (j i) ≫ g) ≫ y T x = pullback.snd _ (j i) ≫ j i := by
      rw [Category.assoc, ← hy, pullback.condition]
    have h1 : pullback.lift _ _ hw2 ≫ pullback.fst (y T x) (j i) = pullback.fst (y T' (P.map g.op x)) (j i) ≫ g :=
      pullback.lift_fst _ _ _
    have h2 : pullback.lift _ _ hw2 ≫ pullback.snd (y T x) (j i) = pullback.snd (y T' (P.map g.op x)) (j i) :=
      pullback.lift_snd _ _ _
    rw [← h1, ← res_res, hφ, ← (FH (Q i) G).2.2.1 (c i)]
    congr 1
    apply huq
    · rw [hqa, FunctorToTypes.naturality, hqa, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
        ← op_comp, ← op_comp, h1]
    · rw [hqb, FunctorToTypes.naturality, hqb]
      exact h2.symm
  let d : ∀ s : Cofan (fun i => (free R).obj (Q i)), (free R).obj P ⟶ s.pt := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose
  have hd : ∀ s T x, val (d s) T x = φ s.pt s.inj T x := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose_spec
  refine ⟨mkCofanColimit _ d ?_ ?_⟩
  · intro s i
    change (free R).map (a i) ≫ d s = s.inj i
    apply (FH (Q i) s.pt).1
    intro W q0
    rw [(FH P s.pt).2.2.2.1 (Q i) (a i), hd]
    obtain ⟨x, hx⟩ : ∃ x, x = (a i).app (op W) q0 := ⟨_, rfl⟩
    have hwx : y W x = ((b i).app _ q0 : W ⟶ V i) ≫ j i := hx ▸ hw i W q0
    rw [← hx]
    apply (SC s.pt W x).1
    refine funext fun k => ?_
    dsimp only
    rw [hφ, ← (FH (Q i) s.pt).2.2.1]
    by_cases hki : k = i
    · subst hki
      congr 1
      apply huq
      · rw [hqa, FunctorToTypes.naturality, ← hx]
      · rw [hqb, FunctorToTypes.naturality]
        change _ = pullback.fst (y W x) (j k) ≫ ((b k).app _ q0 : W ⟶ V k)
        haveI := ho k
        rw [← cancel_mono (j k), Category.assoc, ← pullback.condition, hwx]
    · haveI : IsEmpty ((pullback (y W x) (j k) : Scheme.{0}) : Type) := by
        refine ⟨fun z => hki (hdis k i (pullback.snd (y W x) (j k) z)
          ((pullback.fst (y W x) (j k) ≫ ((b i).app _ q0 : W ⟶ V i)) z) ?_)⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, Category.assoc, ← hwx]
      exact (sec_subsingleton_of_isEmpty s.pt _).elim _ _
  · intro s m hm
    have hm' : ∀ i, (free R).map (a i) ≫ m = s.inj i := hm
    apply (FH P s.pt).1
    intro T x
    rw [hd]
    apply (SC s.pt T x).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, key, hm']

end GlobalTheory.EtC.FreeCofan
