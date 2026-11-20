import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.HkOfPush
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Rewrite using `[Functor.map_comp, GlobalTheory.EtC.pullHQ, GlobalTheory.EtC.pullHl_comp, LinearMap.baseChange_comp]`. Both sides reduce to the same expression.
-/
private lemma pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (x : GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj C) n 0) :
    GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (f ≫ g)) n 0 x =
      GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map f) n 0 (GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map g) n 0 x) := by
  rw [Functor.map_comp, GlobalTheory.EtC.pullHQ, GlobalTheory.EtC.pullHl_comp, LinearMap.baseChange_comp]; rfl

/- English proof (translation)
Substitute `hu` using the available equality. Use `IsPullback.of_bot (h₁₁ := pullback.fst (u ≫ q) c) (v₂₁ := pullback.snd q c) (v₂₂ := q) (h₃₁ := c) ?_ ?_ (IsPullback.of_hasPullback q c)` and prove the remaining obligations. Rewrite using `[pullback.lift_snd]`. Conclude with `IsPullback.of_hasPullback _ _`. Rewrite using `[pullback.lift_fst]`.
-/
private lemma pb_lift {A B S S' : Scheme.{0}} (a : A ⟶ S) (q : B ⟶ S) (u : A ⟶ B) (hu : u ≫ q = a)
    (c : S' ⟶ S) (h : (pullback.fst a c ≫ u) ≫ q = pullback.snd a c ≫ c) :
    IsPullback (pullback.fst a c) (pullback.lift (pullback.fst a c ≫ u) (pullback.snd a c) h) u
      (pullback.fst q c) := by
  subst hu
  refine IsPullback.of_bot (h₁₁ := pullback.fst (u ≫ q) c) (v₂₁ := pullback.snd q c) (v₂₂ := q) (h₃₁ := c)
    ?_ ?_ (IsPullback.of_hasPullback q c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback _ _
  · rw [pullback.lift_fst]

/- English proof (translation)
Take `⟨h, hI⟩` from `H`. Establish `Q` using `(IsPullback.of_hasPullback p' x).paste_horiz P`. Establish `claim : (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) : ∐ (fun _ : Fin m => X) ⟶ pullback p' x) ≫ Q.isoPullback.hom = Sigma.desc (fun i => pullback.lift (z i ≫ b) (𝟙 X) (by rw [h i, Category.id_comp]))`. Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[Sigma.ι_desc_assoc, Sigma.ι_desc]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Q.isoPullback_hom_fst, pullback.lift_fst, pullback.lift_fst_assoc]`. Rewrite using `[Category.assoc, Q.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]`. Use `haveI : IsIso ((Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) : ∐ (fun _ : Fin m => X) ⟶ pullback p' x) ≫ Q.isoPullback.hom) := by`.

Rewrite using `[claim]`. Conclude with `hI`. Conclude with `IsIso.of_isIso_comp_right _ Q.isoPullback.hom`.
-/
private lemma desc_iso_of_pb {X Y Y' Z Z' : Scheme.{0}} {p : Z ⟶ Y} {p' : Z' ⟶ Y'} {a : Y' ⟶ Y} {b : Z' ⟶ Z}
    (P : IsPullback b p' p a) (x : X ⟶ Y') {m : ℕ} (z : Fin m → (X ⟶ Z')) (hz : ∀ i, z i ≫ p' = x)
    (H : SplitOn p (x ≫ a) fun i => z i ≫ b) :
    IsIso (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p' x) := by
  obtain ⟨h, hI⟩ := H
  have Q := (IsPullback.of_hasPullback p' x).paste_horiz P
  have claim : (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p' x) ≫ Q.isoPullback.hom =
      Sigma.desc (fun i => pullback.lift (z i ≫ b) (𝟙 X) (by rw [h i, Category.id_comp])) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    apply pullback.hom_ext
    · rw [Category.assoc, Q.isoPullback_hom_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, Q.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  haveI : IsIso ((Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p' x) ≫ Q.isoPullback.hom) := by
    rw [claim]; exact hI
  exact IsIso.of_isIso_comp_right _ Q.isoPullback.hom

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private abbrev G {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) : E.gb M ⟶ E.gb N :=
  GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu)

private abbrev gX (M : Model l K) : E.gb M ⟶ M.X := pullback.fst _ _ ≫ pullback.fst _ _

/- English proof (translation)
Rewrite using `[G, gX, GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst, gX, Category.assoc]`.
-/
private lemma G_gX {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) : G u hu ≫ gX N = gX M ≫ u := by
  rw [G, gX, GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst,
    gX, Category.assoc]

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[G, GlobalTheory.Et.geomMap, Model.genMap]`. Simplify using `[G, GlobalTheory.Et.geomMap, Model.genMap]`. Simplify using `[G, GlobalTheory.Et.geomMap]`.
-/
private lemma G_comp {A B C : Model l K} (u : A.X ⟶ B.X) (hu : u ≫ B.p = A.p) (v : B.X ⟶ C.X)
    (hv : v ≫ C.p = B.p) (h : (u ≫ v) ≫ C.p = A.p) : G u hu ≫ G v hv = G (u ≫ v) h := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [G, GlobalTheory.Et.geomMap, Model.genMap]
    · simp [G, GlobalTheory.Et.geomMap, Model.genMap]
  · simp [G, GlobalTheory.Et.geomMap]

/- English proof (translation)
Establish `hu : IsUnit ((l : ℕ) : PadicAlgCl l)` using `(Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero).isUnit`. Set `φ : CommRingCat.of (PadicAlgCl l) ⟶ Γ(E.gb W, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl l))).inv ≫ (pullback.snd W.q _).appTop`. Use `hu.map φ.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.
-/
private lemma unit_gb (W : Model l K) : IsUnit (l : Γ(E.gb W, ⊤)) := by
  have hu : IsUnit ((l : ℕ) : PadicAlgCl l) :=
    (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero).isUnit
  let φ : CommRingCat.of (PadicAlgCl l) ⟶ Γ(E.gb W, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl l))).inv ≫ (pullback.snd W.q _).appTop
  have := hu.map φ.hom
  rwa [map_natCast] at this

/- English proof (translation)
Establish `s1` using `pb_lift (corrM M T).p M.p T.p rfl (Spec.map (CommRingCat.ofHom (OK l K).subtype)) (by rw [Category.assoc]; exact pullback.condition)`. Establish `s2` using `pb_lift (corrM M T).q M.q (Model.genMap (M := corrM M T) (N := M) T.p rfl) (Model.genMap_q (M := corrM M T) (N := M) T.p rfl) (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l)))) (by rw [Category.assoc, Model.genMap_q]; exact pullback.condition)`. Conclude with `s2.paste_horiz s1`.
-/
private lemma corr_pb (M : Model l K) (T : Corr l M.X) : IsPullback (gX (corrM M T)) (corrP M T) T.p (gX M) := by
  have s1 := pb_lift (corrM M T).p M.p T.p rfl (Spec.map (CommRingCat.ofHom (OK l K).subtype))
    (by rw [Category.assoc]; exact pullback.condition)
  have s2 := pb_lift (corrM M T).q M.q (Model.genMap (M := corrM M T) (N := M) T.p rfl)
    (Model.genMap_q (M := corrM M T) (N := M) T.p rfl)
    (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
    (by rw [Category.assoc, Model.genMap_q]; exact pullback.condition)
  exact s2.paste_horiz s1

/- English proof (translation)
Introduce `l _ K M T hr j t hP W w hw z hz hsp v`. Establish `hzp : ∀ i, z i ≫ (corrM M T).p = W.p` using `fun i => by show z i ≫ T.p ≫ M.p = W.p`. Rewrite using `[← Category.assoc, hz, hw]`. Establish `hs : ∀ i, G (M` using `W) (N := corrM M T) (z i) (hzp i) ≫ corrP M T = G (M := W) (N := M) w hw := fun i => by`. Establish `e` using `G_comp (A := W) (B := corrM M T) (C := M) (z i) (hzp i) T.p rfl (by rw [hz, hw])`.

Establish `e' : G (M` using `W) (N := M) (z i ≫ T.p) (by rw [hz, hw] : (z i ≫ T.p) ≫ M.p = W.p) = G (M := W) (N := M) w hw := by`. Use `hz i` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression. Conclude with `e.trans e'`.

Establish `hsplit : SplitOn T.p (G (M` using `W) (N := M) w hw ≫ gX M) fun i => G (M := W) (N := corrM M T) (z i) (hzp i) ≫ gX (corrM M T) := by`. Establish `H` using `hsp (E.gb W) (gX W) (unit_gb W)`. Establish `e1 : G (M` using `W) (N := M) w hw ≫ gX M = gX W ≫ w := G_gX (M := W) (N := M) w hw`. Establish `e2 : (fun i => G (M` using `W) (N := corrM M T) (z i) (hzp i) ≫ gX (corrM M T)) = fun i => gX W ≫ z i :=`. Use function extensionality and compare the values at `fun i => G_gX (M := W) (N := corrM M T) (z i) (hzp i)`.

Rewrite using `[e1, e2]`. Conclude with `H`. Establish `hI` using `desc_iso_of_pb (corr_pb M T) (G (M := W) (N := M) w hw) (fun i => G (M := W) (N := corrM M T) (z i) (hzp i)) hs hsplit`. Establish `key` using `hP (E.gb W) (G (M := W) (N := M) w hw) T.d (fun i => G (M := W) (N := corrM M T) (z i) (hzp i)) hs hI (Model.pullV (M := corrM M T) (N := M) T.r hr j v)`. Use `key.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Establish `e` using `G_comp (A := W) (B := corrM M T) (C := M) (z i) (hzp i) T.r hr (by rw [Category.assoc, hr, ← Category.assoc, hz, hw])`. Use `pb_comp l (G (M := W) (N := corrM M T) (z i) (hzp i)) (G (M := corrM M T) (N := M) T.r hr) j v` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this.symm`.
-/
theorem hkOfPush : UpperTheory.Ru.crystallineComparison.HkOfPush := by
  intro l _ K M T hr j t hP W w hw z hz hsp v
  have hzp : ∀ i, z i ≫ (corrM M T).p = W.p := fun i => by
    show z i ≫ T.p ≫ M.p = W.p
    rw [← Category.assoc, hz, hw]
  have hs : ∀ i, G (M := W) (N := corrM M T) (z i) (hzp i) ≫ corrP M T = G (M := W) (N := M) w hw := fun i => by
    have e := G_comp (A := W) (B := corrM M T) (C := M) (z i) (hzp i) T.p rfl (by rw [hz, hw])
    have e' : G (M := W) (N := M) (z i ≫ T.p) (by rw [hz, hw] : (z i ≫ T.p) ≫ M.p = W.p) = G (M := W) (N := M) w hw := by
      have := hz i
      subst this
      rfl
    exact e.trans e'
  have hsplit : SplitOn T.p (G (M := W) (N := M) w hw ≫ gX M) fun i => G (M := W) (N := corrM M T) (z i) (hzp i) ≫ gX (corrM M T) := by
    have H := hsp (E.gb W) (gX W) (unit_gb W)
    have e1 : G (M := W) (N := M) w hw ≫ gX M = gX W ≫ w := G_gX (M := W) (N := M) w hw
    have e2 : (fun i => G (M := W) (N := corrM M T) (z i) (hzp i) ≫ gX (corrM M T)) = fun i => gX W ≫ z i :=
      funext fun i => G_gX (M := W) (N := corrM M T) (z i) (hzp i)
    rw [e1, e2]
    exact H
  have hI := desc_iso_of_pb (corr_pb M T) (G (M := W) (N := M) w hw) (fun i => G (M := W) (N := corrM M T) (z i) (hzp i)) hs hsplit
  have key := hP (E.gb W) (G (M := W) (N := M) w hw) T.d (fun i => G (M := W) (N := corrM M T) (z i) (hzp i)) hs hI (Model.pullV (M := corrM M T) (N := M) T.r hr j v)
  refine key.trans (Finset.sum_congr rfl fun i _ => ?_)
  have e := G_comp (A := W) (B := corrM M T) (C := M) (z i) (hzp i) T.r hr
    (by rw [Category.assoc, hr, ← Category.assoc, hz, hw])
  have := pb_comp l (G (M := W) (N := corrM M T) (z i) (hzp i)) (G (M := corrM M T) (N := M) T.r hr) j v
  rw [e] at this
  exact this.symm

end UpperTheory.Ru.crystallineComparison
