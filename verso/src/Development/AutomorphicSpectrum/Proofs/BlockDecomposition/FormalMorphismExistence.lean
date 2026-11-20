import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.MorphismAlgebraisation

/- English proof (translation)
The claim follows from `IsPullback.of_bot (by rw [hA, hB]; exact IsPullback.id_vert q) hc.symm h`.
-/
lemma isPullback_of_sections {C : Type*} [Category C] {A A' B B' : C} {p : A ⟶ B} {q : A' ⟶ B'}
    {rA : A ⟶ A'} {rB : B ⟶ B'} {sA : A' ⟶ A} {sB : B' ⟶ B} (h : IsPullback p rA rB q)
    (hA : sA ≫ rA = 𝟙 _) (hB : sB ≫ rB = 𝟙 _) (hc : sA ≫ p = q ≫ sB) :
    IsPullback q sA sB p :=
  IsPullback.of_bot (by rw [hA, hB]; exact IsPullback.id_vert q) hc.symm h

section Graph

variable {S Se X Z Y : Scheme.{0}} (hX : X ⟶ S) (hZ : Z ⟶ S) (t : Se ⟶ S) {b : Y ⟶ X} {y : Y ⟶ Se}

def retr (h : IsPullback b y hX t) : pullback (pullback.fst hX hZ ≫ hX) t ⟶ Y :=
  h.lift (pullback.fst _ t ≫ pullback.fst hX hZ) (pullback.snd _ t)
    (by simp only [Category.assoc]; exact pullback.condition)

/- English proof (translation)
The claim follows from `h.lift_fst _ _ _`.
-/
lemma retr_fst (h : IsPullback b y hX t) :
    retr hX hZ t h ≫ b = pullback.fst _ t ≫ pullback.fst hX hZ := h.lift_fst _ _ _

/- English proof (translation)
The claim follows from `h.lift_snd _ _ _`.
-/
lemma retr_snd (h : IsPullback b y hX t) : retr hX hZ t h ≫ y = pullback.snd _ t :=
  h.lift_snd _ _ _

/- English proof (translation)
The claim follows from `IsPullback.of_bot (by rw [retr_snd]; exact IsPullback.of_hasPullback _ _) (retr_fst hX hZ t h).symm h`.
-/
lemma isPullback_retr (h : IsPullback b y hX t) :
    IsPullback (pullback.fst (pullback.fst hX hZ ≫ hX) t) (retr hX hZ t h)
      (pullback.fst hX hZ) b :=
  IsPullback.of_bot (by rw [retr_snd]; exact IsPullback.of_hasPullback _ _)
    (retr_fst hX hZ t h).symm h

def graph (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    Y ⟶ pullback (pullback.fst hX hZ ≫ hX) t :=
  pullback.lift (pullback.lift b f (by rw [hf, h.w])) y (by rw [pullback.lift_fst_assoc, h.w])

@[reassoc (attr := simp)]
/- English proof (translation)
Rewrite using `[graph, pullback.lift_fst_assoc, pullback.lift_fst]`. Use the proof step `@[reassoc (attr := simp)]`.
-/
lemma graph_fst_fst (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.fst _ t ≫ pullback.fst hX hZ = b := by
  rw [graph, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
/- English proof (translation)
Rewrite using `[graph, pullback.lift_fst_assoc, pullback.lift_snd]`. Use the proof step `@[reassoc (attr := simp)]`.
-/
lemma graph_fst_snd (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.fst _ t ≫ pullback.snd hX hZ = f := by
  rw [graph, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
/- English proof (translation)
Rewrite using `[graph, pullback.lift_snd]`.
-/
lemma graph_snd (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.snd _ t = y := by
  rw [graph, pullback.lift_snd]

/- English proof (translation)
Apply `h.hom_ext` to reduce the goal to its premises. Simplify using `[retr_fst]`. Simplify using `[retr_snd]`.
-/
lemma graph_retr (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ retr hX hZ t h = 𝟙 Y := by
  apply h.hom_ext
  · simp [retr_fst]
  · simp [retr_snd]

/- English proof (translation)
Establish `: IsSeparated (retr hX hZ t h)` using `MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_retr hX hZ t h) inferInstance`. Establish `: IsClosedImmersion (graph hX hZ t h f hf ≫ retr hX hZ t h)`. Rewrite using `[graph_retr]`. Use `infer_instance`. Conclude with `IsClosedImmersion.of_comp _ (retr hX hZ t h)`.
-/
lemma isClosedImmersion_graph [IsSeparated hZ] (h : IsPullback b y hX t) (f : Y ⟶ Z)
    (hf : f ≫ hZ = y ≫ t) : IsClosedImmersion (graph hX hZ t h f hf) := by
  have : IsSeparated (retr hX hZ t h) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_retr hX hZ t h) inferInstance
  have : IsClosedImmersion (graph hX hZ t h f hf ≫ retr hX hZ t h) := by
    rw [graph_retr]; infer_instance
  exact IsClosedImmersion.of_comp _ (retr hX hZ t h)

/- English proof (translation)
Use `set m := pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _) (by simp) (by simp [hτ]) with hm`. Establish `m_fst : m ≫ pullback.fst _ t' = pullback.fst _ t`. Rewrite using `[hm, pullback.map, pullback.lift_fst, Category.comp_id]`. Establish `m_snd : m ≫ pullback.snd _ t' = pullback.snd _ t ≫ τ`. Rewrite using `[hm, pullback.map, pullback.lift_snd]`.

Establish `sq : m ≫ retr hX hZ t' h' = retr hX hZ t h ≫ β`. Apply `h'.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hβ, retr_fst, retr_fst, reassoc_of% m_fst]`. Rewrite using `[Category.assoc, Category.assoc, hy, retr_snd, m_snd, reassoc_of% (retr_snd hX hZ t h)]`. Establish `h0 : IsPullback m (retr hX hZ t h) (retr hX hZ t' h') β` using `IsPullback.of_right (h₁₂ := pullback.fst _ t') (h₂₂ := b') (v₁₃ := pullback.fst hX hZ) (by rw [m_fst, hβ]; exact isPullback_retr hX hZ t h) sq (isPullback_retr hX hZ t' h')`.

Use `isPullback_of_sections h0 (graph_retr hX hZ t h f hf) (graph_retr hX hZ t' h' f' hf') ?_` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, m_fst, graph_fst_fst, graph_fst_fst_assoc, hβ]`. Simplify using `only [Category.assoc, m_fst, graph_fst_snd, graph_fst_snd_assoc, hff]`.

Simplify using `only [Category.assoc, m_snd, graph_snd, graph_snd_assoc, hy]`.
-/
lemma isPullback_graph [IsSeparated hZ] {Se' Y' : Scheme.{0}} (t' : Se' ⟶ S) {b' : Y' ⟶ X} {y' : Y' ⟶ Se'}
    (τ : Se ⟶ Se') (hτ : τ ≫ t' = t) (h : IsPullback b y hX t) (h' : IsPullback b' y' hX t')
    (β : Y ⟶ Y') (hβ : β ≫ b' = b) (hy : β ≫ y' = y ≫ τ) (f : Y ⟶ Z) (f' : Y' ⟶ Z)
    (hf : f ≫ hZ = y ≫ t) (hf' : f' ≫ hZ = y' ≫ t') (hff : β ≫ f' = f) :
    IsPullback β (graph hX hZ t h f hf) (graph hX hZ t' h' f' hf')
      (pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _)
        (by simp) (by simp [hτ])) := by
  set m := pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _)
        (by simp) (by simp [hτ]) with hm
  have m_fst : m ≫ pullback.fst _ t' = pullback.fst _ t := by
    rw [hm, pullback.map, pullback.lift_fst, Category.comp_id]
  have m_snd : m ≫ pullback.snd _ t' = pullback.snd _ t ≫ τ := by
    rw [hm, pullback.map, pullback.lift_snd]
  have sq : m ≫ retr hX hZ t' h' = retr hX hZ t h ≫ β := by
    apply h'.hom_ext
    · rw [Category.assoc, Category.assoc, hβ, retr_fst, retr_fst, reassoc_of% m_fst]
    · rw [Category.assoc, Category.assoc, hy, retr_snd, m_snd, reassoc_of% (retr_snd hX hZ t h)]
  have h0 : IsPullback m (retr hX hZ t h) (retr hX hZ t' h') β :=
    IsPullback.of_right (h₁₂ := pullback.fst _ t') (h₂₂ := b') (v₁₃ := pullback.fst hX hZ)
      (by rw [m_fst, hβ]; exact isPullback_retr hX hZ t h) sq (isPullback_retr hX hZ t' h')
  refine isPullback_of_sections h0 (graph_retr hX hZ t h f hf) (graph_retr hX hZ t' h' f' hf') ?_
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, m_fst, graph_fst_fst, graph_fst_fst_assoc, hβ]
    · simp only [Category.assoc, m_fst, graph_fst_snd, graph_fst_snd_assoc, hff]
  · simp only [Category.assoc, m_snd, graph_snd, graph_snd_assoc, hy]

end Graph

/- English proof (translation)
Introduce `hGE hIso R _ _ I hI X Z hXp hZs hZf hZq Y β b hb hβ f hf hfβ`. Set `P : Over (Spec (CommRingCat.of R))` to `Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)`. Establish `hPs : IsSeparated P.hom` using `by dsimp only [P, Over.mk_hom]; infer_instance`. Establish `hPf : LocallyOfFiniteType P.hom` using `by dsimp only [P, Over.mk_hom]; infer_instance`. Establish `hPq : QuasiCompact P.hom` using `by dsimp only [P, Over.mk_hom]; infer_instance`.

Establish `hth : ∀ e, IsClosedImmersion (thick R I e)` using `fun e => IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hy : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e` using `fun e => by`. Rewrite using `[← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp, ← (hb (e + 1)).w, ← (hb e).w, ← Category.assoc, hβ]`. Set `i : ∀ e, (Y e).left ⟶ (thickObj R I e P).left` to `fun e => graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)`. Establish `hi : ∀ e, IsClosedImmersion (i e)` using `fun e => isClosedImmersion_graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)`.

Establish `hiβ : ∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P)` using `fun e => isPullback_graph X.hom Z.hom (thick R I e) (thick R I (e + 1)) (thickTrans R I e) (thickTrans_comp R I e) (hb e) (hb (e + 1)) (β e) (hβ e) (hy e) (f e) (f (e + 1)) (hf e) (hf (e + 1)) (hfβ e)`. Establish `hisnd : ∀ e, i e ≫ pullback.snd P.hom (thick R I e) = (Y e).hom` using `fun e => graph_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)`. Establish `hi0 : IsProper (i 0 ≫ (thickObj R I 0 P).hom)`. Establish `h1 : i 0 ≫ (thickObj R I 0 P).hom = (Y 0).hom` using `hisnd 0`. Rewrite using `[h1]`.

Conclude with `MorphismProperty.of_isPullback (P := @IsProper) (hb 0) hXp`. Take `⟨C', j, b', hj, hjp, hpb, hb'⟩` from `hGE R I hI P hPs hPf hPq (fun e => (Y e).left) i β hi hiβ hi0`. Set `Co : Over (Spec (CommRingCat.of R))` to `Over.mk (j ≫ P.hom)`. Set `p : Co ⟶ X` to `Over.homMk (j ≫ pullback.fst X.hom Z.hom) (by simp [Co, P])`. Establish `hpl : p.left = j ≫ pullback.fst X.hom Z.hom` using `rfl`.

Establish `hpp : IsProper p.left`. Establish `h1 : IsProper (p.left ≫ X.hom)`. Establish `h2 : p.left ≫ X.hom = j ≫ P.hom` using `by simp [hpl, P]`. Rewrite using `[h2]`. Conclude with `hjp`.

Conclude with `IsProper.of_comp _ X.hom`. Establish `hC : ∀ e, IsPullback (b' e) (Y e).hom Co.hom (thick R I e)` using `fun e => by`. Establish `h1` using `(hpb e).paste_vert (IsPullback.of_hasPullback P.hom (thick R I e))`. Rewrite `h1` using `[hisnd e]`. Conclude with `h1`.

Establish `hbe : ∀ e, b' e ≫ p.left = b e` using `fun e => by`. Establish `h1` using `(hpb e).w`. Rewrite using `[hpl, reassoc_of% h1]`. Conclude with `graph_fst_fst X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)`. Establish `hiso : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left` using `fun e => by`.

Establish `key : (hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left = (hb e).isoPullback.hom`. Establish `m1 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.fst X.hom (thick R I e) = pullback.fst Co.hom (thick R I e) ≫ p.left` using `pullback.lift_fst _ _ _`. Establish `m2 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.snd X.hom (thick R I e) = pullback.snd Co.hom (thick R I e)` using `pullback.lift_snd _ _ _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, m1, IsPullback.isoPullback_hom_fst_assoc, hbe, IsPullback.isoPullback_hom_fst]`.

Rewrite using `[Category.assoc, m2, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]`. Establish `h1 : IsIso ((hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left)`. Rewrite using `[key]`. Use `infer_instance`. Conclude with `IsIso.of_isIso_comp_left (hC e).isoPullback.hom _`.

Establish `hp : IsIso p` using `hIso R I hI X Co p hXp hpp hiso`. Establish `hl : IsIso p.left` using `inferInstanceAs (IsIso ((Over.forget _).map p))`. Establish `hz : j ≫ pullback.snd X.hom Z.hom ≫ Z.hom = p.left ≫ X.hom`. Rewrite using `[hpl, Category.assoc, pullback.condition]`. Use `⟨Over.homMk (inv p.left ≫ j ≫ pullback.snd X.hom Z.hom) ?_, fun e => ?_⟩` and prove the remaining obligations.

Simplify using `[hz]`. Establish `h1` using `(hpb e).w`. Establish `h2 : b' e ≫ j ≫ pullback.snd X.hom Z.hom = f e`. Rewrite using `[reassoc_of% h1]`. Conclude with `graph_fst_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)`.

Simplify using `only [Over.homMk_left]`. Rewrite using `[← hbe e, Category.assoc, IsIso.hom_inv_id_assoc, h2]`.
-/
theorem exists_hom_of_thickenings : GEClosed → IsoOfThick →
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃ g : X ⟶ Z, ∀ e, b e ≫ g.left = f e := by
  intro hGE hIso R _ _ I hI X Z hXp hZs hZf hZq Y β b hb hβ f hf hfβ
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)
  have hPs : IsSeparated P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hPf : LocallyOfFiniteType P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hPq : QuasiCompact P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hth : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := fun e => by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp,
      ← (hb (e + 1)).w, ← (hb e).w, ← Category.assoc, hβ]
  let i : ∀ e, (Y e).left ⟶ (thickObj R I e P).left := fun e =>
    graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hi : ∀ e, IsClosedImmersion (i e) := fun e =>
    isClosedImmersion_graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hiβ : ∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P) := fun e =>
    isPullback_graph X.hom Z.hom (thick R I e) (thick R I (e + 1)) (thickTrans R I e)
      (thickTrans_comp R I e) (hb e) (hb (e + 1)) (β e) (hβ e) (hy e) (f e) (f (e + 1)) (hf e)
      (hf (e + 1)) (hfβ e)
  have hisnd : ∀ e, i e ≫ pullback.snd P.hom (thick R I e) = (Y e).hom := fun e =>
    graph_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hi0 : IsProper (i 0 ≫ (thickObj R I 0 P).hom) := by
    have h1 : i 0 ≫ (thickObj R I 0 P).hom = (Y 0).hom := hisnd 0
    rw [h1]
    exact MorphismProperty.of_isPullback (P := @IsProper) (hb 0) hXp
  obtain ⟨C', j, b', hj, hjp, hpb, hb'⟩ :=
    hGE R I hI P hPs hPf hPq (fun e => (Y e).left) i β hi hiβ hi0
  let Co : Over (Spec (CommRingCat.of R)) := Over.mk (j ≫ P.hom)
  let p : Co ⟶ X := Over.homMk (j ≫ pullback.fst X.hom Z.hom) (by simp [Co, P])
  have hpl : p.left = j ≫ pullback.fst X.hom Z.hom := rfl
  have hpp : IsProper p.left := by
    have h1 : IsProper (p.left ≫ X.hom) := by
      have h2 : p.left ≫ X.hom = j ≫ P.hom := by simp [hpl, P]
      rw [h2]; exact hjp
    exact IsProper.of_comp _ X.hom
  have hC : ∀ e, IsPullback (b' e) (Y e).hom Co.hom (thick R I e) := fun e => by
    have h1 := (hpb e).paste_vert (IsPullback.of_hasPullback P.hom (thick R I e))
    rw [hisnd e] at h1
    exact h1
  have hbe : ∀ e, b' e ≫ p.left = b e := fun e => by
    have h1 := (hpb e).w
    rw [hpl, reassoc_of% h1]
    exact graph_fst_fst X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hiso : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left := fun e => by
    have key : (hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left =
        (hb e).isoPullback.hom := by
      have m1 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.fst X.hom (thick R I e) =
          pullback.fst Co.hom (thick R I e) ≫ p.left := pullback.lift_fst _ _ _
      have m2 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.snd X.hom (thick R I e) =
          pullback.snd Co.hom (thick R I e) := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, m1, IsPullback.isoPullback_hom_fst_assoc, hbe,
          IsPullback.isoPullback_hom_fst]
      · rw [Category.assoc, m2, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]
    have h1 : IsIso ((hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left) := by
      rw [key]; infer_instance
    exact IsIso.of_isIso_comp_left (hC e).isoPullback.hom _
  have hp : IsIso p := hIso R I hI X Co p hXp hpp hiso
  have hl : IsIso p.left := inferInstanceAs (IsIso ((Over.forget _).map p))
  have hz : j ≫ pullback.snd X.hom Z.hom ≫ Z.hom = p.left ≫ X.hom := by
    rw [hpl, Category.assoc, pullback.condition]
  refine ⟨Over.homMk (inv p.left ≫ j ≫ pullback.snd X.hom Z.hom) ?_, fun e => ?_⟩
  · simp [hz]
  · have h1 := (hpb e).w
    have h2 : b' e ≫ j ≫ pullback.snd X.hom Z.hom = f e := by
      rw [reassoc_of% h1]
      exact graph_fst_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
    simp only [Over.homMk_left]
    rw [← hbe e, Category.assoc, IsIso.hom_inv_id_assoc, h2]

end GlobalTheory.CompanionTheory.MorphismAlgebraisation
