import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlueClosed

/- English proof (translation)
Establish `hx : U.ι (pullback.fst U.ι V.ι x) ∈ U ⊓ V`. Use `⟨(pullback.fst U.ι V.ι x).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`. Conclude with `(pullback.snd U.ι V.ι x).2`. Take `⟨y, hy⟩ : ∃ y : (U ⊓ V).toScheme, (U ⊓ V).ι y = U.ι (pullback.fst U.ι V.ι x)` from `⟨⟨_, hx⟩, rfl⟩`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Apply `(pullback.fst U.ι V.ι ≫ U.ι).isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[← Scheme.Hom.comp_apply _ (pullback.fst U.ι V.ι ≫ U.ι), pullback.lift_fst_assoc, Scheme.homOfLE_ι, hy]`. Both sides reduce to the same expression.
-/
theorem exists_lift_eq {X : Scheme.{0}} (U V : X.Opens) (x : (pullback U.ι V.ι).carrier) :
    ∃ y : (U ⊓ V).toScheme, pullback.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (by simp) y = x := by
  have hx : U.ι (pullback.fst U.ι V.ι x) ∈ U ⊓ V := by
    refine ⟨(pullback.fst U.ι V.ι x).2, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd U.ι V.ι x).2
  obtain ⟨y, hy⟩ : ∃ y : (U ⊓ V).toScheme, (U ⊓ V).ι y = U.ι (pullback.fst U.ι V.ι x) :=
    ⟨⟨_, hx⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply (pullback.fst U.ι V.ι ≫ U.ι).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply _ (pullback.fst U.ι V.ι ≫ U.ι), pullback.lift_fst_assoc,
    Scheme.homOfLE_ι, hy]
  rfl

section
variable {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)

noncomputable def coverOfSet : X.OpenCover where
  I₀ := S
  X U := U.1.toScheme
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstanceAs (IsOpenImmersion U.1.ι)⟩
    obtain ⟨U, hU, hx⟩ := hcov x
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

instance : Preorder (coverOfSet S hcov).I₀ := inferInstanceAs (Preorder S)

@[reducible] noncomputable def locallyDirected (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) :
    (coverOfSet S hcov).LocallyDirected where
  trans {U V} h := X.homOfLE (show U.1 ≤ V.1 from h.le)
  trans_id U := X.homOfLE_rfl _
  trans_comp h k := (X.homOfLE_homOfLE _ _).symm
  w h := X.homOfLE_ι _
  directed {U V} x := by
    obtain ⟨y, hy⟩ := exists_lift_eq U.1 V.1 x
    exact ⟨⟨U.1 ⊓ V.1, hinf _ U.2 _ V.2⟩, homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1),
      homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1), y, hy⟩
  property_trans h := inferInstanceAs (IsOpenImmersion (X.homOfLE _))

end

/- English proof (translation)
Use `choose t ht using fun (U V : S) (h : U.1 ≤ V.1) ↦ (H U V h _ (c U)).1 ⟨𝟙 _, Category.id_comp _⟩`. Establish `hid : ∀ U : S, t U U le_rfl = 𝟙 _` using `fun U ↦ by`. Rewrite using `[← cancel_mono (c U), ht, X.homOfLE_rfl]`. Simplify using the standard rewrite rules. Establish `hcomp : ∀ (U V W : S) (h : U.1 ≤ V.1) (k : V.1 ≤ W.1), t U W (h.trans k) = t U V h ≫ t V W k` using `fun U V W h k ↦ by`.

Rewrite using `[← cancel_mono (c W), ht, Category.assoc, ht, ← Category.assoc, ht, Category.assoc, X.homOfLE_homOfLE]`. Establish `hpb : ∀ (U V : S) (h : U.1 ≤ V.1), IsPullback (t U V h) (c U) (c V) (X.homOfLE h)` using `fun U V h ↦ by`. Use `⟨⟨ht _ _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s`. Rewrite using `[← cancel_mono (c V), Category.assoc, ht, ← Category.assoc, ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec, s.condition]`.

Introduce `s`. Conclude with `((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec`. Introduce `s m _ h2`. Rewrite using `[← cancel_mono (c U), h2, ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec]`. Use `letI := locallyDirected S hcov hinf`.

Set `d : (coverOfSet S hcov).RelativeGluingData` to `{ functor := { obj := C map := fun {U V} h ↦ t U V h.le map_id := hid map_comp := fun {U V W} h k ↦ hcomp U V W h.le k.le } natTrans := { app := c, naturality := fun U V h ↦ ht U V h.le } equifibered := fun {U V} h ↦ hpb U V h.le }`. Conclude with `⟨d.glued, d.toBase, d.cover.f, d.isPullback_natTrans_ι_toBase⟩`.
-/
theorem exists_glue {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)
    (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) (C : S → Scheme.{0}) (c : ∀ U, C U ⟶ U.1.toScheme)
    [∀ U, Mono (c U)]
    (H : ∀ (U V : S) (h : U.1 ≤ V.1) (Y : Scheme.{0}) (g : Y ⟶ U.1.toScheme),
      (∃ z : Y ⟶ C U, z ≫ c U = g) ↔ ∃ z : Y ⟶ C V, z ≫ c V = g ≫ X.homOfLE h) :
    ∃ (B : Scheme.{0}) (b : B ⟶ X) (e : ∀ U, C U ⟶ B), ∀ U, IsPullback (c U) (e U) U.1.ι b := by
  choose t ht using fun (U V : S) (h : U.1 ≤ V.1) ↦ (H U V h _ (c U)).1 ⟨𝟙 _, Category.id_comp _⟩
  have hid : ∀ U : S, t U U le_rfl = 𝟙 _ := fun U ↦ by
    rw [← cancel_mono (c U), ht, X.homOfLE_rfl]; simp
  have hcomp : ∀ (U V W : S) (h : U.1 ≤ V.1) (k : V.1 ≤ W.1),
      t U W (h.trans k) = t U V h ≫ t V W k := fun U V W h k ↦ by
    rw [← cancel_mono (c W), ht, Category.assoc, ht, ← Category.assoc, ht, Category.assoc,
      X.homOfLE_homOfLE]
  have hpb : ∀ (U V : S) (h : U.1 ≤ V.1),
      IsPullback (t U V h) (c U) (c V) (X.homOfLE h) := fun U V h ↦ by
    refine ⟨⟨ht _ _ _⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
    · intro s
      rw [← cancel_mono (c V), Category.assoc, ht, ← Category.assoc,
        ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec, s.condition]
    · intro s
      exact ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec
    · intro s m _ h2
      rw [← cancel_mono (c U), h2, ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec]
  letI := locallyDirected S hcov hinf
  let d : (coverOfSet S hcov).RelativeGluingData :=
    { functor :=
        { obj := C
          map := fun {U V} h ↦ t U V h.le
          map_id := hid
          map_comp := fun {U V W} h k ↦ hcomp U V W h.le k.le }
      natTrans := { app := c, naturality := fun U V h ↦ ht U V h.le }
      equifibered := fun {U V} h ↦ hpb U V h.le }
  exact ⟨d.glued, d.toBase, d.cover.f, d.isPullback_natTrans_ι_toBase⟩

/- English proof (translation)
Introduce `X ι Xi m hm hcov A a ha hcomp`. Set `S : Set X.Opens` to `{U | ∃ i, U ≤ (m i).opensRange}`. Establish `hS : ∀ x : X, ∃ U ∈ S, x ∈ U` using `fun x ↦ by`. Take `⟨i, hi⟩` from `hcov x`. Conclude with `⟨(m i).opensRange, ⟨i, le_rfl⟩, hi⟩`.

Establish `hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S` using `fun U ⟨i, hi⟩ V _ ↦ ⟨i, inf_le_left.trans hi⟩`. Establish `hl : ∀ (U : X.Opens) (i : ι), U ≤ (m i).opensRange → ∃ l : U.toScheme ⟶ Xi i, l ≫ m i = U.ι` using `fun U i h ↦ ⟨IsOpenImmersion.lift (m i) U.ι (by rw [Scheme.Opens.range_ι]; exact h), IsOpenImmersion.lift_fac _ _ _⟩`. Use `choose l hl using hl`. Establish `hC : ∀ U : S, ∃ (C : Scheme.{0}) (c : C ⟶ U.1.toScheme), IsClosedImmersion c ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (h : Y ⟶ U.1.toScheme), h ≫ U.1.ι = g ≫ m i → ((∃ z : Y ⟶ C, z ≫ c = h) ↔ ∃ z : Y ⟶ A i, z ≫ a i = g)`. Introduce and unpack `⟨U, j, hj⟩`.

Use `⟨pullback (a j) (l U j hj), pullback.snd _ _, inferInstance, fun i Y g h hg ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomp j i Y (h ≫ l U j hj) g (by rw [Category.assoc, hl, hg])]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z ≫ pullback.fst _ _, by simp [pullback.condition]⟩`.

Introduce and unpack `⟨z, hz⟩`. Conclude with `⟨pullback.lift z h hz, pullback.lift_snd _ _ _⟩`. Use `choose C c hc hCa using hC`. Take `⟨B, b, e, he⟩` from `exists_glue S hS hinf C c (by`. Introduce `U V h Y g`.

Take `⟨i, hi⟩` from `V.2`. Rewrite using `[hCa U i Y (g ≫ l U.1 i (h.trans hi)) g (by rw [Category.assoc, hl]), hCa V i Y (g ≫ l U.1 i (h.trans hi)) (g ≫ X.homOfLE h) (by rw [Category.assoc, Category.assoc, hl, X.homOfLE_ι])])`. Use `⟨B, b, ?_, fun i Y g ↦ ?_⟩` and prove the remaining obligations. Apply `IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (coverOfSet S hS)` to reduce the goal to its premises. Introduce `U`.

Use `hc U` as an intermediate fact. Express the relevant statement in the definitionally equal form `IsClosedImmersion (pullback.snd b U.1.ι)`. Rewrite using `[← (he U).flip.isoPullback_inv_snd]`. Use `infer_instance`. Set `U : S` to `⟨(m i).opensRange, i, le_rfl⟩`.

Establish `hh : (g ≫ (m i).isoOpensRange.hom) ≫ U.1.ι = g ≫ m i` using `by simp [U]`. Rewrite using `[← hCa U i Y g _ hh]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Conclude with `⟨(he U).lift _ z (hh.trans hz.symm), (he U).lift_fst _ _ _⟩`.

Introduce and unpack `⟨z, hz⟩`. Conclude with `⟨z ≫ e U, by rw [Category.assoc, ← (he U).w, ← Category.assoc, hz, hh]⟩`.
-/
theorem exists_glue_isClosedImmersion : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by
  intro X ι Xi m hm hcov A a ha hcomp
  let S : Set X.Opens := {U | ∃ i, U ≤ (m i).opensRange}
  have hS : ∀ x : X, ∃ U ∈ S, x ∈ U := fun x ↦ by
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨(m i).opensRange, ⟨i, le_rfl⟩, hi⟩
  have hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S := fun U ⟨i, hi⟩ V _ ↦ ⟨i, inf_le_left.trans hi⟩
  have hl : ∀ (U : X.Opens) (i : ι), U ≤ (m i).opensRange →
      ∃ l : U.toScheme ⟶ Xi i, l ≫ m i = U.ι := fun U i h ↦
    ⟨IsOpenImmersion.lift (m i) U.ι (by rw [Scheme.Opens.range_ι]; exact h),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose l hl using hl
  have hC : ∀ U : S, ∃ (C : Scheme.{0}) (c : C ⟶ U.1.toScheme), IsClosedImmersion c ∧
      ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (h : Y ⟶ U.1.toScheme), h ≫ U.1.ι = g ≫ m i →
        ((∃ z : Y ⟶ C, z ≫ c = h) ↔ ∃ z : Y ⟶ A i, z ≫ a i = g) := by
    rintro ⟨U, j, hj⟩
    refine ⟨pullback (a j) (l U j hj), pullback.snd _ _, inferInstance, fun i Y g h hg ↦ ?_⟩
    rw [← hcomp j i Y (h ≫ l U j hj) g (by rw [Category.assoc, hl, hg])]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z ≫ pullback.fst _ _, by simp [pullback.condition]⟩
    · rintro ⟨z, hz⟩
      exact ⟨pullback.lift z h hz, pullback.lift_snd _ _ _⟩
  choose C c hc hCa using hC
  obtain ⟨B, b, e, he⟩ := exists_glue S hS hinf C c (by
    intro U V h Y g
    obtain ⟨i, hi⟩ := V.2
    rw [hCa U i Y (g ≫ l U.1 i (h.trans hi)) g (by rw [Category.assoc, hl]),
      hCa V i Y (g ≫ l U.1 i (h.trans hi)) (g ≫ X.homOfLE h)
        (by rw [Category.assoc, Category.assoc, hl, X.homOfLE_ι])])
  refine ⟨B, b, ?_, fun i Y g ↦ ?_⟩
  · apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (coverOfSet S hS)
    intro U
    have := hc U
    change IsClosedImmersion (pullback.snd b U.1.ι)
    rw [← (he U).flip.isoPullback_inv_snd]
    infer_instance
  · let U : S := ⟨(m i).opensRange, i, le_rfl⟩
    have hh : (g ≫ (m i).isoOpensRange.hom) ≫ U.1.ι = g ≫ m i := by simp [U]
    rw [← hCa U i Y g _ hh]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(he U).lift _ z (hh.trans hz.symm), (he U).lift_fst _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ e U, by rw [Category.assoc, ← (he U).w, ← Category.assoc, hz, hh]⟩

end GlobalTheory.GlueClosed
