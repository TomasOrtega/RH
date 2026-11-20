import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram

noncomputable section

namespace GlobalTheory.OmitGlue

open CategoryTheory Limits AlgebraicGeometry GlobalTheory GlobalTheory.VB GlobalTheory.Vert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Cat

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

private def Le (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ u : A ⟶ B, u ≫ g = f

private def Same (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ e : A ≅ B, e.hom ≫ g = f

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

/- English proof (translation)
Assemble the required witnesses or components as `⟨𝟙 _, Category.id_comp _⟩`.
-/
private theorem Le.refl (f : A ⟶ E) : Le f f := ⟨𝟙 _, Category.id_comp _⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Take `⟨v, rfl⟩` from `h'`. Conclude with `⟨u ≫ v, Category.assoc ..⟩`.
-/
private theorem Le.trans (h : Le f g) (h' : Le g f') : Le f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≫ v, Category.assoc ..⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Conclude with `⟨u, (Category.assoc ..).symm⟩`.
-/
private theorem Le.comp (h : Le f g) (t : E ⟶ E') : Le (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨u, rfl⟩`.
-/
private theorem le_comp (u : A ⟶ B) (g : B ⟶ E) : Le (u ≫ g) g := ⟨u, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨Iso.refl _, Category.id_comp _⟩`.
-/
private theorem Same.refl (f : A ⟶ E) : Same f f := ⟨Iso.refl _, Category.id_comp _⟩

/- English proof (translation)
The claim follows from `h ▸ .refl f`.
-/
private theorem Same.of_eq {f f' : A ⟶ E} (h : f = f') : Same f f' := h ▸ .refl f

/- English proof (translation)
Take `⟨e, rfl⟩` from `h`. Conclude with `⟨e.symm, e.inv_hom_id_assoc _⟩`.
-/
private theorem Same.symm (h : Same f g) : Same g f := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, e.inv_hom_id_assoc _⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Take `⟨v, rfl⟩` from `h'`. Conclude with `⟨u ≪≫ v, Category.assoc ..⟩`.
-/
private theorem Same.trans (h : Same f g) (h' : Same g f') : Same f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≪≫ v, Category.assoc ..⟩

/- English proof (translation)
The claim follows from `h.elim fun e he => ⟨e.hom, he⟩`.
-/
private theorem Same.le (h : Same f g) : Le f g := h.elim fun e he => ⟨e.hom, he⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Conclude with `⟨F.mapIso u, (F.map_comp ..).symm⟩`.
-/
private theorem Same.map (h : Same f g) (F : C ⥤ C') : Same (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.mapIso u, (F.map_comp ..).symm⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Conclude with `⟨u, (Category.assoc ..).symm⟩`.
-/
private theorem Same.comp (h : Same f g) (t : E ⟶ E') : Same (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Conclude with `⟨u, by rw [← cancel_mono t, Category.assoc, hu]⟩`.
-/
private theorem Same.of_comp (t : E ⟶ E') [Mono t] (h : Same (f ≫ t) (g ≫ t)) : Same f g := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [← cancel_mono t, Category.assoc, hu]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨asIso u, rfl⟩`.
-/
private theorem same_isIso_comp (u : A ⟶ B) [IsIso u] (g : B ⟶ E) : Same (u ≫ g) g := ⟨asIso u, rfl⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Take `⟨v, hv⟩` from `h'`. Conclude with `⟨⟨u, v, by rw [← cancel_mono f, Category.assoc, hv, hu, Category.id_comp], by rw [← cancel_mono g, Category.assoc, hu, hv, Category.id_comp]⟩, hu⟩`.
-/
private theorem Same.of_le [Mono f] [Mono g] (h : Le f g) (h' : Le g f) : Same f g := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv⟩ := h'
  exact ⟨⟨u, v, by rw [← cancel_mono f, Category.assoc, hv, hu, Category.id_comp],
    by rw [← cancel_mono g, Category.assoc, hu, hv, Category.id_comp]⟩, hu⟩

private def Ov {P E Q M K : C} (j : P ⟶ E) (q : E ⟶ Q) (μ : M ⟶ E) (κ : K ⟶ Q) : Prop :=
  Le j μ ∧ ∃ g : M ⟶ K, g ≫ κ = μ ≫ q ∧ Epi g

/- English proof (translation)
Take `⟨⟨u, rfl⟩, g, hg, _⟩` from `h`. Use `⟨h₁.trans ⟨F.map u, by simp⟩, F.map g, ?_, inferInstance⟩` and prove the remaining obligations. Rewrite using `[← F.map_comp_assoc, hg, Category.assoc, h₂, F.map_comp_assoc]`.
-/
private theorem Ov.map {P E Q M K : C} {j : P ⟶ E} {q : E ⟶ Q} {μ : M ⟶ E} {κ : K ⟶ Q} (h : Ov j q μ κ)
    (F : C ⥤ C') [F.PreservesEpimorphisms] {P' E' Q' : C'} {j' : P' ⟶ E'} {q' : E' ⟶ Q'}
    (β : F.obj E ⟶ E') (χ : F.obj Q ⟶ Q') (h₁ : Le j' (F.map j ≫ β)) (h₂ : β ≫ q' = F.map q ≫ χ) :
    Ov j' q' (F.map μ ≫ β) (F.map κ ≫ χ) := by
  obtain ⟨⟨u, rfl⟩, g, hg, _⟩ := h
  refine ⟨h₁.trans ⟨F.map u, by simp⟩, F.map g, ?_, inferInstance⟩
  rw [← F.map_comp_assoc, hg, Category.assoc, h₂, F.map_comp_assoc]

/- English proof (translation)
Take `⟨hl, g, hg, _⟩` from `h`. Take `⟨e, rfl⟩` from `h₁.symm`. Take `⟨e', rfl⟩` from `h₂`. Conclude with `⟨hl.trans ⟨e.inv, by simp⟩, e.hom ≫ g ≫ e'.hom, by simp [← hg], inferInstance⟩`.
-/
private theorem Ov.of_same {P E Q M K M' K' : C} {j : P ⟶ E} {q : E ⟶ Q} {μ : M ⟶ E} {κ : K ⟶ Q} {μ' : M' ⟶ E}
    {κ' : K' ⟶ Q} (h : Ov j q μ κ) (h₁ : Same μ μ') (h₂ : Same κ κ') : Ov j q μ' κ' := by
  obtain ⟨hl, g, hg, _⟩ := h
  obtain ⟨e, rfl⟩ := h₁.symm
  obtain ⟨e', rfl⟩ := h₂
  exact ⟨hl.trans ⟨e.inv, by simp⟩, e.hom ≫ g ≫ e'.hom, by simp [← hg], inferInstance⟩

end Cat

section Ab

variable {C : Type*} [Category C] [Abelian C] {P E Q M K M' K' : C} {j : P ⟶ E} {q : E ⟶ Q}
  {μ : M ⟶ E} {κ : K ⟶ Q} {μ' : M' ⟶ E} {κ' : K' ⟶ Q}

private def Cok (j : P ⟶ E) (q : E ⟶ Q) : Prop :=
  j ≫ q = 0 ∧ Epi q ∧ ∀ (Z : C) (b : E ⟶ Z), j ≫ b = 0 → ∃ a, q ≫ a = b

/- English proof (translation)
Assemble the required witnesses or components as `⟨cokernel.condition j, inferInstance, fun _ b hb => ⟨cokernel.desc j b hb, cokernel.π_desc ..⟩⟩`.
-/
private theorem cok_π (j : P ⟶ E) : Cok j (cokernel.π j) :=
  ⟨cokernel.condition j, inferInstance, fun _ b hb => ⟨cokernel.desc j b hb, cokernel.π_desc ..⟩⟩

/- English proof (translation)
Take `⟨h₀, _, h₁⟩` from `h`. Take `⟨a, ha⟩` from `h₁ _ _ (cokernel.condition j)`. Conclude with `⟨cokernel.desc j q h₀, a, by rw [← cancel_epi (cokernel.π j)]; simp [ha], by rw [← cancel_epi q, reassoc_of% ha]; simp⟩`.
-/
private theorem Cok.nonempty_iso (h : Cok j q) : Nonempty (cokernel j ≅ Q) := by
  obtain ⟨h₀, _, h₁⟩ := h
  obtain ⟨a, ha⟩ := h₁ _ _ (cokernel.condition j)
  exact ⟨cokernel.desc j q h₀, a, by rw [← cancel_epi (cokernel.π j)]; simp [ha],
    by rw [← cancel_epi q, reassoc_of% ha]; simp⟩

/- English proof (translation)
Use `h.2.1` as an intermediate fact. Use `choose a ha using h.2.2`. Conclude with `ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ _ _ (fun b hb => a _ b hb) (fun b hb => ha _ b hb) fun b hb m hm => by rw [← cancel_epi q, hm, ha])`.
-/
private theorem Cok.exact (h : Cok j q) : (ShortComplex.mk j q h.1).Exact := by
  have := h.2.1
  choose a ha using h.2.2
  exact ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ _ _ (fun b hb => a _ b hb)
    (fun b hb => ha _ b hb) fun b hb m hm => by rw [← cancel_epi q, hm, ha])

/- English proof (translation)
The claim follows from `(ShortComplex.exact_cokernel μ').lift' _ h`.
-/
private theorem le_of_comp_π [Mono μ'] (h : μ ≫ cokernel.π μ' = 0) : Le μ μ' :=
  (ShortComplex.exact_cokernel μ').lift' _ h

/- English proof (translation)
Take `⟨⟨u, rfl⟩, g, hg, _⟩` from `h`. Take `⟨h₀, _, h₁⟩` from `hq`. Use `⟨by rw [← reassoc_of% hg]; simp, inferInstance, fun Z b hb => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `h₁ Z b (by rw [Category.assoc, hb, comp_zero])`. Conclude with `⟨cokernel.desc κ a (by rw [← cancel_epi g, reassoc_of% hg, hb, comp_zero]), by simp⟩`.
-/
private theorem Ov.cok (h : Ov j q μ κ) (hq : Cok j q) : Cok μ (q ≫ cokernel.π κ) := by
  obtain ⟨⟨u, rfl⟩, g, hg, _⟩ := h
  obtain ⟨h₀, _, h₁⟩ := hq
  refine ⟨by rw [← reassoc_of% hg]; simp, inferInstance, fun Z b hb => ?_⟩
  obtain ⟨a, rfl⟩ := h₁ Z b (by rw [Category.assoc, hb, comp_zero])
  exact ⟨cokernel.desc κ a (by rw [← cancel_epi g, reassoc_of% hg, hb, comp_zero]), by simp⟩

/- English proof (translation)
The claim follows from `(h.cok hq).nonempty_iso`.
-/
private theorem Ov.nonempty_iso (h : Ov j q μ κ) (hq : Cok j q) : Nonempty (cokernel μ ≅ cokernel κ) :=
  (h.cok hq).nonempty_iso

/- English proof (translation)
Take `⟨-, g, hg, _⟩` from `h`. Take `⟨-, g', hg', _⟩` from `h'`. Take `⟨u, rfl⟩` from `H`. Use `le_of_comp_π ?_` and prove the remaining obligations. Rewrite using `[← cancel_epi g, reassoc_of% hg, ← reassoc_of% hg']`.

Simplify using the standard rewrite rules.
-/
private theorem Ov.le_of_le [Mono κ'] (h : Ov j q μ κ) (h' : Ov j q μ' κ') (H : Le μ μ') : Le κ κ' := by
  obtain ⟨-, g, hg, _⟩ := h
  obtain ⟨-, g', hg', _⟩ := h'
  obtain ⟨u, rfl⟩ := H
  refine le_of_comp_π ?_
  rw [← cancel_epi g, reassoc_of% hg, ← reassoc_of% hg']
  simp

/- English proof (translation)
Take `⟨a, ha⟩` from `(h'.cok hq).2.2 _ _ (cokernel.condition μ')`. Take `⟨-, g, hg, _⟩` from `h`. Take `⟨u, rfl⟩` from `H`. Use `le_of_comp_π ?_` and prove the remaining obligations. Rewrite using `[← ha, Category.assoc, ← reassoc_of% hg]`.

Simplify using the standard rewrite rules.
-/
private theorem Ov.le_of_le' [Mono μ'] (hq : Cok j q) (h : Ov j q μ κ) (h' : Ov j q μ' κ') (H : Le κ κ') :
    Le μ μ' := by
  obtain ⟨a, ha⟩ := (h'.cok hq).2.2 _ _ (cokernel.condition μ')
  obtain ⟨-, g, hg, _⟩ := h
  obtain ⟨u, rfl⟩ := H
  refine le_of_comp_π ?_
  rw [← ha, Category.assoc, ← reassoc_of% hg]
  simp

/- English proof (translation)
Use `hq.2.1` as an intermediate fact. Conclude with `⟨pullback q κ, pullback.fst q κ, inferInstance, ⟨pullback.lift j 0 (by simp [hq.1]), by simp⟩, pullback.snd q κ, pullback.condition.symm, inferInstance⟩`.
-/
private theorem exists_ov [Mono κ] (hq : Cok j q) : ∃ (M : C) (μ : M ⟶ E), Mono μ ∧ Ov j q μ κ := by
  have := hq.2.1
  exact ⟨pullback q κ, pullback.fst q κ, inferInstance, ⟨pullback.lift j 0 (by simp [hq.1]), by simp⟩,
    pullback.snd q κ, pullback.condition.symm, inferInstance⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, image.ι (μ ≫ q), inferInstance, h, factorThruImage _, image.fac _, inferInstance⟩`.
-/
private theorem exists_ov' (q : E ⟶ Q) (h : Le j μ) : ∃ (K : C) (κ : K ⟶ Q), Mono κ ∧ Ov j q μ κ :=
  ⟨_, image.ι (μ ≫ q), inferInstance, h, factorThruImage _, image.fac _, inferInstance⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨.refl _, 0, by simp [hq.1], h.epi _⟩`.
-/
private theorem ov_of_isZero (hq : Cok j q) (h : IsZero K) (κ : K ⟶ Q) : Ov j q j κ :=
  ⟨.refl _, 0, by simp [hq.1], h.epi _⟩

/- English proof (translation)
Establish `e : F.map (cokernel.π j) = cokernel.π (F.map j) ≫ (PreservesCokernel.iso F j).inv`. Rewrite using `[PreservesCokernel.iso_inv, π_comp_cokernelComparison]`. Rewrite using `[e]`. Use `⟨by simp [← F.map_comp], inferInstance, fun Z b hb => ⟨(PreservesCokernel.iso F j).hom ≫ cokernel.desc (F.map j) (β.hom ≫ b) (by simpa using hb), by simp⟩⟩` and prove the remaining obligations.
-/
private theorem Cok.map {C' : Type*} [Category C'] [Abelian C'] (F : C ⥤ C') [F.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair F] (j : P ⟶ E) {E' : C'} (β : F.obj E ≅ E') :
    Cok (F.map j ≫ β.hom) (β.inv ≫ F.map (cokernel.π j)) := by
  have e : F.map (cokernel.π j) = cokernel.π (F.map j) ≫ (PreservesCokernel.iso F j).inv := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  rw [e]
  refine ⟨by simp [← F.map_comp], inferInstance, fun Z b hb => ⟨(PreservesCokernel.iso F j).hom ≫
    cokernel.desc (F.map j) (β.hom ≫ b) (by simpa using hb), by simp⟩⟩

end Ab

section Bundles

variable {X : Scheme.{0}} {A B E E' S P Q E₁ M K : X.Modules} {a b r : ℕ}

/- English proof (translation)
Introduce `x` and use `by have : Nonempty X := ⟨x⟩ obtain ⟨_, s, hs⟩ := hg obtain rfl : s = r - b := by have := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk g (cokernel.π _) (cokernel.condition _)) b s { exact := ShortComplex.exact_cokernel _ } hB hs).1 omega exact hs x`.
-/
private theorem rank_cokernel {g : B ⟶ E} (hg : IsSubbundle g) (hB : IsVB B b) (hE : IsVB E r) :
    IsVB (cokernel g) (r - b) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨_, s, hs⟩ := hg
  obtain rfl : s = r - b := by
    have := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk g (cokernel.π _)
      (cokernel.condition _)) b s { exact := ShortComplex.exact_cokernel _ } hB hs).1
    omega
  exact hs x

/- English proof (translation)
The claim follows from `VB.isVB_X₁_of_shortExact X (.mk g (cokernel.π _) (cokernel.condition _)) b a { exact := ShortComplex.exact_cokernel _ } (h ▸ hE) hQ`.
-/
private theorem isVB_of_cokernel (g : B ⟶ E) [Mono g] (hE : IsVB E r) (hQ : IsVB (cokernel g) a) (h : r = b + a) :
    IsVB B b :=
  VB.isVB_X₁_of_shortExact X (.mk g (cokernel.π _) (cokernel.condition _)) b a
    { exact := ShortComplex.exact_cokernel _ } (h ▸ hE) hQ

/- English proof (translation)
Use `hu.mono` as an intermediate fact. Use `hg.mono` as an intermediate fact. Take `⟨s, hs⟩` from `hu.isVB_cokernel`. Take `⟨t, ht⟩` from `hg.isVB_cokernel`. Conclude with `⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _ (Vert.shortExact_cokernel_comp u g) hs ht).1⟩`.
-/
private theorem isSubbundle_comp {u : A ⟶ B} {g : B ⟶ E} (hu : IsSubbundle u) (hg : IsSubbundle g) :
    IsSubbundle (u ≫ g) := by
  have := hu.mono
  have := hg.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨t, ht⟩ := hg.isVB_cokernel
  exact ⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp u g) hs ht).1⟩

/- English proof (translation)
Substitute `w` using the available equality. Use `hg.mono` as an intermediate fact. Use `hf.mono` as an intermediate fact. Use `⟨mono_of_mono u g, b - a, VB.isVB_X₁_of_shortExact X _ _ _ (Vert.shortExact_cokernel_comp u g) ?_ (rank_cokernel hg hB hE)⟩` and prove the remaining obligations. Establish `h` using `rank_cokernel hf hA hE`.

Rewrite `h` using `[show r - a = b - a + (r - b) by omega]`. Then use the resulting hypothesis.
-/
private theorem isSubbundle_of_comp {u : A ⟶ B} {g : B ⟶ E} {f : A ⟶ E} (w : u ≫ g = f) (hf : IsSubbundle f)
    (hg : IsSubbundle g) (hA : IsVB A a) (hB : IsVB B b) (hE : IsVB E r) (h₁ : a ≤ b) (h₂ : b ≤ r) :
    IsSubbundle u := by
  subst w
  have := hg.mono
  have := hf.mono
  refine ⟨mono_of_mono u g, b - a, VB.isVB_X₁_of_shortExact X _ _ _ (Vert.shortExact_cokernel_comp u g) ?_
    (rank_cokernel hg hB hE)⟩
  have h := rank_cokernel hf hA hE
  rwa [show r - a = b - a + (r - b) by omega] at h

/- English proof (translation)
Use `hg.mono` as an intermediate fact. Establish `h` using `rank_cokernel hg hB hE`. Rewrite `h` using `[Nat.sub_self, isVB_zero_iff]`. Establish `: Epi g` using `Preadditive.epi_of_isZero_cokernel g h`. Conclude with `isIso_of_mono_of_epi g`.
-/
private theorem isIso_of_rank {g : B ⟶ E} (hg : IsSubbundle g) (hB : IsVB B r) (hE : IsVB E r) : IsIso g := by
  have := hg.mono
  have h := rank_cokernel hg hB hE
  rw [Nat.sub_self, isVB_zero_iff] at h
  have : Epi g := Preadditive.epi_of_isZero_cokernel g h
  exact isIso_of_mono_of_epi g

/- English proof (translation)
Use `choose A μ hs hv hΦ using h₁`. Use `choose st hst using fun l : Fin r => h₂ l _ _ _ _ (hs _).mono (hΦ _) (hΦ _)`. Conclude with `⟨⟨A, μ, hs, hv, st, hst, isIso_of_rank (hs _) (hv _) hE⟩, hΦ⟩`.
-/
private theorem exists_flag (hE : IsVB E r) (Φ : ∀ (_ : Fin (r + 1)) (A : X.Modules), (A ⟶ E) → Prop)
    (h₁ : ∀ l : Fin (r + 1), ∃ (A : X.Modules) (μ : A ⟶ E), IsSubbundle μ ∧ IsVB A (l : ℕ) ∧ Φ l A μ)
    (h₂ : ∀ (l : Fin r) (A A' : X.Modules) (μ : A ⟶ E) (μ' : A' ⟶ E), Mono μ' → Φ l.castSucc A μ → Φ l.succ A' μ' →
      Le μ μ') : ∃ fl : Flag E r, ∀ l, Φ l _ (fl.ι l) := by
  choose A μ hs hv hΦ using h₁
  choose st hst using fun l : Fin r => h₂ l _ _ _ _ (hs _).mono (hΦ _) (hΦ _)
  exact ⟨⟨A, μ, hs, hv, st, hst, isIso_of_rank (hs _) (hv _) hE⟩, hΦ⟩

/- English proof (translation)
Use `replace h : i ≤ j := h`. Proceed by induction on `j using Fin.induction with`. Consider the case `zero => obtain rfl := Fin.le_zero_iff.1 h`. Conclude with `.refl _`. Consider the case `succ j ih`.

Take `rfl | h'` from `h.eq_or_lt`. Conclude with `.refl _`. Conclude with `(ih (Fin.le_castSucc_iff.2 h')).trans ⟨fl.step j, fl.step_ι j⟩`.
-/
private theorem flag_le (fl : Flag E r) {i j : Fin (r + 1)} (h : (i : ℕ) ≤ j) : Le (fl.ι i) (fl.ι j) := by
  replace h : i ≤ j := h
  induction j using Fin.induction with
  | zero => obtain rfl := Fin.le_zero_iff.1 h; exact .refl _
  | succ j ih =>
    obtain rfl | h' := h.eq_or_lt
    · exact .refl _
    · exact (ih (Fin.le_castSucc_iff.2 h')).trans ⟨fl.step j, fl.step_ι j⟩

/- English proof (translation)
Use `hκ.mono` as an intermediate fact. Take `⟨M, μ, _, H⟩` from `exists_ov (κ := κ) hq`. Establish `hc` using `(rank_cokernel hκ hK hQ).of_iso (H.nonempty_iso hq).some.symm`. Conclude with `⟨M, μ, ⟨inferInstance, _, hc⟩, isVB_of_cokernel μ hE hc h, H⟩`.
-/
private theorem exists_ov_bundle {j : P ⟶ E} {q : E ⟶ Q} {κ : K ⟶ Q} (hq : Cok j q) (hκ : IsSubbundle κ)
    (hE : IsVB E r) {n k : ℕ} (hQ : IsVB Q n) (hK : IsVB K k) (h : r = a + (n - k)) :
    ∃ (M : X.Modules) (μ : M ⟶ E), IsSubbundle μ ∧ IsVB M a ∧ Ov j q μ κ := by
  have := hκ.mono
  obtain ⟨M, μ, _, H⟩ := exists_ov (κ := κ) hq
  have hc := (rank_cokernel hκ hK hQ).of_iso (H.nonempty_iso hq).some.symm
  exact ⟨M, μ, ⟨inferInstance, _, hc⟩, isVB_of_cokernel μ hE hc h, H⟩

/- English proof (translation)
Take `⟨K, κ, _, H⟩` from `exists_ov' q hl`. Establish `hc` using `(rank_cokernel hμ hM hE).of_iso (H.nonempty_iso hq).some`. Conclude with `⟨K, κ, ⟨inferInstance, _, hc⟩, isVB_of_cokernel κ hQ hc h, H⟩`.
-/
private theorem exists_ov_bundle' {j : P ⟶ E} {q : E ⟶ Q} {μ : M ⟶ E} (hq : Cok j q) (hμ : IsSubbundle μ) (hl : Le j μ)
    (hE : IsVB E r) {n k : ℕ} (hQ : IsVB Q n) (hM : IsVB M a) (h : n = k + (r - a)) :
    ∃ (K : X.Modules) (κ : K ⟶ Q), IsSubbundle κ ∧ IsVB K k ∧ Ov j q μ κ := by
  obtain ⟨K, κ, _, H⟩ := exists_ov' q hl
  have hc := (rank_cokernel hμ hM hE).of_iso (H.nonempty_iso hq).some
  exact ⟨K, κ, ⟨inferInstance, _, hc⟩, isVB_of_cokernel κ hQ hc h, H⟩

end Bundles

section Part

variable {X : Scheme.{0}} {A A' E S P Q E₁ : X.Modules} {n i : ℕ}

private def SameFl {r : ℕ} (f f' : Flag E r) : Prop := ∀ l, Same (f.ι l) (f'.ι l)

/- English proof (translation)
Introduce `l` and use `(h l).symm`.
-/
private theorem SameFl.symm {r : ℕ} {f f' : Flag E r} (h : SameFl f f') : SameFl f' f := fun l => (h l).symm

/- English proof (translation)
Introduce `l` and use `(h l).trans (h' l)`.
-/
private theorem SameFl.trans {r : ℕ} {f f' f'' : Flag E r} (h : SameFl f f') (h' : SameFl f' f'') : SameFl f f'' :=
  fun l => (h l).trans (h' l)

private structure Dat (s : S ⟶ P) (j : P ⟶ E) (q : E ⟶ Q) (t : P ⟶ E₁) (n i : ℕ) : Prop where
  hs : IsSubbundle s
  hj : IsSubbundle j
  hq : Cok j q
  ht : Cok s t
  hE : IsVB E n
  hS : IsVB S i
  hP : IsVB P (i + 2)
  le : i + 2 ≤ n

variable {s : S ⟶ P} {j : P ⟶ E} {q : E ⟶ Q} {t : P ⟶ E₁}

/- English proof (translation)
The claim follows from `(rank_cokernel D.hj D.hP D.hE).of_iso D.hq.nonempty_iso.some`.
-/
private theorem Dat.hQ (D : Dat s j q t n i) : IsVB Q (n - (i + 2)) :=
  (rank_cokernel D.hj D.hP D.hE).of_iso D.hq.nonempty_iso.some

/- English proof (translation)
Simplify using `using (rank_cokernel D.hs D.hS D.hP).of_iso D.ht.nonempty_iso.some`.
-/
private theorem Dat.hE₁ (D : Dat s j q t n i) : IsVB E₁ 2 := by
  simpa using (rank_cokernel D.hs D.hS D.hP).of_iso D.ht.nonempty_iso.some

variable (s j q t) in

private def PartAt (fS : Flag S i) (fQ : Flag Q (n - (i + 2))) (l : ℕ) (μ : A ⟶ E) : Prop :=
  (∀ m : Fin (i + 1), (m : ℕ) = l → Same μ (fS.ι m ≫ s ≫ j)) ∧
    ∀ m : Fin (n - (i + 2) + 1), i + 2 + m = l → Ov j q μ (fQ.ι m)

variable (s j t) in

private def MidAt (f₁ : Flag E₁ 2) (μ : A ⟶ E) : Prop := ∃ x : A ⟶ P, x ≫ j = μ ∧ Ov s t x (f₁.ι 1)

variable {fS fS' : Flag S i} {fQ fQ' : Flag Q (n - (i + 2))} {f₁ f₁' : Flag E₁ 2} {l l' : ℕ} {μ : A ⟶ E}
  {μ' : A' ⟶ E}

/- English proof (translation)
The claim follows from `(h.1 (Fin.last i) rfl).trans (same_isIso_comp _ _)`.
-/
private theorem PartAt.same_S (h : PartAt s j q fS fQ i μ) : Same μ (s ≫ j) :=
  (h.1 (Fin.last i) rfl).trans (same_isIso_comp _ _)

/- English proof (translation)
Use `D.hj.mono` as an intermediate fact. Establish `h₀` using `h.2 0 rfl`. Conclude with `.of_le (h₀.le_of_le' D.hq (ov_of_isZero D.hq (isVB_zero_iff.1 (fQ.isVB 0)) _) (.refl _)) h₀.1`.
-/
private theorem PartAt.same_P (D : Dat s j q t n i) [Mono μ] (h : PartAt s j q fS fQ (i + 2) μ) : Same μ j := by
  have := D.hj.mono
  have h₀ := h.2 0 rfl
  exact .of_le (h₀.le_of_le' D.hq (ov_of_isZero D.hq (isVB_zero_iff.1 (fQ.isVB 0)) _) (.refl _)) h₀.1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun m hm => H.symm.trans (h.1 m hm), fun m hm => (h.2 m hm).of_same H (.refl _)⟩`.
-/
private theorem PartAt.of_same (h : PartAt s j q fS fQ l μ) (H : Same μ μ') : PartAt s j q fS fQ l μ' :=
  ⟨fun m hm => H.symm.trans (h.1 m hm), fun m hm => (h.2 m hm).of_same H (.refl _)⟩

/- English proof (translation)
Use `D.le` as an intermediate fact. Distinguish the cases in `h : l ≤ i`. Use `⟨_, fS.ι ⟨l, by omega⟩ ≫ s ≫ j, isSubbundle_comp (fS.isSubbundle _) (isSubbundle_comp D.hs D.hj), fS.isVB _, fun m hm => ?_, fun m hm => by omega⟩` and prove the remaining obligations. Substitute `hm` using the available equality. Conclude with `.refl _`.

Take `⟨m, rfl⟩ : ∃ m : Fin (n - (i + 2) + 1), l = i + 2 + m` from `⟨⟨l - (i + 2), by omega⟩, by simp; omega⟩`. Take `⟨M, μ, h₃, h₄, h₅⟩` from `exists_ov_bundle (a := i + 2 + m) D.hq (fQ.isSubbundle m) D.hE D.hQ (fQ.isVB m) (by omega)`. Use `⟨M, μ, h₃, h₄, fun m' hm => by omega, fun m' hm => ?_⟩` and prove the remaining obligations. Take `rfl : m' = m` from `Fin.ext (by omega)`. Conclude with `h₅`.
-/
private theorem exists_partAt (D : Dat s j q t n i) (fS : Flag S i) (fQ : Flag Q (n - (i + 2))) (h₁ : l ≤ n)
    (h₂ : l ≠ i + 1) : ∃ (A : X.Modules) (μ : A ⟶ E), IsSubbundle μ ∧ IsVB A l ∧ PartAt s j q fS fQ l μ := by
  have := D.le
  by_cases h : l ≤ i
  · refine ⟨_, fS.ι ⟨l, by omega⟩ ≫ s ≫ j, isSubbundle_comp (fS.isSubbundle _) (isSubbundle_comp D.hs D.hj),
      fS.isVB _, fun m hm => ?_, fun m hm => by omega⟩
    subst hm
    exact .refl _
  · obtain ⟨m, rfl⟩ : ∃ m : Fin (n - (i + 2) + 1), l = i + 2 + m := ⟨⟨l - (i + 2), by omega⟩, by simp; omega⟩
    obtain ⟨M, μ, h₃, h₄, h₅⟩ := exists_ov_bundle (a := i + 2 + m) D.hq (fQ.isSubbundle m) D.hE D.hQ (fQ.isVB m)
      (by omega)
    refine ⟨M, μ, h₃, h₄, fun m' hm => by omega, fun m' hm => ?_⟩
    obtain rfl : m' = m := Fin.ext (by omega)
    exact h₅

/- English proof (translation)
Use `D.le` as an intermediate fact. Distinguish the cases in `a : l' ≤ i`. Conclude with `(h.1 ⟨l, by omega⟩ rfl).le.trans ((((hS _).le.trans (flag_le fS' (j := ⟨l', by omega⟩) h₀)).comp _).trans (h'.1 _ rfl).symm.le)`. Establish `b` using `h'.2 ⟨l' - (i + 2), by omega⟩ (by simp; omega)`. Distinguish the cases in `a' : l ≤ i`.

Conclude with `(h.1 ⟨l, by omega⟩ rfl).le.trans (((le_comp _ _).trans (le_comp _ _)).trans b.1)`. Conclude with `(h.2 ⟨l - (i + 2), by omega⟩ (by simp; omega)).le_of_le' D.hq b ((hQ _).le.trans (flag_le fQ' (by simp; omega)))`.
-/
private theorem PartAt.le (D : Dat s j q t n i) [Mono μ'] (h : PartAt s j q fS fQ l μ) (h' : PartAt s j q fS' fQ' l' μ')
    (hS : SameFl fS fS') (hQ : SameFl fQ fQ') (h₀ : l ≤ l') (h₁ : l' ≤ n) (h₂ : l ≠ i + 1) (h₃ : l' ≠ i + 1) :
    Le μ μ' := by
  have := D.le
  by_cases a : l' ≤ i
  · exact (h.1 ⟨l, by omega⟩ rfl).le.trans ((((hS _).le.trans (flag_le fS' (j := ⟨l', by omega⟩) h₀)).comp _).trans
      (h'.1 _ rfl).symm.le)
  have b := h'.2 ⟨l' - (i + 2), by omega⟩ (by simp; omega)
  by_cases a' : l ≤ i
  · exact (h.1 ⟨l, by omega⟩ rfl).le.trans (((le_comp _ _).trans (le_comp _ _)).trans b.1)
  · exact (h.2 ⟨l - (i + 2), by omega⟩ (by simp; omega)).le_of_le' D.hq b
      ((hQ _).le.trans (flag_le fQ' (by simp; omega)))

/- English proof (translation)
Take `⟨x, rfl, hx⟩` from `h`. Take `⟨x', rfl, hx'⟩` from `h'`. Use `mono_of_mono x' j` as an intermediate fact. Conclude with `(hx.le_of_le' D.ht hx' H).comp j`.
-/
private theorem MidAt.le (D : Dat s j q t n i) [Mono μ'] (h : MidAt s j t f₁ μ) (h' : MidAt s j t f₁' μ')
    (H : Le (f₁.ι 1) (f₁'.ι 1)) : Le μ μ' := by
  obtain ⟨x, rfl, hx⟩ := h
  obtain ⟨x', rfl, hx'⟩ := h'
  have := mono_of_mono x' j
  exact (hx.le_of_le' D.ht hx' H).comp j

/- English proof (translation)
Use `D.hj.mono` as an intermediate fact. Take `⟨x, rfl, hx⟩` from `h`. Take `⟨x', rfl, hx'⟩` from `h'`. Take `⟨u, hu⟩` from `H`. Conclude with `hx.le_of_le hx' ⟨u, by rw [← cancel_mono j, Category.assoc, hu]⟩`.
-/
private theorem MidAt.le' (D : Dat s j q t n i) (h : MidAt s j t f₁ μ) (h' : MidAt s j t f₁' μ')
    (H : Le μ μ') : Le (f₁.ι 1) (f₁'.ι 1) := by
  have := D.hj.mono
  obtain ⟨x, rfl, hx⟩ := h
  obtain ⟨x', rfl, hx'⟩ := h'
  obtain ⟨u, hu⟩ := H
  exact hx.le_of_le hx' ⟨u, by rw [← cancel_mono j, Category.assoc, hu]⟩

variable (s j q t) in

private def Glue (fl : Flag E n) (fS : Flag S i) (f₁ : Flag E₁ 2) (fQ : Flag Q (n - (i + 2))) : Prop :=
  ∀ l : Fin (n + 1), PartAt s j q fS fQ l (fl.ι l) ∧ ((l : ℕ) = i + 1 → MidAt s j t f₁ (fl.ι l))

/- English proof (translation)
Use `exists_flag D.hE (fun l A μ => PartAt s j q fS fQ l μ ∧ ((l : ℕ) = i + 1 → MidAt s j t f₁ μ)) (fun l => ?_) fun l A A' μ μ' _ h h' => ?_` and prove the remaining obligations. Distinguish the cases in `hl : (l : ℕ) = i + 1`. Take `⟨M, x, h₃, h₄, h₅⟩` from `exists_ov_bundle (a := i + 1) D.ht (f₁.isSubbundle 1) D.hP D.hE₁ (f₁.isVB 1) rfl`. Conclude with `⟨M, x ≫ j, isSubbundle_comp h₃ D.hj, hl ▸ h₄, ⟨fun m hm => by omega, fun m hm => by omega⟩, fun _ => ⟨x, rfl, h₅⟩⟩`. Take `⟨M, μ, h₃, h₄, h₅⟩` from `exists_partAt D fS fQ (l := l) (by omega) hl`.

Conclude with `⟨M, μ, h₃, h₄, h₅, fun h => (hl h).elim⟩`. Simplify using `only [Fin.val_castSucc, Fin.val_succ] at h h'`. Distinguish the cases in `a : (l : ℕ) = i`. Take `⟨x, rfl, hx, -⟩` from `h'.2 (by omega)`. Conclude with `(a ▸ h.1 : PartAt s j q fS fQ i μ).same_S.le.trans (hx.comp j)`.

Distinguish the cases in `b : (l : ℕ) = i + 1`. Take `⟨x, rfl, -⟩` from `h.2 b`. Conclude with `(le_comp _ _).trans (h'.1.2 0 (by simp; omega)).1`. Conclude with `h.1.le D h'.1 (fun _ => .refl _) (fun _ => .refl _) (by omega) (by omega) b (by omega)`.
-/
private theorem exists_glue (D : Dat s j q t n i) (fS : Flag S i) (f₁ : Flag E₁ 2) (fQ : Flag Q (n - (i + 2))) :
    ∃ fl : Flag E n, Glue s j q t fl fS f₁ fQ := by
  refine exists_flag D.hE (fun l A μ => PartAt s j q fS fQ l μ ∧ ((l : ℕ) = i + 1 → MidAt s j t f₁ μ))
    (fun l => ?_) fun l A A' μ μ' _ h h' => ?_
  · by_cases hl : (l : ℕ) = i + 1
    · obtain ⟨M, x, h₃, h₄, h₅⟩ := exists_ov_bundle (a := i + 1) D.ht (f₁.isSubbundle 1) D.hP D.hE₁ (f₁.isVB 1) rfl
      exact ⟨M, x ≫ j, isSubbundle_comp h₃ D.hj, hl ▸ h₄, ⟨fun m hm => by omega, fun m hm => by omega⟩,
        fun _ => ⟨x, rfl, h₅⟩⟩
    · obtain ⟨M, μ, h₃, h₄, h₅⟩ := exists_partAt D fS fQ (l := l) (by omega) hl
      exact ⟨M, μ, h₃, h₄, h₅, fun h => (hl h).elim⟩
  · simp only [Fin.val_castSucc, Fin.val_succ] at h h'
    by_cases a : (l : ℕ) = i
    · obtain ⟨x, rfl, hx, -⟩ := h'.2 (by omega)
      exact (a ▸ h.1 : PartAt s j q fS fQ i μ).same_S.le.trans (hx.comp j)
    by_cases b : (l : ℕ) = i + 1
    · obtain ⟨x, rfl, -⟩ := h.2 b
      exact (le_comp _ _).trans (h'.1.2 0 (by simp; omega)).1
    · exact h.1.le D h'.1 (fun _ => .refl _) (fun _ => .refl _) (by omega) (by omega) b (by omega)

open ZeroObject in
/- English proof (translation)
Use `D.le` as an intermediate fact. Use `D.hs.mono` as an intermediate fact. Use `D.hj.mono` as an intermediate fact. Take `⟨fS, hS⟩` from `exists_flag D.hS (fun m A ν => Same (fl.ι ⟨m, by omega⟩) (ν ≫ s ≫ j)) (fun m => by`. Take `⟨u, hu⟩` from `(flag_le fl (i := ⟨m, by omega⟩) (j := i₀) (by simp; omega)).trans h₀.symm.le`.

Conclude with `⟨_, u, isSubbundle_of_comp hu (fl.isSubbundle _) (isSubbundle_comp D.hs D.hj) (fl.isVB _) D.hS D.hE (by simp; omega) (by omega), fl.isVB _, .of_eq hu.symm⟩) (fun m A A' ν ν' _ h h' => by`. Take `⟨u, hu⟩` from `h.symm.le.trans ((flag_le fl (by simp)).trans h'.le)`. Conclude with `⟨u, by rw [← cancel_mono (s ≫ j), Category.assoc, hu]⟩)`. Take `⟨fQ, hQ⟩` from `exists_flag D.hQ (fun m A ν => Ov j q (fl.ι ⟨i + 2 + m, by omega⟩) ν) (fun m => exists_ov_bundle' (a := i + 2 + m) D.hq (fl.isSubbundle _) (h₂.le.trans (flag_le fl (j := ⟨i + 2 + m, by omega⟩) (by simp; omega))) D.hE D.hQ (fl.isVB _) (by omega)) fun m A A' ν ν' _ h h' => h.le_of_ …`. Take `⟨x, hx⟩` from `(flag_le fl (i := ⟨i + 1, by omega⟩) (j := i₂) (by simp; omega)).trans h₂.symm.le`.

Take `⟨y, hy⟩` from `h₀.le.trans (flag_le fl (j := ⟨i + 1, by omega⟩) (by simp; omega))`. Take `⟨K, κ, h₃, h₄, h₅⟩` from `exists_ov_bundle' (k := 1) D.ht (isSubbundle_of_comp hx (fl.isSubbundle _) D.hj (fl.isVB _) D.hP D.hE (by simp) D.le) ⟨y, by rw [← cancel_mono j, Category.assoc, hx, hy]⟩ D.hP D.hE₁ (fl.isVB _) (by simp)`. Take `⟨f₁, hf⟩` from `exists_flag D.hE₁ (fun m A ν => ((m : ℕ) = 0 → IsZero A) ∧ ((m : ℕ) = 1 → Same κ ν) ∧ ((m : ℕ) = 2 → IsIso ν)) (fun m => by fin_cases m`. Conclude with `⟨_, (0 : (0 : X.Modules) ⟶ E₁), ⟨(isZero_zero _).mono _, 2, D.hE₁.of_iso cokernelZeroIsoTarget.symm⟩, isVB_zero_iff.2 (isZero_zero _), fun _ => isZero_zero _, by simp, by simp⟩`. Conclude with `⟨K, κ, h₃, h₄, by simp, fun _ => .refl _, by simp⟩`.

Conclude with `⟨_, 𝟙 _, isSubbundle_of_isIso _, D.hE₁, by simp, by simp, fun _ => inferInstance⟩)`. Use the proof step `(fun m A A' ν ν' _ h h' => by fin_cases m`. Conclude with `⟨0, (h.1 rfl).eq_of_src _ _⟩`. Use `h'.2.2 rfl` as an intermediate fact. Conclude with `⟨ν ≫ inv ν', by simp⟩)`.

Use `⟨fS, f₁, fQ, fun ⟨l, _⟩ => ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun hl => ?_⟩⟩` and prove the remaining obligations. Take `rfl : (m : ℕ) = l` from `hm`. Conclude with `hS m`. Take `rfl : i + 2 + m = l` from `hm`. Conclude with `hQ m`.

Take `rfl : l = i + 1` from `hl`. Conclude with `⟨x, hx, h₅.of_same (.refl _) ((hf 1).2.1 rfl)⟩`.
-/
private theorem exists_split (D : Dat s j q t n i) (fl : Flag E n) {i₀ i₂ : Fin (n + 1)} (e₀ : (i₀ : ℕ) = i)
    (e₂ : (i₂ : ℕ) = i + 2) (h₀ : Same (s ≫ j) (fl.ι i₀)) (h₂ : Same j (fl.ι i₂)) :
    ∃ (fS : Flag S i) (f₁ : Flag E₁ 2) (fQ : Flag Q (n - (i + 2))), Glue s j q t fl fS f₁ fQ := by
  have := D.le
  have := D.hs.mono
  have := D.hj.mono
  obtain ⟨fS, hS⟩ := exists_flag D.hS (fun m A ν => Same (fl.ι ⟨m, by omega⟩) (ν ≫ s ≫ j)) (fun m => by
    obtain ⟨u, hu⟩ := (flag_le fl (i := ⟨m, by omega⟩) (j := i₀) (by simp; omega)).trans h₀.symm.le
    exact ⟨_, u, isSubbundle_of_comp hu (fl.isSubbundle _) (isSubbundle_comp D.hs D.hj) (fl.isVB _) D.hS D.hE
      (by simp; omega) (by omega), fl.isVB _, .of_eq hu.symm⟩) (fun m A A' ν ν' _ h h' => by
    obtain ⟨u, hu⟩ := h.symm.le.trans ((flag_le fl (by simp)).trans h'.le)
    exact ⟨u, by rw [← cancel_mono (s ≫ j), Category.assoc, hu]⟩)
  obtain ⟨fQ, hQ⟩ := exists_flag D.hQ (fun m A ν => Ov j q (fl.ι ⟨i + 2 + m, by omega⟩) ν) (fun m =>
    exists_ov_bundle' (a := i + 2 + m) D.hq (fl.isSubbundle _)
      (h₂.le.trans (flag_le fl (j := ⟨i + 2 + m, by omega⟩) (by simp; omega))) D.hE D.hQ (fl.isVB _)
      (by omega)) fun m A A' ν ν' _ h h' => h.le_of_le h' (flag_le fl (by simp))
  obtain ⟨x, hx⟩ := (flag_le fl (i := ⟨i + 1, by omega⟩) (j := i₂) (by simp; omega)).trans h₂.symm.le
  obtain ⟨y, hy⟩ := h₀.le.trans (flag_le fl (j := ⟨i + 1, by omega⟩) (by simp; omega))
  obtain ⟨K, κ, h₃, h₄, h₅⟩ := exists_ov_bundle' (k := 1) D.ht (isSubbundle_of_comp hx (fl.isSubbundle _) D.hj
    (fl.isVB _) D.hP D.hE (by simp) D.le) ⟨y, by rw [← cancel_mono j, Category.assoc, hx, hy]⟩ D.hP D.hE₁
    (fl.isVB _) (by simp)
  obtain ⟨f₁, hf⟩ := exists_flag D.hE₁ (fun m A ν => ((m : ℕ) = 0 → IsZero A) ∧ ((m : ℕ) = 1 → Same κ ν) ∧
    ((m : ℕ) = 2 → IsIso ν)) (fun m => by
      fin_cases m
      · exact ⟨_, (0 : (0 : X.Modules) ⟶ E₁), ⟨(isZero_zero _).mono _, 2, D.hE₁.of_iso cokernelZeroIsoTarget.symm⟩,
          isVB_zero_iff.2 (isZero_zero _), fun _ => isZero_zero _, by simp, by simp⟩
      · exact ⟨K, κ, h₃, h₄, by simp, fun _ => .refl _, by simp⟩
      · exact ⟨_, 𝟙 _, isSubbundle_of_isIso _, D.hE₁, by simp, by simp, fun _ => inferInstance⟩)
    (fun m A A' ν ν' _ h h' => by
      fin_cases m
      · exact ⟨0, (h.1 rfl).eq_of_src _ _⟩
      · have := h'.2.2 rfl
        exact ⟨ν ≫ inv ν', by simp⟩)
  refine ⟨fS, f₁, fQ, fun ⟨l, _⟩ => ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun hl => ?_⟩⟩
  · obtain rfl : (m : ℕ) = l := hm
    exact hS m
  · obtain rfl : i + 2 + m = l := hm
    exact hQ m
  · obtain rfl : l = i + 1 := hl
    exact ⟨x, hx, h₅.of_same (.refl _) ((hf 1).2.1 rfl)⟩

variable {fl fl' : Flag E n}

/- English proof (translation)
Introduce `l` and use `by by_cases hl : (l : ℕ) = i + 1 · exact .of_le (((h l).2 hl).le D ((h' l).2 hl) (h₁ 1).le) (((h' l).2 hl).le D ((h l).2 hl) (h₁ 1).symm.le) · exact .of_le ((h l).1.le D (h' l).1 hS hQ le_rfl (by omega) hl hl) ((h' l).1.le D (h l).1 hS.symm hQ.symm le_rfl (by omega) hl hl)`.
-/
private theorem Glue.sameFl (D : Dat s j q t n i) (h : Glue s j q t fl fS f₁ fQ) (h' : Glue s j q t fl' fS' f₁' fQ')
    (hS : SameFl fS fS') (h₁ : SameFl f₁ f₁') (hQ : SameFl fQ fQ') : SameFl fl fl' := fun l => by
  by_cases hl : (l : ℕ) = i + 1
  · exact .of_le (((h l).2 hl).le D ((h' l).2 hl) (h₁ 1).le) (((h' l).2 hl).le D ((h l).2 hl) (h₁ 1).symm.le)
  · exact .of_le ((h l).1.le D (h' l).1 hS hQ le_rfl (by omega) hl hl)
      ((h' l).1.le D (h l).1 hS.symm hQ.symm le_rfl (by omega) hl hl)

/- English proof (translation)
Use `D.le` as an intermediate fact. Use `D.hs.mono` as an intermediate fact. Use `D.hj.mono` as an intermediate fact. Use `⟨fun m => .of_comp (s ≫ j) ?_, fun m => ?_, fun m => ?_⟩` and prove the remaining obligations. Conclude with `((h ⟨m, by omega⟩).1.1 m rfl).symm.trans ((H _).trans ((h' _).1.1 m rfl))`.

Use `fin_cases m`. Establish `z` using `isVB_zero_iff.1 (f₁.isVB 0)`. Conclude with `⟨z.iso (isVB_zero_iff.1 (f₁'.isVB 0)), z.eq_of_src _ _⟩`. Establish `a` using `(h ⟨i + 1, by omega⟩).2 rfl`. Establish `a'` using `(h' ⟨i + 1, by omega⟩).2 rfl`.

Conclude with `.of_le (g := f₁'.ι 1) (a.le' D a' (H _).le) (a'.le' D a (H _).symm.le)`. Conclude with `⟨asIso (f₁.ι (Fin.last 2)) ≪≫ (asIso (f₁'.ι (Fin.last 2))).symm, by`. Express the relevant statement in the definitionally equal form `(f₁.ι (Fin.last 2) ≫ inv (f₁'.ι (Fin.last 2))) ≫ f₁'.ι (Fin.last 2) = f₁.ι (Fin.last 2)`. Use the proof step `simp⟩`. Establish `a` using `(h ⟨i + 2 + m, by omega⟩).1.2 m rfl`.

Establish `a'` using `(h' ⟨i + 2 + m, by omega⟩).1.2 m rfl`. Conclude with `.of_le (a.le_of_le a' (H _).le) (a'.le_of_le a (H _).symm.le)`.
-/
private theorem Glue.sameFl_parts (D : Dat s j q t n i) (h : Glue s j q t fl fS f₁ fQ) (h' : Glue s j q t fl' fS' f₁' fQ')
    (H : SameFl fl fl') : SameFl fS fS' ∧ SameFl f₁ f₁' ∧ SameFl fQ fQ' := by
  have := D.le
  have := D.hs.mono
  have := D.hj.mono
  refine ⟨fun m => .of_comp (s ≫ j) ?_, fun m => ?_, fun m => ?_⟩
  · exact ((h ⟨m, by omega⟩).1.1 m rfl).symm.trans ((H _).trans ((h' _).1.1 m rfl))
  · fin_cases m
    · have z := isVB_zero_iff.1 (f₁.isVB 0)
      exact ⟨z.iso (isVB_zero_iff.1 (f₁'.isVB 0)), z.eq_of_src _ _⟩
    · have a := (h ⟨i + 1, by omega⟩).2 rfl
      have a' := (h' ⟨i + 1, by omega⟩).2 rfl
      exact .of_le (g := f₁'.ι 1) (a.le' D a' (H _).le) (a'.le' D a (H _).symm.le)
    · exact ⟨asIso (f₁.ι (Fin.last 2)) ≪≫ (asIso (f₁'.ι (Fin.last 2))).symm, by
        change (f₁.ι (Fin.last 2) ≫ inv (f₁'.ι (Fin.last 2))) ≫ f₁'.ι (Fin.last 2) = f₁.ι (Fin.last 2)
        simp⟩
  · have a := (h ⟨i + 2 + m, by omega⟩).1.2 m rfl
    have a' := (h' ⟨i + 2 + m, by omega⟩).1.2 m rfl
    exact .of_le (a.le_of_le a' (H _).le) (a'.le_of_le a (H _).symm.le)

end Part

section Pull

open GlobalTheory.LineQuot GlobalTheory.CovTest GlobalTheory.OmitFlag

variable {T T' Y B G : Scheme.{0}}

private def pullTo {π : Y ⟶ B} {E : B.Modules} {r : ℕ} (fl : Flag ((Scheme.Modules.pullback π).obj E) r) (h : T ⟶ Y)
    {g : T ⟶ B} (w : h ≫ π = g) : Flag ((Scheme.Modules.pullback g).obj E) r :=
  (fl.pull h).ofIso ((cmp h π w).app E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pullTo_ι {π : Y ⟶ B} {E : B.Modules} {r : ℕ} (fl : Flag ((Scheme.Modules.pullback π).obj E) r) (h : T ⟶ Y)
    {g : T ⟶ B} (w : h ≫ π = g) (l : Fin (r + 1)) :
    (pullTo fl h w).ι l = (Scheme.Modules.pullback h).map (fl.ι l) ≫ (cmp h π w).hom.app E := rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem isFlagBundle_iff {π : Y ⟶ B} {ι : Type} {E : ι → B.Modules} {n : ι → ℕ}
    {fl : ∀ a, Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)} : IsFlagBundle π E n fl ↔
    ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
      ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a, SameFl (pullTo (fl a) g' w) (fl' a) := Iff.rfl

/- English proof (translation)
Introduce `l` and use `((H l).map (Scheme.Modules.pullback h)).comp _`.
-/
private theorem SameFl.pullTo {π : Y ⟶ B} {E : B.Modules} {r : ℕ} {fl fl' : Flag ((Scheme.Modules.pullback π).obj E) r}
    (H : SameFl fl fl') (h : T ⟶ Y) {g : T ⟶ B} (w : h ≫ π = g) : SameFl (pullTo fl h w) (pullTo fl' h w) :=
  fun l => ((H l).map (Scheme.Modules.pullback h)).comp _

/- English proof (translation)
Introduce `l` and use `⟨(cmp h' h w₁).app (fl.F l), by change (cmp h' h w₁).hom.app (fl.F l) ≫ (Scheme.Modules.pullback y).map (fl.ι l) ≫ (cmp y π w₂).hom.app E = (Scheme.Modules.pullback h').map ((Scheme.Modules.pullback h).map (fl.ι l) ≫ (cmp h π w).hom.app E) ≫ (cmp h' g w').hom.app E rw [Functor.ma …`.
-/
private theorem pullTo_pullTo {π : Y ⟶ B} {E : B.Modules} {r : ℕ} (fl : Flag ((Scheme.Modules.pullback π).obj E) r)
    (h : T ⟶ Y) {g : T ⟶ B} (w : h ≫ π = g) (h' : T' ⟶ T) {g' : T' ⟶ B} (w' : h' ≫ g = g') {y : T' ⟶ Y}
    (w₁ : h' ≫ h = y) (w₂ : y ≫ π = g') : SameFl (pullTo (pullTo fl h w) h' w') (pullTo fl y w₂) := fun l =>
  ⟨(cmp h' h w₁).app (fl.F l), by
    change (cmp h' h w₁).hom.app (fl.F l) ≫ (Scheme.Modules.pullback y).map (fl.ι l) ≫ (cmp y π w₂).hom.app E =
      (Scheme.Modules.pullback h').map ((Scheme.Modules.pullback h).map (fl.ι l) ≫ (cmp h π w).hom.app E) ≫
        (cmp h' g w').hom.app E
    rw [Functor.map_comp, Category.assoc, cmp_assoc h' h π w w' w₁ w₂, cmp_naturality_assoc]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h l => .of_comp e.hom (h l), fun h l => (h l).comp e.hom⟩`.
-/
private theorem sameFl_ofIso_iff {X : Scheme.{0}} {E E' : X.Modules} {r : ℕ} (e : E ≅ E') {f f' : Flag E r} :
    SameFl (f.ofIso e) (f'.ofIso e) ↔ SameFl f f' :=
  ⟨fun h l => .of_comp e.hom (h l), fun h l => (h l).comp e.hom⟩

/- English proof (translation)
Rewrite using `[← sameFl_ofIso_iff e]`. Establish `: SameFl ((f'.ofIso e.symm).ofIso e) f'` using `fun l => .of_eq (by simp [Flag.ofIso])`. Conclude with `⟨fun h => h.trans this, fun h => h.trans this.symm⟩`.
-/
private theorem sameFl_ofIso_symm_iff {X : Scheme.{0}} {E E' : X.Modules} {r : ℕ} (e : E ≅ E') {f : Flag E r}
    {f' : Flag E' r} : SameFl f (f'.ofIso e.symm) ↔ SameFl (f.ofIso e) f' := by
  rw [← sameFl_ofIso_iff e]
  have : SameFl ((f'.ofIso e.symm).ofIso e) f' := fun l => .of_eq (by simp [Flag.ofIso])
  exact ⟨fun h => h.trans this, fun h => h.trans this.symm⟩

/- English proof (translation)
Introduce `l` and use `.of_eq (by change ((Scheme.Modules.pullback h).map (fl.ι l) ≫ (cmp h τ wk).hom.app _) ≫ (cmp k γ w).hom.app E = (Scheme.Modules.pullback h).map (fl.ι l ≫ (cmp τ γ w₀).hom.app E) ≫ (cmp h π wg).hom.app E rw [Functor.map_comp, Category.assoc, Category.assoc, cmp_assoc h τ γ w₀ wg w …`.
-/
private theorem pullTo_ofIso {γ : G ⟶ B} {τ : Y ⟶ G} {π : Y ⟶ B} (w₀ : τ ≫ γ = π) {E : B.Modules} {r : ℕ}
    (fl : Flag ((Scheme.Modules.pullback τ).obj ((Scheme.Modules.pullback γ).obj E)) r)
    (h : T ⟶ Y) {k : T ⟶ G} (wk : h ≫ τ = k) {g : T ⟶ B} (w : k ≫ γ = g) (wg : h ≫ π = g) :
    SameFl ((pullTo fl h wk).ofIso ((cmp k γ w).app E)) (pullTo (fl.ofIso ((cmp τ γ w₀).app E)) h wg) := fun l =>
  .of_eq (by
    change ((Scheme.Modules.pullback h).map (fl.ι l) ≫ (cmp h τ wk).hom.app _) ≫ (cmp k γ w).hom.app E =
      (Scheme.Modules.pullback h).map (fl.ι l ≫ (cmp τ γ w₀).hom.app E) ≫ (cmp h π wg).hom.app E
    rw [Functor.map_comp, Category.assoc, Category.assoc, cmp_assoc h τ γ w₀ wg wk w])

variable {γ : G ⟶ B} {E : B.Modules} {S P : G.Modules} (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E)

private def jk (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g) :
    (Scheme.Modules.pullback k).obj P ⟶ (Scheme.Modules.pullback g).obj E :=
  (Scheme.Modules.pullback k).map j ≫ (cmp k γ w).hom.app E

private def qk (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g) :
    (Scheme.Modules.pullback g).obj E ⟶ (Scheme.Modules.pullback k).obj (cokernel j) :=
  (cmp k γ w).inv.app E ≫ (Scheme.Modules.pullback k).map (cokernel.π j)

variable {s j} {n i : ℕ}

/- English proof (translation)
The claim follows from `SubPull.isSubbundle_pullback _ _ k _ _ _ _ hS hs hj := isSubbundle_comp (SubPull.isSubbundle_pullback _ _ k _ _ _ _ hP hj) (isSubbundle_of_isIso _) hq := Cok.map (Scheme.Modules.pullback k) j ((cmp k γ w).app E) ht := by simpa using Cok.map (Scheme.Modules.pullback k) s (Iso.refl …`.
-/
private theorem dat (hE : IsVB E n) (hS : IsVB S i) (hP : IsVB P (i + 2)) (hs : IsSubbundle s) (hj : IsSubbundle j)
    (le : i + 2 ≤ n) (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g) :
    Dat ((Scheme.Modules.pullback k).map s) (jk j k w) (qk j k w)
      ((Scheme.Modules.pullback k).map (cokernel.π s)) n i where
  hs := SubPull.isSubbundle_pullback _ _ k _ _ _ _ hS hs
  hj := isSubbundle_comp (SubPull.isSubbundle_pullback _ _ k _ _ _ _ hP hj) (isSubbundle_of_isIso _)
  hq := Cok.map (Scheme.Modules.pullback k) j ((cmp k γ w).app E)
  ht := by simpa using Cok.map (Scheme.Modules.pullback k) s (Iso.refl _)
  hE := hE.pullback g
  hS := hS.pullback k
  hP := hP.pullback k
  le := le

variable {k : T ⟶ G} {g : T ⟶ B} {w : k ≫ γ = g} (h : T' ⟶ T) {k' : T' ⟶ G} {g' : T' ⟶ B} (wk : h ≫ k = k')
  (wg : h ≫ g = g') (w' : k' ≫ γ = g')

/- English proof (translation)
Rewrite using `[jk, jk, Functor.map_comp, Category.assoc, cmp_assoc h k γ w wg wk w', cmp_naturality_assoc]`.
-/
@[reassoc] private theorem map_jk : (Scheme.Modules.pullback h).map (jk j k w) ≫ (cmp h g wg).hom.app E =
    (cmp h k wk).hom.app P ≫ jk j k' w' := by
  rw [jk, jk, Functor.map_comp, Category.assoc, cmp_assoc h k γ w wg wk w', cmp_naturality_assoc]

/- English proof (translation)
Rewrite using `[← cancel_epi ((Scheme.Modules.pullback h).map ((cmp k γ w).hom.app E)), cmp_assoc_assoc h k γ w wg wk w', qk, qk, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc, cmp_naturality]`.
-/
private theorem map_qk : (cmp h g wg).hom.app E ≫ qk j k' w' =
    (Scheme.Modules.pullback h).map (qk j k w) ≫ (cmp h k wk).hom.app _ := by
  rw [← cancel_epi ((Scheme.Modules.pullback h).map ((cmp k γ w).hom.app E)), cmp_assoc_assoc h k γ w wg wk w',
    qk, qk, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc, cmp_naturality]

variable {fS : Flag ((Scheme.Modules.pullback k).obj S) i}
  {fQ : Flag ((Scheme.Modules.pullback k).obj (cokernel j)) (n - (i + 2))}
  {f₁ : Flag ((Scheme.Modules.pullback k).obj (cokernel s)) 2}

/- English proof (translation)
Use `⟨fun m hm => (((H.1 m hm).map (Scheme.Modules.pullback h)).comp _).trans (.of_eq ?_), fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[pullTo_ι]`. Simplify using `only [Functor.map_comp, Category.assoc]`. Rewrite using `[map_jk h wk wg w', cmp_naturality_assoc]`. Use `(H.2 m hm).map (Scheme.Modules.pullback h) _ _ ?_ (map_qk h wk wg w')` and prove the remaining obligations.

Rewrite using `[map_jk h wk wg w']`. Conclude with `(same_isIso_comp _ _).symm.le`.
-/
private theorem PartAt.pull {A : T.Modules} {μ : A ⟶ (Scheme.Modules.pullback g).obj E} {l : ℕ}
    (H : PartAt ((Scheme.Modules.pullback k).map s) (jk j k w) (qk j k w) fS fQ l μ) :
    PartAt ((Scheme.Modules.pullback k').map s) (jk j k' w') (qk j k' w') (pullTo fS h wk) (pullTo fQ h wk) l
      ((Scheme.Modules.pullback h).map μ ≫ (cmp h g wg).hom.app E) := by
  refine ⟨fun m hm => (((H.1 m hm).map (Scheme.Modules.pullback h)).comp _).trans (.of_eq ?_), fun m hm => ?_⟩
  · rw [pullTo_ι]
    simp only [Functor.map_comp, Category.assoc]
    rw [map_jk h wk wg w', cmp_naturality_assoc]
  · refine (H.2 m hm).map (Scheme.Modules.pullback h) _ _ ?_ (map_qk h wk wg w')
    rw [map_jk h wk wg w']
    exact (same_isIso_comp _ _).symm.le

/- English proof (translation)
Take `⟨x, rfl, hx⟩` from `H`. Use `⟨(Scheme.Modules.pullback h).map x ≫ (cmp h k wk).hom.app P, ?_, hx.map (Scheme.Modules.pullback h) _ _ ?_ (cmp_naturality h k wk _).symm⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, Category.assoc, Category.assoc, map_jk h wk wg w']`. Rewrite using `[cmp_naturality]`. Conclude with `(same_isIso_comp _ _).symm.le`.
-/
private theorem MidAt.pull {A : T.Modules} {μ : A ⟶ (Scheme.Modules.pullback g).obj E}
    (H : MidAt ((Scheme.Modules.pullback k).map s) (jk j k w) ((Scheme.Modules.pullback k).map (cokernel.π s)) f₁ μ) :
    MidAt ((Scheme.Modules.pullback k').map s) (jk j k' w') ((Scheme.Modules.pullback k').map (cokernel.π s))
      (pullTo f₁ h wk) ((Scheme.Modules.pullback h).map μ ≫ (cmp h g wg).hom.app E) := by
  obtain ⟨x, rfl, hx⟩ := H
  refine ⟨(Scheme.Modules.pullback h).map x ≫ (cmp h k wk).hom.app P, ?_,
    hx.map (Scheme.Modules.pullback h) _ _ ?_ (cmp_naturality h k wk _).symm⟩
  · rw [Functor.map_comp, Category.assoc, Category.assoc, map_jk h wk wg w']
  · rw [cmp_naturality]
    exact (same_isIso_comp _ _).symm.le

/- English proof (translation)
Introduce `l` and use `⟨(H l).1.pull h wk wg w', fun hl => ((H l).2 hl).pull h wk wg w'⟩`.
-/
private theorem Glue.pull {fl : Flag ((Scheme.Modules.pullback g).obj E) n}
    (H : Glue ((Scheme.Modules.pullback k).map s) (jk j k w) (qk j k w)
      ((Scheme.Modules.pullback k).map (cokernel.π s)) fl fS f₁ fQ) :
    Glue ((Scheme.Modules.pullback k').map s) (jk j k' w') (qk j k' w')
      ((Scheme.Modules.pullback k').map (cokernel.π s)) (pullTo fl h wg) (pullTo fS h wk) (pullTo f₁ h wk)
      (pullTo fQ h wk) :=
  fun l => ⟨(H l).1.pull h wk wg w', fun hl => ((H l).2 hl).pull h wk wg w'⟩

/- English proof (translation)
Use `hj.mono` as an intermediate fact. Use `(existsUnique_congr fun k => exists_congr fun w => ?_).1 (hG T g S' P' s' j' hs hj hS hP)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨eS, eP, h₁, h₂⟩`. Conclude with `⟨⟨eP, h₁⟩, eS, by rw [reassoc_of% h₂, h₁]; rfl⟩`.

Introduce and unpack `⟨⟨eP, h₁⟩, eS, h₂⟩`. Conclude with `⟨eS, eP, h₁, by rw [← cancel_mono j', Category.assoc, Category.assoc, h₁, h₂]⟩`.
-/
private theorem pair_iff {m₁ m₂ : ℕ} (hG : IsPairBundle γ E m₁ m₂ s j) (g : T ⟶ B) {S' P' : T.Modules} {s' : S' ⟶ P'}
    {j' : P' ⟶ (Scheme.Modules.pullback g).obj E} (hs : IsSubbundle s') (hj : IsSubbundle j') (hS : IsVB S' m₁)
    (hP : IsVB P' m₂) : ∃! k : T ⟶ G, ∃ w : k ≫ γ = g, Same (jk j k w) j' ∧
      Same ((Scheme.Modules.pullback k).map s ≫ jk j k w) (s' ≫ j') := by
  have := hj.mono
  refine (existsUnique_congr fun k => exists_congr fun w => ?_).1 (hG T g S' P' s' j' hs hj hS hP)
  constructor
  · rintro ⟨eS, eP, h₁, h₂⟩
    exact ⟨⟨eP, h₁⟩, eS, by rw [reassoc_of% h₂, h₁]; rfl⟩
  · rintro ⟨⟨eP, h₁⟩, eS, h₂⟩
    exact ⟨eS, eP, h₁, by rw [← cancel_mono j', Category.assoc, Category.assoc, h₁, h₂]⟩

/- English proof (translation)
Use `(existsUnique_congr fun h => exists_congr fun wk => ?_).1 (isFlagBundle_iff.1 hY T k fun c => match c with` and prove the remaining obligations. Consider the case `.inl b => (fb b).ofIso ((cmp k γ w).app (E b.1)).symm`. Consider the case `.inr true => fS`. Consider the case `.inr false => fQ)`. Establish `wg : h ≫ τ ≫ γ = g` using `by rw [← Category.assoc, wk, w]`.

Prove the components needed by the constructor for the conclusion. Introduce `H`. Conclude with `⟨wg, fun b => (pullTo_ofIso (E := E b.1) (r := r b.1) rfl (fl' (.inl b)) h wk w wg).symm.trans ((sameFl_ofIso_symm_iff _).1 (H (.inl b))), H (.inr true), H (.inr false)⟩`. Introduce and unpack `⟨_, h₁, h₂, h₃⟩ (b | _ | _)`. Conclude with `(sameFl_ofIso_symm_iff _).2 ((pullTo_ofIso (E := E b.1) (r := r b.1) rfl (fl' (.inl b)) h wk w wg).trans (h₁ b))`.

Conclude with `h₃`. Conclude with `h₂`.
-/
private theorem omit_iff {ι : Type} {E : ι → B.Modules} {r : ι → ℕ} {a : ι} {j : P ⟶ (Scheme.Modules.pullback γ).obj (E a)}
    {m₁ m₂ : ℕ} {τ : Y ⟶ G}
    {fl' : ∀ c, Flag ((Scheme.Modules.pullback τ).obj (fam γ E a s j c)) (rk r a m₁ m₂ c)}
    (hY : IsFlagBundle τ (fam γ E a s j) (rk r a m₁ m₂) fl') (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g)
    (fb : ∀ b : {b // b ≠ a}, Flag ((Scheme.Modules.pullback g).obj (E b.1)) (r b.1))
    (fS : Flag ((Scheme.Modules.pullback k).obj S) m₁)
    (fQ : Flag ((Scheme.Modules.pullback k).obj (cokernel j)) (r a - m₂)) :
    ∃! h : T ⟶ Y, ∃ (wk : h ≫ τ = k) (wg : h ≫ τ ≫ γ = g),
      (∀ b : {b // b ≠ a}, SameFl (pullTo (E := E b.1) (r := r b.1)
        ((fl' (.inl b)).ofIso ((cmp τ γ rfl).app (E b.1))) h wg) (fb b)) ∧
      SameFl (pullTo (E := S) (r := m₁) (fl' (.inr true)) h wk) fS ∧
      SameFl (pullTo (E := cokernel j) (r := r a - m₂) (fl' (.inr false)) h wk) fQ := by
  refine (existsUnique_congr fun h => exists_congr fun wk => ?_).1 (isFlagBundle_iff.1 hY T k fun c =>
    match c with
    | .inl b => (fb b).ofIso ((cmp k γ w).app (E b.1)).symm
    | .inr true => fS
    | .inr false => fQ)
  have wg : h ≫ τ ≫ γ = g := by rw [← Category.assoc, wk, w]
  constructor
  · intro H
    exact ⟨wg, fun b => (pullTo_ofIso (E := E b.1) (r := r b.1) rfl (fl' (.inl b)) h wk w wg).symm.trans
      ((sameFl_ofIso_symm_iff _).1 (H (.inl b))), H (.inr true), H (.inr false)⟩
  · rintro ⟨_, h₁, h₂, h₃⟩ (b | _ | _)
    · exact (sameFl_ofIso_symm_iff _).2
        ((pullTo_ofIso (E := E b.1) (r := r b.1) rfl (fl' (.inl b)) h wk w wg).trans (h₁ b))
    · exact h₃
    · exact h₂

end Pull

end GlobalTheory.OmitGlue

end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB
set_option backward.isDefEq.respectTransparency false in
open GlobalTheory.OmitGlue in
/- English proof (translation)
Introduce `B Y π ι _ E r hE fl hfl a i i' hi' G γ SG PG sG jG hS hP hs hj _ hG Y₁ τ fl' hY₁`. Establish `hle : (i : ℕ) + 2 ≤ r a` using `by omega`. Establish `D {T : Scheme.{0}} (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g)` using `dat (hE a) hS hP hs hj hle k w`. Establish `e₀ : (i.castSucc : ℕ) = i` using `rfl`. Establish `e₂ : (i'.succ : ℕ) = i + 2` using `by simp [hi']`.

Take `⟨s₀, hs₀⟩` from `flag_le (fl a) (i := i.castSucc) (j := i'.succ) (by omega)`. Take `⟨k₀, ⟨w₀, hP₀, hS₀⟩, -⟩` from `pair_iff hG π (s' := s₀) (j' := (fl a).ι i'.succ) (isSubbundle_of_comp hs₀ ((fl a).isSubbundle _) ((fl a).isSubbundle _) ((fl a).isVB _) ((fl a).isVB _) ((hE a).pullback π) (by omega) (by omega)) ((fl a).isSubbundle _) ((fl a).isVB _) (e₂ ▸ (fl a).isVB _)`. Rewrite `hS₀` using `[hs₀]`. Take `⟨fS₀, f₀, fQ₀, hgl⟩` from `exists_split (D k₀ w₀) (fl a) e₀ e₂ hS₀ hP₀`. Take `⟨ρ, ⟨wρ, wσ, hb, hSρ, hQρ⟩, -⟩` from `omit_iff hY₁ k₀ w₀ (fun b => fl b.1) fS₀ fQ₀`.

Set `flB (b : {b // b ≠ a}) : Vert.Flag ((Scheme.Modules.pullback (τ ≫ γ)).obj (E b.1)) (r b.1)` to `(fl' (.inl b)).ofIso ((LineQuot.cmp τ γ rfl).app (E b.1))`. Set `fS₁ : Vert.Flag ((Scheme.Modules.pullback τ).obj SG) i` to `fl' (.inr true)`. Set `fQ₁ : Vert.Flag ((Scheme.Modules.pullback τ).obj (Limits.cokernel jG)) (r a - (i + 2))` to `fl' (.inr false)`. Use `replace hb : ∀ b, SameFl (pullTo (flB b) ρ wσ) (fl b.1) := hb`. Use `replace hSρ : SameFl (pullTo fS₁ ρ wρ) fS₀ := hSρ`.

Use `replace hQρ : SameFl (pullTo fQ₁ ρ wρ) fQ₀ := hQρ`. Establish `D₁` using `D τ rfl`. Establish `hz : ∀ z : Σ b, Fin (r b), ∃ (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁) (v : A₁ ⟶ (Scheme.Modules.pullback (τ ≫ γ)).obj (E z.1)), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ → GlobalTheory.VB.IsSubbundle u ∧ GlobalTheory.VB.IsSubbundle v ∧ GlobalTheory.VB.IsVB A₀ z.2 ∧ GlobalTheory.VB.IsVB A₁ ((z.2 : ℕ) + …`. Introduce and unpack `⟨b, l⟩`. Distinguish the cases in `hba : b = a`.

Substitute `hba` using the available equality. Distinguish the cases in `h₁ : l = i`. Conclude with `⟨_, _, 𝟙 _, 𝟙 _, fun h => (h (by rw [h₁])).elim⟩`. Distinguish the cases in `h₂ : l = i'`. Conclude with `⟨_, _, 𝟙 _, 𝟙 _, fun _ h => (h (by rw [h₂])).elim⟩`.

Establish `h₁' : (l : ℕ) + 1 ≠ i + 1` using `fun h => h₁ (Fin.ext (by omega))`. Establish `h₂' : (l : ℕ) ≠ i + 1` using `fun h => h₂ (Fin.ext (by omega))`. Take `⟨A₀, μ₀, a₁, a₂, a₃⟩` from `exists_partAt D₁ fS₁ fQ₁ (l := l) (by omega) h₂'`. Take `⟨A₁, μ₁, b₁, b₂, b₃⟩` from `exists_partAt D₁ fS₁ fQ₁ (l := l + 1) (by omega) h₁'`. Use `b₁.mono` as an intermediate fact.

Take `⟨u, rfl⟩` from `a₃.le D₁ b₃ (fun _ => .refl _) (fun _ => .refl _) (by omega) (by omega) h₂' h₁'`. Establish `key {A : Y₁.Modules} {μ : A ⟶ (Scheme.Modules.pullback (τ ≫ γ)).obj (E b)} (m : Fin (r b + 1)) (hm : (m : ℕ) ≠ i + 1) (h₁ : IsSubbundle μ) (h₂ : IsVB A m) (h₃ : PartAt ((Scheme.Modules.pullback τ).map sG) (jk jG τ rfl) (qk jG τ rfl) fS₁ fQ₁ m μ) : Same ((Scheme.Modules.pullback ρ …`. Use `(SubPull.isSubbundle_pullback _ _ ρ _ _ _ _ h₂ h₁).mono` as an intermediate fact. Establish `h₄` using `h₃.pull ρ wρ wσ w₀`. Conclude with `.of_le (h₄.le (D k₀ w₀) (hgl m).1 hSρ hQρ le_rfl (by omega) hm hm) ((hgl m).1.le (D k₀ w₀) h₄ hSρ.symm hQρ.symm le_rfl (by omega) hm hm)`.

Conclude with `⟨A₀, A₁, u, μ₁, fun _ _ => ⟨isSubbundle_of_comp rfl a₁ b₁ a₂ b₂ D₁.hE (by omega) (by omega), b₁, a₂, b₂, key l.succ h₁' b₁ b₂ b₃, key l.castSucc h₂' a₁ a₂ a₃⟩⟩`. Use `⟨_, _, (flB ⟨b, hba⟩).step l, (flB ⟨b, hba⟩).ι l.succ, fun _ _ => ⟨⟨inferInstance, 1, (flB ⟨b, hba⟩).isVB_gr l⟩, (flB ⟨b, hba⟩).isSubbundle _, (flB ⟨b, hba⟩).isVB _, (flB ⟨b, hba⟩).isVB _, hb ⟨b, hba⟩ l.succ, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Vert.Flag.step_ι]`. Conclude with `hb ⟨b, hba⟩ l.castSucc`. Use `choose A₀ A₁ u v hz using hz`.

Use `D₁.hs.mono` as an intermediate fact. Use `D₁.ht.2.1` as an intermediate fact. Establish `hj₀` using `map_jk (j := jG) (w := rfl) ρ wρ wσ w₀`. Use `⟨ρ, wσ, _, _, _, (Scheme.Modules.pullback τ).map sG, jk jG τ rfl, (Scheme.Modules.pullback τ).map (Limits.cokernel.π sG), D₁.ht.1, f₀.ofIso ((LineQuot.cmp ρ τ wρ).app (Limits.cokernel sG)).symm, A₀, A₁, u, v, ?_, { exact := D₁.ht.exact }, D₁.hs, D₁.hj, D₁.hS, D₁.hP, D₁.hE₁, ?_, ? …` and prove the remaining obligations. Use `isFlagBundle_iff.2 fun T h f => ?_` and prove the remaining obligations.

Establish `wh : (h ≫ τ) ≫ γ = h ≫ τ ≫ γ` using `Category.assoc ..`. Take `⟨flA, hA⟩` from `exists_glue (D (h ≫ τ) wh) (pullTo fS₁ h rfl) ((f ()).ofIso ((LineQuot.cmp h τ rfl).app (Limits.cokernel sG))) (pullTo fQ₁ h rfl)`. Take `⟨fT, hTa, hTb⟩ : ∃ fT : ∀ b, Vert.Flag ((Scheme.Modules.pullback (h ≫ τ ≫ γ)).obj (E b)) (r b), fT a = flA ∧ ∀ b : {b // b ≠ a}, fT b.1 = pullTo (flB b) h rfl` from `⟨fun b => if hb : b = a then hb ▸ flA else pullTo (flB ⟨b, hb⟩) h rfl, dif_pos rfl, fun b => dif_neg b.2⟩`. Use `(existsUnique_congr fun y => ?_).1 (isFlagBundle_iff.1 hfl T (h ≫ τ ≫ γ) fT)` and prove the remaining obligations. Establish `mid (w : y ≫ ρ = h) (wk : y ≫ k₀ = h ≫ τ) : SameFl (pullTo (f₀.ofIso ((LineQuot.cmp ρ τ wρ).app (Limits.cokernel sG)).symm) y w) (f ()) ↔ SameFl (pullTo f₀ y wk) ((f ()).ofIso ((LineQuot.cmp h τ rfl).app (Limits.cokernel sG)))`.

Rewrite using `[← sameFl_ofIso_iff ((LineQuot.cmp h τ rfl).app (Limits.cokernel sG))]`. Establish `H` using `(pullTo_ofIso wρ (f₀.ofIso ((LineQuot.cmp ρ τ wρ).app (Limits.cokernel sG)).symm) y w rfl wk).trans (((sameFl_ofIso_symm_iff _).1 fun _ => .refl _).pullTo y wk)`. Conclude with `⟨fun h => H.symm.trans h, fun h => H.trans h⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨wy, hy⟩`.

Establish `ha` using `hy a`. Rewrite `ha` using `[hTa]`. Establish `wk : y ≫ k₀ = h ≫ τ`. Establish `w₁ : (y ≫ k₀) ≫ γ = h ≫ τ ≫ γ` using `by rw [Category.assoc, w₀, wy]`. Establish `g₁` using `hgl.pull y rfl wy w₁`.

Use `(pair_iff hG _ (D _ wh).hs (D _ wh).hj (D _ wh).hS (D _ wh).hP).unique ⟨w₁, ?_, ?_⟩ ⟨wh, .refl _, .refl _⟩` and prove the remaining obligations. Conclude with `(PartAt.same_P (D _ w₁) (e₂ ▸ (g₁ i'.succ).1)).symm.trans ((ha _).trans (PartAt.same_P (D _ wh) (e₂ ▸ (hA i'.succ).1)))`. Conclude with `(PartAt.same_S (g₁ i.castSucc).1).symm.trans ((ha _).trans (PartAt.same_S (hA i.castSucc).1))`. Take `⟨c₁, c₂, c₃⟩` from `(hgl.pull y wk wy wh).sameFl_parts (D _ wh) hA ha`. Establish `w : y ≫ ρ = h`.

Establish `w₁ : (y ≫ ρ) ≫ τ = h ≫ τ` using `by rw [Category.assoc, wρ, wk]`. Establish `w₂ : (y ≫ ρ) ≫ τ ≫ γ = h ≫ τ ≫ γ` using `by rw [Category.assoc, wσ, wy]`. Use `(omit_iff hY₁ (h ≫ τ) wh (fun b => pullTo (flB b) h rfl) (pullTo fS₁ h rfl) (pullTo fQ₁ h rfl)).unique ⟨w₁, w₂, fun b => ?_, ?_, ?_⟩ ⟨rfl, rfl, fun _ _ => .refl _, fun _ => .refl _, fun _ => .refl _⟩` and prove the remaining obligations. Conclude with `(pullTo_pullTo (flB b) ρ wσ y wy rfl w₂).symm.trans (((hb b).pullTo y wy).trans (hTb b ▸ hy b.1))`. Conclude with `(pullTo_pullTo fS₁ ρ wρ y wk rfl w₁).symm.trans ((hSρ.pullTo y wk).trans c₁)`.

Conclude with `(pullTo_pullTo fQ₁ ρ wρ y wk rfl w₁).symm.trans ((hQρ.pullTo y wk).trans c₃)`. Conclude with `⟨w, fun _ => (mid w wk).2 c₂⟩`. Introduce and unpack `⟨w, hy⟩`. Establish `wk : y ≫ k₀ = h ≫ τ` using `by rw [← wρ, ← w, Category.assoc]`. Establish `wy : y ≫ π = h ≫ τ ≫ γ` using `by rw [← wσ, ← w, Category.assoc]`.

Use `⟨wy, fun b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hba : b = a`. Rewrite using `[hba, hTa]`. Conclude with `(hgl.pull y wk wy wh).sameFl (D _ wh) hA ((hSρ.pullTo y wk).symm.trans (pullTo_pullTo fS₁ ρ wρ y wk w rfl)) ((mid w wk).1 (hy ())) ((hQρ.pullTo y wk).symm.trans (pullTo_pullTo fQ₁ ρ wρ y wk w rfl))`. Rewrite using `[hTb ⟨b, hba⟩]`.

Conclude with `((hb ⟨b, hba⟩).pullTo y wy).symm.trans (pullTo_pullTo (flB ⟨b, hba⟩) ρ wσ y wy w rfl)`. Conclude with `(Same.of_eq hj₀).trans ((same_isIso_comp _ _).trans hP₀)`. Use `Same.trans (g := (LineQuot.cmp ρ τ wρ).hom.app SG ≫ (Scheme.Modules.pullback k₀).map sG ≫ jk jG k₀ w₀) (.of_eq ?_) ((same_isIso_comp _ _).trans hS₀)` and prove the remaining obligations. Rewrite using `[← LineQuot.cmp_hom_app, Functor.map_comp, Category.assoc, hj₀, LineQuot.cmp_naturality_assoc]`. Take `⟨x, hx, -, g, hg, hg'⟩` from `(hgl i.succ).2 rfl`.

Use `⟨x ≫ (LineQuot.cmp ρ τ wρ).inv.app PG, g, ?_, ?_, hg'⟩` and prove the remaining obligations. Rewrite using `[← LineQuot.cmp_hom_app, hj₀, Category.assoc, Iso.inv_hom_id_app_assoc, hx]`. Express the relevant statement in the definitionally equal form `g ≫ f₀.ι 1 ≫ (LineQuot.cmp ρ τ wρ).inv.app _ = _`. Rewrite using `[reassoc_of% hg, Category.assoc]`. Conclude with `congrArg (x ≫ ·) ((LineQuot.cmp ρ τ wρ).inv.naturality _)`.
-/
theorem _root_.GlobalTheory.T.flag_bundle_successive_grassmannian : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∀ (G : Scheme.{0}) (γ : G ⟶ B) (SG PG : G.Modules) (sG : SG ⟶ PG)
      (jG : PG ⟶ (Scheme.Modules.pullback γ).obj (E a)),
      GlobalTheory.VB.IsVB SG i → GlobalTheory.VB.IsVB PG ((i : ℕ) + 2) → GlobalTheory.VB.IsSubbundle sG → GlobalTheory.VB.IsSubbundle jG →
      GlobalTheory.VB.IsVB (Limits.cokernel jG) (r a - ((i : ℕ) + 2)) →
      GlobalTheory.OmitFlag.IsPairBundle γ (E a) i ((i : ℕ) + 2) sG jG →
    ∀ (Y₁ : Scheme.{0}) (τ : Y₁ ⟶ G)
      (fl' : ∀ c, Vert.Flag ((Scheme.Modules.pullback τ).obj (GlobalTheory.OmitFlag.fam γ E a sG jG c))
        (GlobalTheory.OmitFlag.rk r a i ((i : ℕ) + 2) c)),
      IsFlagBundle τ (GlobalTheory.OmitFlag.fam γ E a sG jG) (GlobalTheory.OmitFlag.rk r a i ((i : ℕ) + 2)) fl' →
    ∃ (ρ : Y ⟶ Y₁) (wσ : ρ ≫ (τ ≫ γ) = π) (S P E₁ : Y₁.Modules) (s : S ⟶ P)
      (j : P ⟶ (Scheme.Modules.pullback (τ ≫ γ)).obj (E a)) (t : P ⟶ E₁) (wst : s ≫ t = 0)
      (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (A₀ A₁ : (Σ b, Fin (r b)) → Y₁.Modules)
      (u : ∀ z, A₀ z ⟶ A₁ z) (v : ∀ z, A₁ z ⟶ (Scheme.Modules.pullback (τ ≫ γ)).obj (E z.1)),
            IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (ShortComplex.mk s t wst).ShortExact ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧ GlobalTheory.VB.IsVB S i ∧
      GlobalTheory.VB.IsVB P ((i : ℕ) + 2) ∧ GlobalTheory.VB.IsVB E₁ 2 ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ (fl a).F i'.succ, e.hom ≫ (fl a).ι i'.succ =
        (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ (τ ≫ γ)).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ (fl a).F i.castSucc, e.hom ≫ (fl a).ι i.castSucc =
        (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ (τ ≫ γ)).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ (x : (fl a).F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : (fl a).F i.succ ⟶ fl₁.F 1),
        x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ (τ ≫ γ)).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a) = (fl a).ι i.succ ∧
        g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) ∧
      ∀ z : Σ b, Fin (r b), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        GlobalTheory.VB.IsSubbundle (u z) ∧ GlobalTheory.VB.IsSubbundle (v z) ∧ GlobalTheory.VB.IsVB (A₀ z) z.2 ∧
        GlobalTheory.VB.IsVB (A₁ z) ((z.2 : ℕ) + 1) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₁ z) ≅ (fl z.1).F z.2.succ, e.hom ≫ (fl z.1).ι z.2.succ =
          (Scheme.Modules.pullback ρ).map (v z) ≫ (Scheme.Modules.pullbackComp ρ (τ ≫ γ)).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₀ z) ≅ (fl z.1).F z.2.castSucc, e.hom ≫ (fl z.1).ι z.2.castSucc =
          (Scheme.Modules.pullback ρ).map (u z ≫ v z) ≫ (Scheme.Modules.pullbackComp ρ (τ ≫ γ)).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) := by
  intro B Y π ι _ E r hE fl hfl a i i' hi' G γ SG PG sG jG hS hP hs hj _ hG Y₁ τ fl' hY₁
  have hle : (i : ℕ) + 2 ≤ r a := by omega
  have D {T : Scheme.{0}} (k : T ⟶ G) {g : T ⟶ B} (w : k ≫ γ = g) := dat (hE a) hS hP hs hj hle k w
  have e₀ : (i.castSucc : ℕ) = i := rfl
  have e₂ : (i'.succ : ℕ) = i + 2 := by simp [hi']
  obtain ⟨s₀, hs₀⟩ := flag_le (fl a) (i := i.castSucc) (j := i'.succ) (by omega)
  obtain ⟨k₀, ⟨w₀, hP₀, hS₀⟩, -⟩ := pair_iff hG π (s' := s₀) (j' := (fl a).ι i'.succ)
    (isSubbundle_of_comp hs₀ ((fl a).isSubbundle _) ((fl a).isSubbundle _) ((fl a).isVB _) ((fl a).isVB _)
      ((hE a).pullback π) (by omega) (by omega)) ((fl a).isSubbundle _) ((fl a).isVB _) (e₂ ▸ (fl a).isVB _)
  rw [hs₀] at hS₀
  obtain ⟨fS₀, f₀, fQ₀, hgl⟩ := exists_split (D k₀ w₀) (fl a) e₀ e₂ hS₀ hP₀
  obtain ⟨ρ, ⟨wρ, wσ, hb, hSρ, hQρ⟩, -⟩ := omit_iff hY₁ k₀ w₀ (fun b => fl b.1) fS₀ fQ₀
  let flB (b : {b // b ≠ a}) : Vert.Flag ((Scheme.Modules.pullback (τ ≫ γ)).obj (E b.1)) (r b.1) :=
    (fl' (.inl b)).ofIso ((LineQuot.cmp τ γ rfl).app (E b.1))
  let fS₁ : Vert.Flag ((Scheme.Modules.pullback τ).obj SG) i := fl' (.inr true)
  let fQ₁ : Vert.Flag ((Scheme.Modules.pullback τ).obj (Limits.cokernel jG)) (r a - (i + 2)) := fl' (.inr false)
  replace hb : ∀ b, SameFl (pullTo (flB b) ρ wσ) (fl b.1) := hb
  replace hSρ : SameFl (pullTo fS₁ ρ wρ) fS₀ := hSρ
  replace hQρ : SameFl (pullTo fQ₁ ρ wρ) fQ₀ := hQρ
  have D₁ := D τ rfl
  have hz : ∀ z : Σ b, Fin (r b), ∃ (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁)
      (v : A₁ ⟶ (Scheme.Modules.pullback (τ ≫ γ)).obj (E z.1)), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        GlobalTheory.VB.IsSubbundle u ∧ GlobalTheory.VB.IsSubbundle v ∧ GlobalTheory.VB.IsVB A₀ z.2 ∧ GlobalTheory.VB.IsVB A₁ ((z.2 : ℕ) + 1) ∧
        Same ((Scheme.Modules.pullback ρ).map v ≫ (LineQuot.cmp ρ (τ ≫ γ) wσ).hom.app (E z.1))
          ((fl z.1).ι z.2.succ) ∧
        Same ((Scheme.Modules.pullback ρ).map (u ≫ v) ≫ (LineQuot.cmp ρ (τ ≫ γ) wσ).hom.app (E z.1))
          ((fl z.1).ι z.2.castSucc) := by
    rintro ⟨b, l⟩
    by_cases hba : b = a
    · subst hba
      by_cases h₁ : l = i
      · exact ⟨_, _, 𝟙 _, 𝟙 _, fun h => (h (by rw [h₁])).elim⟩
      by_cases h₂ : l = i'
      · exact ⟨_, _, 𝟙 _, 𝟙 _, fun _ h => (h (by rw [h₂])).elim⟩
      have h₁' : (l : ℕ) + 1 ≠ i + 1 := fun h => h₁ (Fin.ext (by omega))
      have h₂' : (l : ℕ) ≠ i + 1 := fun h => h₂ (Fin.ext (by omega))
      obtain ⟨A₀, μ₀, a₁, a₂, a₃⟩ := exists_partAt D₁ fS₁ fQ₁ (l := l) (by omega) h₂'
      obtain ⟨A₁, μ₁, b₁, b₂, b₃⟩ := exists_partAt D₁ fS₁ fQ₁ (l := l + 1) (by omega) h₁'
      have := b₁.mono
      obtain ⟨u, rfl⟩ := a₃.le D₁ b₃ (fun _ => .refl _) (fun _ => .refl _) (by omega) (by omega) h₂' h₁'
      have key {A : Y₁.Modules} {μ : A ⟶ (Scheme.Modules.pullback (τ ≫ γ)).obj (E b)} (m : Fin (r b + 1))
          (hm : (m : ℕ) ≠ i + 1) (h₁ : IsSubbundle μ) (h₂ : IsVB A m)
          (h₃ : PartAt ((Scheme.Modules.pullback τ).map sG) (jk jG τ rfl) (qk jG τ rfl) fS₁ fQ₁ m μ) :
          Same ((Scheme.Modules.pullback ρ).map μ ≫ (LineQuot.cmp ρ (τ ≫ γ) wσ).hom.app (E b)) ((fl b).ι m) := by
        have := (SubPull.isSubbundle_pullback _ _ ρ _ _ _ _ h₂ h₁).mono
        have h₄ := h₃.pull ρ wρ wσ w₀
        exact .of_le (h₄.le (D k₀ w₀) (hgl m).1 hSρ hQρ le_rfl (by omega) hm hm)
          ((hgl m).1.le (D k₀ w₀) h₄ hSρ.symm hQρ.symm le_rfl (by omega) hm hm)
      exact ⟨A₀, A₁, u, μ₁, fun _ _ => ⟨isSubbundle_of_comp rfl a₁ b₁ a₂ b₂ D₁.hE (by omega) (by omega), b₁, a₂, b₂,
        key l.succ h₁' b₁ b₂ b₃, key l.castSucc h₂' a₁ a₂ a₃⟩⟩
    · refine ⟨_, _, (flB ⟨b, hba⟩).step l, (flB ⟨b, hba⟩).ι l.succ, fun _ _ =>
        ⟨⟨inferInstance, 1, (flB ⟨b, hba⟩).isVB_gr l⟩, (flB ⟨b, hba⟩).isSubbundle _, (flB ⟨b, hba⟩).isVB _,
          (flB ⟨b, hba⟩).isVB _, hb ⟨b, hba⟩ l.succ, ?_⟩⟩
      rw [Vert.Flag.step_ι]
      exact hb ⟨b, hba⟩ l.castSucc
  choose A₀ A₁ u v hz using hz
  have := D₁.hs.mono
  have := D₁.ht.2.1
  have hj₀ := map_jk (j := jG) (w := rfl) ρ wρ wσ w₀
  refine ⟨ρ, wσ, _, _, _, (Scheme.Modules.pullback τ).map sG, jk jG τ rfl,
    (Scheme.Modules.pullback τ).map (Limits.cokernel.π sG), D₁.ht.1,
    f₀.ofIso ((LineQuot.cmp ρ τ wρ).app (Limits.cokernel sG)).symm, A₀, A₁, u, v, ?_, { exact := D₁.ht.exact },
    D₁.hs, D₁.hj, D₁.hS, D₁.hP, D₁.hE₁, ?_, ?_, ?_, hz⟩
  · refine isFlagBundle_iff.2 fun T h f => ?_
    have wh : (h ≫ τ) ≫ γ = h ≫ τ ≫ γ := Category.assoc ..
    obtain ⟨flA, hA⟩ := exists_glue (D (h ≫ τ) wh) (pullTo fS₁ h rfl)
      ((f ()).ofIso ((LineQuot.cmp h τ rfl).app (Limits.cokernel sG))) (pullTo fQ₁ h rfl)
    obtain ⟨fT, hTa, hTb⟩ : ∃ fT : ∀ b, Vert.Flag ((Scheme.Modules.pullback (h ≫ τ ≫ γ)).obj (E b)) (r b),
        fT a = flA ∧ ∀ b : {b // b ≠ a}, fT b.1 = pullTo (flB b) h rfl :=
      ⟨fun b => if hb : b = a then hb ▸ flA else pullTo (flB ⟨b, hb⟩) h rfl, dif_pos rfl, fun b => dif_neg b.2⟩
    refine (existsUnique_congr fun y => ?_).1 (isFlagBundle_iff.1 hfl T (h ≫ τ ≫ γ) fT)
    have mid (w : y ≫ ρ = h) (wk : y ≫ k₀ = h ≫ τ) :
        SameFl (pullTo (f₀.ofIso ((LineQuot.cmp ρ τ wρ).app (Limits.cokernel sG)).symm) y w) (f ()) ↔
        SameFl (pullTo f₀ y wk) ((f ()).ofIso ((LineQuot.cmp h τ rfl).app (Limits.cokernel sG))) := by
      rw [← sameFl_ofIso_iff ((LineQuot.cmp h τ rfl).app (Limits.cokernel sG))]
      have H := (pullTo_ofIso wρ (f₀.ofIso ((LineQuot.cmp ρ τ wρ).app (Limits.cokernel sG)).symm) y w rfl wk).trans
        (((sameFl_ofIso_symm_iff _).1 fun _ => .refl _).pullTo y wk)
      exact ⟨fun h => H.symm.trans h, fun h => H.trans h⟩
    constructor
    · rintro ⟨wy, hy⟩
      have ha := hy a
      rw [hTa] at ha
      have wk : y ≫ k₀ = h ≫ τ := by
        have w₁ : (y ≫ k₀) ≫ γ = h ≫ τ ≫ γ := by rw [Category.assoc, w₀, wy]
        have g₁ := hgl.pull y rfl wy w₁
        refine (pair_iff hG _ (D _ wh).hs (D _ wh).hj (D _ wh).hS (D _ wh).hP).unique ⟨w₁, ?_, ?_⟩
          ⟨wh, .refl _, .refl _⟩
        · exact (PartAt.same_P (D _ w₁) (e₂ ▸ (g₁ i'.succ).1)).symm.trans
            ((ha _).trans (PartAt.same_P (D _ wh) (e₂ ▸ (hA i'.succ).1)))
        · exact (PartAt.same_S (g₁ i.castSucc).1).symm.trans ((ha _).trans (PartAt.same_S (hA i.castSucc).1))
      obtain ⟨c₁, c₂, c₃⟩ := (hgl.pull y wk wy wh).sameFl_parts (D _ wh) hA ha
      have w : y ≫ ρ = h := by
        have w₁ : (y ≫ ρ) ≫ τ = h ≫ τ := by rw [Category.assoc, wρ, wk]
        have w₂ : (y ≫ ρ) ≫ τ ≫ γ = h ≫ τ ≫ γ := by rw [Category.assoc, wσ, wy]
        refine (omit_iff hY₁ (h ≫ τ) wh (fun b => pullTo (flB b) h rfl) (pullTo fS₁ h rfl)
          (pullTo fQ₁ h rfl)).unique ⟨w₁, w₂, fun b => ?_, ?_, ?_⟩
          ⟨rfl, rfl, fun _ _ => .refl _, fun _ => .refl _, fun _ => .refl _⟩
        · exact (pullTo_pullTo (flB b) ρ wσ y wy rfl w₂).symm.trans (((hb b).pullTo y wy).trans (hTb b ▸ hy b.1))
        · exact (pullTo_pullTo fS₁ ρ wρ y wk rfl w₁).symm.trans ((hSρ.pullTo y wk).trans c₁)
        · exact (pullTo_pullTo fQ₁ ρ wρ y wk rfl w₁).symm.trans ((hQρ.pullTo y wk).trans c₃)
      exact ⟨w, fun _ => (mid w wk).2 c₂⟩
    · rintro ⟨w, hy⟩
      have wk : y ≫ k₀ = h ≫ τ := by rw [← wρ, ← w, Category.assoc]
      have wy : y ≫ π = h ≫ τ ≫ γ := by rw [← wσ, ← w, Category.assoc]
      refine ⟨wy, fun b => ?_⟩
      by_cases hba : b = a
      · rw [hba, hTa]
        exact (hgl.pull y wk wy wh).sameFl (D _ wh) hA
          ((hSρ.pullTo y wk).symm.trans (pullTo_pullTo fS₁ ρ wρ y wk w rfl)) ((mid w wk).1 (hy ()))
          ((hQρ.pullTo y wk).symm.trans (pullTo_pullTo fQ₁ ρ wρ y wk w rfl))
      · rw [hTb ⟨b, hba⟩]
        exact ((hb ⟨b, hba⟩).pullTo y wy).symm.trans (pullTo_pullTo (flB ⟨b, hba⟩) ρ wσ y wy w rfl)
  · exact (Same.of_eq hj₀).trans ((same_isIso_comp _ _).trans hP₀)
  · refine Same.trans (g := (LineQuot.cmp ρ τ wρ).hom.app SG ≫ (Scheme.Modules.pullback k₀).map sG ≫ jk jG k₀ w₀)
      (.of_eq ?_) ((same_isIso_comp _ _).trans hS₀)
    rw [← LineQuot.cmp_hom_app, Functor.map_comp, Category.assoc, hj₀, LineQuot.cmp_naturality_assoc]
  · obtain ⟨x, hx, -, g, hg, hg'⟩ := (hgl i.succ).2 rfl
    refine ⟨x ≫ (LineQuot.cmp ρ τ wρ).inv.app PG, g, ?_, ?_, hg'⟩
    · rw [← LineQuot.cmp_hom_app, hj₀, Category.assoc, Iso.inv_hom_id_app_assoc, hx]
    · change g ≫ f₀.ι 1 ≫ (LineQuot.cmp ρ τ wρ).inv.app _ = _
      rw [reassoc_of% hg, Category.assoc]
      exact congrArg (x ≫ ·) ((LineQuot.cmp ρ τ wρ).inv.naturality _)
