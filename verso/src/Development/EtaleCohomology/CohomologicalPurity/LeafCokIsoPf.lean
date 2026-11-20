import Development.EtaleCohomology.CohomologicalPurity.LeafExcSpPfMono

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

def LeafFreePb : Prop := ∀ (R : Type) [CommRing R] {A' A B' B : PSh} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
  (b : A ⟶ B), IsPullback t l r b → Mono r → Mono b →
  IsPullback ((free R).map t) ((free R).map l) ((free R).map r) ((free R).map b)

/- English proof (translation)
Use `Abelian.mono_cokernel_map_of_isPullback sq` as an intermediate fact. Establish `: Epi (cokernel.map _ _ _ _ sq.w)`. Establish `h1 : biprod.desc r b ≫ cokernel.π b = (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b)`. Apply the tactic sequence `ext <;> simp`. Establish `h3 : Epi (r ≫ cokernel.π b)`.

Establish `: Epi ((biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b))` using `by rw [← h1]; infer_instance`. Conclude with `epi_of_epi (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) _`. Establish `h2 : cokernel.π t ≫ cokernel.map _ _ _ _ sq.w = r ≫ cokernel.π b` using `by simp`. Rewrite `h3` using `[← h2]`. Conclude with `epi_of_epi (cokernel.π t) _`.

Conclude with `isIso_of_mono_of_epi _`.
-/
theorem isIso_cokernel_map_of_pb_epi {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPullback t l r b)
    (he : Epi (biprod.desc r b)) : IsIso (cokernel.map _ _ _ _ sq.w) := by
  have := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (cokernel.map _ _ _ _ sq.w) := by
    have h1 : biprod.desc r b ≫ cokernel.π b = (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b) := by
      ext <;> simp
    have h3 : Epi (r ≫ cokernel.π b) := by
      have : Epi ((biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b)) := by rw [← h1]; infer_instance
      exact epi_of_epi (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) _
    have h2 : cokernel.π t ≫ cokernel.map _ _ _ _ sq.w = r ≫ cokernel.π b := by simp
    rw [← h2] at h3
    exact epi_of_epi (cokernel.π t) _
  exact isIso_of_mono_of_epi _

/- English proof (translation)
Substitute `ht hl hr hb` using the available equality. Use `⟨sq.of_iso e₁.symm e₂.symm e₃.symm e₄.symm (by simp) (by simp) (by simp) (by simp), ?_⟩` and prove the remaining obligations. Establish `: biprod.desc (e₂.hom ≫ r' ≫ e₄.inv) (e₃.hom ≫ b' ≫ e₄.inv) = (biprod.mapIso e₂ e₃).hom ≫ biprod.desc r' b' ≫ e₄.inv`. Apply the tactic sequence `ext <;> simp`. Rewrite using `[this]`.

Use `infer_instance`.
-/
theorem transport_sq {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄)
    (ht : t = e₁.hom ≫ t' ≫ e₂.inv) (hl : l = e₁.hom ≫ l' ≫ e₃.inv)
    (hr : r = e₂.hom ≫ r' ≫ e₄.inv) (hb : b = e₃.hom ≫ b' ≫ e₄.inv)
    (sq : IsPullback t' l' r' b') (he : Epi (biprod.desc r' b')) :
    IsPullback t l r b ∧ Epi (biprod.desc r b) := by
  subst ht hl hr hb
  refine ⟨sq.of_iso e₁.symm e₂.symm e₃.symm e₄.symm (by simp) (by simp) (by simp) (by simp), ?_⟩
  have : biprod.desc (e₂.hom ≫ r' ≫ e₄.inv) (e₃.hom ≫ b' ≫ e₄.inv) =
      (biprod.mapIso e₂ e₃).hom ≫ biprod.desc r' b' ≫ e₄.inv := by
    ext <;> simp
  rw [this]
  infer_instance

/- English proof (translation)
Introduce `q P' P φ hpb hc n`. Distinguish the cases in `hn : ∃ p : ℕ, -(p : ℤ) = n`. Take `⟨p, rfl⟩` from `hn`. Establish `h : ComplexShape.embeddingDownNat.f p = -(p : ℤ)` using `rfl`. Establish `key : ∀ {E' E : Spc} (f : E' ⟶ E), ((chains (ZMod q)).map f).f (-(p : ℤ)) = (HomologicalComplex.extendXIso _ _ h).hom ≫ (free (ZMod q)).map (f.app (op (SimplexCategory.mk p))) ≫ (HomologicalComplex.extendXIso _ _ h).inv`.

Introduce `E' E f`. Express the relevant statement in the definitionally equal form `(HomologicalComplex.extendMap ((chainsN (ZMod q)).map f) _).f _ = _`. Rewrite using `[HomologicalComplex.extendMap_f _ _ h]`. Both sides reduce to the same expression. Establish `hpb' : IsPullback (P'.hom.app (op (SimplexCategory.mk p))) (φ.left.app (op (SimplexCategory.mk p))) (φ.right.app (op (SimplexCategory.mk p))) (P.hom.app (op (SimplexCategory.mk p)))` using `hpb.map ((evaluation _ _).obj (op (SimplexCategory.mk p)))`.

Establish `mr : Mono (φ.right.app (op (SimplexCategory.mk p)))`. Use `hc.1` as an intermediate fact. Rewrite `this` using `[NatTrans.mono_iff_mono_app]`. Conclude with `this _`. Establish `mb : Mono (P.hom.app (op (SimplexCategory.mk p)))`.

Use `hc.2.1` as an intermediate fact. Rewrite `this` using `[NatTrans.mono_iff_mono_app]`. Conclude with `this _`. Take `⟨h1, h2⟩` from `transport_sq _ _ _ _ (key P'.hom) (key φ.left) (key φ.right) (key P.hom) (hF (ZMod q) _ _ _ _ hpb' mr mb) (hc.2.2 _)`. Conclude with `isIso_cokernel_map_of_pb_epi h1 h2`.

Use `push Not at hn`. Establish `hz : ∀ E : Spc, IsZero (((chains (ZMod q)).obj E).X n)` using `fun E => HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)`. Establish `hA : IsZero (cokernel ((chains (ZMod q)).map P'.hom |>.f n))` using `IsZero.of_epi (cokernel.π _) (hz _)`. Establish `hB : IsZero (cokernel ((chains (ZMod q)).map P.hom |>.f n))` using `IsZero.of_epi (cokernel.π _) (hz _)`. Conclude with `⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩`.
-/
theorem leafCokIso_of (hF : LeafFreePb) : LeafCokIso := by
  intro q P' P φ hpb hc n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    have key : ∀ {E' E : Spc} (f : E' ⟶ E), ((chains (ZMod q)).map f).f (-(p : ℤ)) =
        (HomologicalComplex.extendXIso _ _ h).hom ≫ (free (ZMod q)).map (f.app (op (SimplexCategory.mk p))) ≫
          (HomologicalComplex.extendXIso _ _ h).inv := by
      intro E' E f
      change (HomologicalComplex.extendMap ((chainsN (ZMod q)).map f) _).f _ = _
      rw [HomologicalComplex.extendMap_f _ _ h]
      rfl
    have hpb' : IsPullback (P'.hom.app (op (SimplexCategory.mk p))) (φ.left.app (op (SimplexCategory.mk p)))
        (φ.right.app (op (SimplexCategory.mk p))) (P.hom.app (op (SimplexCategory.mk p))) :=
      hpb.map ((evaluation _ _).obj (op (SimplexCategory.mk p)))
    have mr : Mono (φ.right.app (op (SimplexCategory.mk p))) := by
      have := hc.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    have mb : Mono (P.hom.app (op (SimplexCategory.mk p))) := by
      have := hc.2.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    obtain ⟨h1, h2⟩ := transport_sq _ _ _ _ (key P'.hom) (key φ.left) (key φ.right) (key P.hom)
      (hF (ZMod q) _ _ _ _ hpb' mr mb) (hc.2.2 _)
    exact isIso_cokernel_map_of_pb_epi h1 h2
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains (ZMod q)).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hA : IsZero (cokernel ((chains (ZMod q)).map P'.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    have hB : IsZero (cokernel ((chains (ZMod q)).map P.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    exact ⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
