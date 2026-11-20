import Development.EtaleCohomology.EtaleSheaves.longPf

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.longPfSes
open LateralTheory.E.CxDescPf

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `show -(N : ℤ) + (((i + N).toNat : ℕ) : ℤ) = i`. Use linear arithmetic over natural numbers and integers.
-/
theorem eF (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (ComplexShape.embeddingUpIntGE (-(N : ℤ))).f (i + N).toNat = i := by
  show -(N : ℤ) + (((i + N).toNat : ℕ) : ℤ) = i; omega

def trX (K : Cx R) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (tr K N).X i ≅ K.X i := K.stupidTruncXIso _ (eF N i h)

/- English proof (translation)
The claim follows from `K.isZero_stupidTrunc_X _ i (by intro k; show -(N : ℤ) + (k : ℤ) ≠ i; omega)`.
-/
theorem trZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i < -(N : ℤ)) : IsZero ((tr K N).X i) :=
  K.isZero_stupidTrunc_X _ i (by intro k; show -(N : ℤ) + (k : ℤ) ≠ i; omega)

/- English proof (translation)
Establish `h1` using `eF N i hi`. Establish `h2` using `eF N j hj`. Simplify using `only [trX, HomologicalComplex.stupidTruncXIso, tr, HomologicalComplex.stupidTrunc, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]`. Rewrite using `[HomologicalComplex.extend_d_eq _ _ h1 h2, HomologicalComplex.restriction_d_eq _ _ h1 h2]`. Simplify using `[HomologicalComplex.restrictionXIso]`.
-/
theorem tr_d (K : Cx R) (N : ℕ) (i j : ℤ) (hi : -(N : ℤ) ≤ i) (hj : -(N : ℤ) ≤ j) :
    (tr K N).d i j = (trX K N i hi).hom ≫ K.d i j ≫ (trX K N j hj).inv := by
  have h1 := eF N i hi
  have h2 := eF N j hj
  simp only [trX, HomologicalComplex.stupidTruncXIso, tr, HomologicalComplex.stupidTrunc, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rw [HomologicalComplex.extend_d_eq _ _ h1 h2, HomologicalComplex.restriction_d_eq _ _ h1 h2]
  simp [HomologicalComplex.restrictionXIso]

/- English proof (translation)
Rewrite using `[← Category.assoc, Iso.eq_comp_inv]`. Conclude with `HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom g _ (eF N i h)`.
-/
theorem trm_f {K L : Cx R} (g : K ⟶ L) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) :
    (trm g N).f i = (trX K N i h).hom ≫ g.f i ≫ (trX L N i h).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom g _ (eF N i h)

abbrev Sg (K : Cx R) (N : ℕ) : Cx R :=
  (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ)))

/- English proof (translation)
The claim follows from `HomologicalComplex.isZero_single_obj_X _ _ _ _ h`.
-/
theorem SgZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i ≠ -((N + 1 : ℕ) : ℤ)) : IsZero ((Sg K N).X i) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

def ιf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K N).X i ⟶ (tr K (N + 1)).X i :=
  if h : -(N : ℤ) ≤ i then (trX K N i h).hom ≫ (trX K (N + 1) i (by push_cast; omega)).inv else 0

def ι (K : Cx R) (N : ℕ) : tr K N ⟶ tr K (N + 1) where
  f := ιf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h : -(N : ℤ) ≤ i
    · have hj : -(N : ℤ) ≤ j := by omega
      rw [ιf, dif_pos h, ιf, dif_pos hj, tr_d K N i j h hj, tr_d K (N + 1) i j (by push_cast; omega) (by push_cast; omega)]
      simp
    · rw [ιf, dif_neg h, zero_comp]
      exact (trZ K N i (by omega)).eq_of_src _ _

def pf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K (N + 1)).X i ⟶ (Sg K N).X i :=
  if h : i = -((N + 1 : ℕ) : ℤ) then
    (trX K (N + 1) i (by omega)).hom ≫ eqToHom (by rw [h]) ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) _ (K.X (-((N + 1 : ℕ) : ℤ))) i h).inv
  else 0

def pp (K : Cx R) (N : ℕ) : tr K (N + 1) ⟶ Sg K N where
  f := pf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hj : j = -((N + 1 : ℕ) : ℤ)
    · exact (trZ K (N + 1) i (by push_cast at hj ⊢; omega)).eq_of_src _ _
    · exact (SgZ K N j hj).eq_of_tgt _ _

/- English proof (translation)
Use `HomologicalComplex.hom_ext _ _ (fun i => ?_)` and prove the remaining obligations. Rewrite using `[HomologicalComplex.comp_f, HomologicalComplex.zero_f]`. Distinguish the cases in `h : -(N : ℤ) ≤ i`. Conclude with `(SgZ K N i (by push_cast; omega)).eq_of_tgt _ _`. Use `show ιf K N i ≫ _ = 0`.

Rewrite using `[ιf, dif_neg h, zero_comp]`.
-/
theorem ιp (K : Cx R) (N : ℕ) : ι K N ≫ pp K N = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  by_cases h : -(N : ℤ) ≤ i
  · exact (SgZ K N i (by push_cast; omega)).eq_of_tgt _ _
  · show ιf K N i ≫ _ = 0
    rw [ιf, dif_neg h, zero_comp]

/- English proof (translation)
Use `HomologicalComplex.hom_ext _ _ (fun i => ?_)` and prove the remaining obligations. Rewrite using `[HomologicalComplex.comp_f, HomologicalComplex.comp_f]`. Distinguish the cases in `h : -(N : ℤ) ≤ i`. Use `show ιf K N i ≫ _ = _ ≫ ιf L N i`. Rewrite using `[ιf, dif_pos h, ιf, dif_pos h, trm_f g N i h, trm_f g (N + 1) i (by push_cast; omega)]`.

Simplify using the standard rewrite rules. Conclude with `(trZ K N i (by omega)).eq_of_src _ _`.
-/
theorem nat1 {K L : Cx R} (g : K ⟶ L) (N : ℕ) : ι K N ≫ trm g (N + 1) = trm g N ≫ ι L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : -(N : ℤ) ≤ i
  · show ιf K N i ≫ _ = _ ≫ ιf L N i
    rw [ιf, dif_pos h, ιf, dif_pos h, trm_f g N i h, trm_f g (N + 1) i (by push_cast; omega)]
    simp
  · exact (trZ K N i (by omega)).eq_of_src _ _

/- English proof (translation)
Use `HomologicalComplex.hom_ext _ _ (fun i => ?_)` and prove the remaining obligations. Rewrite using `[HomologicalComplex.comp_f, HomologicalComplex.comp_f]`. Distinguish the cases in `h : i = -((N + 1 : ℕ) : ℤ)`. Substitute `h show pf K N _ ≫ _ = _ ≫ pf L N _` using the available equality. Rewrite using `[pf, dif_pos rfl, pf, dif_pos rfl, trm_f g (N + 1) _ (by omega)]`.

Simplify using `[CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf]`. Use `erw [Category.id_comp, Category.id_comp, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]`. Both sides reduce to the same expression. Conclude with `(SgZ L N i h).eq_of_tgt _ _`.
-/
theorem nat2 {K L : Cx R} (g : K ⟶ L) (N : ℕ) :
    pp K N ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) =
      trm g (N + 1) ≫ pp L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : i = -((N + 1 : ℕ) : ℤ)
  · subst h
    show pf K N _ ≫ _ = _ ≫ pf L N _
    rw [pf, dif_pos rfl, pf, dif_pos rfl, trm_f g (N + 1) _ (by omega)]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleObjXSelf]
    erw [Category.id_comp, Category.id_comp, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  · exact (SgZ L N i h).eq_of_tgt _ _

/- English proof (translation)
Apply `HomologicalComplex.shortExact_of_degreewise_shortExact` to reduce the goal to its premises. Introduce `i`. Distinguish the cases in `h : -(N : ℤ) ≤ i`. Establish `hz : IsZero ((Sg K N).X i)` using `SgZ K N i (by push_cast; omega)`. Establish `: IsIso (ιf K N i)` using `by rw [ιf, dif_pos h]; infer_instance`.

Establish `hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).f` using `this`. Use `ShortComplex.ShortExact.mk' ?_ inferInstance (hz.epi _)` and prove the remaining obligations. Rewrite using `[ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)]`. Use `infer_instance`. Distinguish the cases in `h' : i = -((N + 1 : ℕ) : ℤ)`.

Establish `hz : IsZero ((tr K N).X i)` using `trZ K N i (by omega)`. Establish `: IsIso (pf K N i)` using `by subst h'; rw [pf, dif_pos rfl]; exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))`. Establish `hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).g` using `this`. Use `ShortComplex.ShortExact.mk' ?_ (hz.mono _) inferInstance` and prove the remaining obligations. Rewrite using `[ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)]`.

Use `infer_instance`. Establish `hz2 : IsZero ((tr K (N + 1)).X i)` using `trZ K (N + 1) i (by push_cast at h' ⊢; omega)`. Establish `hz1 : IsZero ((tr K N).X i)` using `trZ K N i (by omega)`. Conclude with `ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz2) (hz1.mono _) ((SgZ K N i h').epi _)`.
-/
theorem sesK (K : Cx R) (N : ℕ) : (ShortComplex.mk (ι K N) (pp K N) (ιp K N)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h : -(N : ℤ) ≤ i
  · have hz : IsZero ((Sg K N).X i) := SgZ K N i (by push_cast; omega)
    have : IsIso (ιf K N i) := by rw [ιf, dif_pos h]; infer_instance
    have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).f := this
    refine ShortComplex.ShortExact.mk' ?_ inferInstance (hz.epi _)
    rw [ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)]
    infer_instance
  · by_cases h' : i = -((N + 1 : ℕ) : ℤ)
    · have hz : IsZero ((tr K N).X i) := trZ K N i (by omega)
      have : IsIso (pf K N i) := by subst h'; rw [pf, dif_pos rfl]; exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))
      have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).g := this
      refine ShortComplex.ShortExact.mk' ?_ (hz.mono _) inferInstance
      rw [ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)]
      infer_instance
    · have hz2 : IsZero ((tr K (N + 1)).X i) := trZ K (N + 1) i (by push_cast at h' ⊢; omega)
      have hz1 : IsZero ((tr K N).X i) := trZ K N i (by omega)
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz2) (hz1.mono _) ((SgZ K N i h').epi _)

/- English proof (translation)
Introduce `_ _ N` and use `⟨fun K => ι K N, fun K => pp K N, fun K => ιp K N, fun K => sesK K N, fun g => ⟨nat1 g N, nat2 g N⟩⟩`.
-/
theorem ses : LateralTheory.E.longPf.Ses := fun _ _ N =>
  ⟨fun K => ι K N, fun K => pp K N, fun K => ιp K N, fun K => sesK K N, fun g => ⟨nat1 g N, nat2 g N⟩⟩

/- English proof (translation)
The claim follows from `LateralTheory.E.longPf.long_of hLES ses`.
-/
theorem long_of (hLES : LateralTheory.E.longPf.LES) : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPf.long_of hLES ses

end LateralTheory.E.longPfSes
