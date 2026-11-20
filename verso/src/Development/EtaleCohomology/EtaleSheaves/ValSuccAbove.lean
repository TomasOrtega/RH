import Development.EtaleCohomology.EtaleSheaves.EtaleGroupHomologySlantOfDeltaCochain

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

/- English proof (translation)
Assemble the required witnesses or components as `⟨AddMonoidHom.mk' (slantHom R X) (slantHom_add R X), fun _ => rfl⟩`.
-/
theorem slantHom_neg (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} :
    ∃ f : ((Fin m → Γ) →₀ R) →+ _, ∀ c, f c = slantHom R X c :=
  ⟨AddMonoidHom.mk' (slantHom R X) (slantHom_add R X), fun _ => rfl⟩

/- English proof (translation)
Introduce `R _ Γ _ X m b`. Proceed by induction on `b using Finsupp.induction_linear with`. Consider the case `zero => rw [slantHom_zero, show bd R (0 : (Fin (m + 1) → Γ) →₀ R) = 0 from map_zero _, slantHom_zero]`. Conclude with `zero_comp`. Consider the case `add a b ha hb`.

Rewrite using `[slantHom_add, show bd R (a + b) = bd R a + bd R b from map_add _ _ _, slantHom_add, ← ha, ← hb]`. Conclude with `Preadditive.add_comp _ _ _ _ _ _`. Consider the case `single g r`. Take `⟨f, hf⟩` from `slantHom_neg R X (Γ := Γ) (m := m)`. Establish `e : bd R (Finsupp.single g r) = Finsupp.single (fun i => g i.succ) r + ∑ j : Fin (m + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r`.

Use `groupHomology.inhomogeneousChains.d_single (A := Rep.trivial R Γ R) m g r` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul R]`.

Simplify using the standard rewrite rules. Establish `d : ((chainsN R).obj (BX Γ X)).d (m + 1) m = ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((BX Γ X).δ i)` using `AlgebraicTopology.alternatingFaceMapComplex_obj_d _ m`. Rewrite using `[e, ← hf (_ + _), map_add, map_sum, d, slantHom_single]`. Establish `e2 : ∀ j : Fin (m + 1), f ((-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r) = (-1 : ℤ) ^ ((j : ℕ) + 1) • (ULift.up r : ULift.{1} R) • (free R).map (grpPt X (j.contractNth (· * ·) g))` using `fun j => by rw [map_zsmul, hf, slantHom_single]`. Rewrite using `[Finset.sum_congr rfl fun j _ => e2 j, hf, slantHom_single]`.

Use `erw [Preadditive.comp_sum]`. Rewrite using `[Fin.sum_univ_succ]`. Use `congr 1`. Use `erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).1]`. Conclude with `one_smul ℤ _`.

Use `Finset.sum_congr rfl fun j _ => ?_ erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).2 j]` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem homD_of (h : Faces) : HomD := by
  intro R _ Γ _ X m b
  induction b using Finsupp.induction_linear with
  | zero => rw [slantHom_zero, show bd R (0 : (Fin (m + 1) → Γ) →₀ R) = 0 from map_zero _, slantHom_zero]; exact zero_comp
  | add a b ha hb =>
    rw [slantHom_add, show bd R (a + b) = bd R a + bd R b from map_add _ _ _, slantHom_add, ← ha, ← hb]
    exact Preadditive.add_comp _ _ _ _ _ _
  | single g r =>
    obtain ⟨f, hf⟩ := slantHom_neg R X (Γ := Γ) (m := m)
    have e : bd R (Finsupp.single g r) = Finsupp.single (fun i => g i.succ) r +
        ∑ j : Fin (m + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r := by
      have := groupHomology.inhomogeneousChains.d_single (A := Rep.trivial R Γ R) m g r
      refine this.trans ?_
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul R]
      simp
    have d : ((chainsN R).obj (BX Γ X)).d (m + 1) m =
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((BX Γ X).δ i) :=
      AlgebraicTopology.alternatingFaceMapComplex_obj_d _ m
    rw [e, ← hf (_ + _), map_add, map_sum, d, slantHom_single]
    have e2 : ∀ j : Fin (m + 1), f ((-1 : ℤ) ^ ((j : ℕ) + 1) • Finsupp.single (j.contractNth (· * ·) g) r) =
        (-1 : ℤ) ^ ((j : ℕ) + 1) • (ULift.up r : ULift.{1} R) • (free R).map (grpPt X (j.contractNth (· * ·) g)) :=
      fun j => by rw [map_zsmul, hf, slantHom_single]
    rw [Finset.sum_congr rfl fun j _ => e2 j, hf, slantHom_single]
    erw [Preadditive.comp_sum]
    rw [Fin.sum_univ_succ]
    congr 1
    · erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).1]
      exact one_smul ℤ _
    · refine Finset.sum_congr rfl fun j _ => ?_
      erw [Preadditive.comp_zsmul, Linear.smul_comp, ← Functor.map_comp, (h Γ X m g).2 j]
      rfl

/- English proof (translation)
Establish `d : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 = ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((sch.obj X).δ i)` using `AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0`. Establish `d0 : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 = 0`. Rewrite using `[d, Fin.sum_univ_two]`. Establish `: (sch.obj X).δ (0 : Fin (0 + 2)) = (sch.obj X).δ 1` using `rfl`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Use `((chainsN R).obj (sch.obj X)).extend_d_eq ComplexShape.embeddingDownNat (i := 0 + 1) (j := 0) (i' := -1) (j' := 0) (by simp) (by simp)` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Rewrite using `[d0]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem sch_d (R : Type) [CommRing R] (X : Scheme.{0}) : ((chains R).obj (sch.obj X)).d (-1) 0 = 0 := by
  have d : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 =
      ∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((sch.obj X).δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ 0
  have d0 : ((chainsN R).obj (sch.obj X)).d (0 + 1) 0 = 0 := by
    rw [d, Fin.sum_univ_two]
    have : (sch.obj X).δ (0 : Fin (0 + 2)) = (sch.obj X).δ 1 := rfl
    rw [this]; simp; rfl
  have := ((chainsN R).obj (sch.obj X)).extend_d_eq ComplexShape.embeddingDownNat (i := 0 + 1) (j := 0) (i' := -1) (j' := 0)
    (by simp) (by simp)
  refine this.trans ?_
  rw [d0]; simp; rfl

/- English proof (translation)
Rewrite using `[Cochain.δ_single f n m hm (p - 1) q' (by omega) hq, hK]`. Simplify using the standard rewrite rules.
-/
theorem single_congr {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q q' : ℤ} (f : K.X p ⟶ L.X q)
    (n m : ℤ) (hm : n + 1 = m) (hq : q + 1 = q') (hK : K.d (p - 1) p = 0) :
    δ n m (Cochain.single f n) = Cochain.single (f ≫ L.d q q') m := by
  rw [Cochain.δ_single f n m hm (p - 1) q' (by omega) hq, hK]
  simp

/- English proof (translation)
Introduce `R _ Γ _ X`. Use `⟨fun c => ?_, fun m b => ?_⟩` and prove the remaining obligations. Unfold `slantCo`. Rewrite using `[single_congr _ _ _ rfl rfl (sch_d R X)]`. Establish `z : IsZero (((chains R).obj (BX Γ X)).X (-((0 : ℕ) : ℤ) + 1))` using `((chainsN R).obj (BX Γ X)).isZero_extend_X ComplexShape.embeddingDownNat _ (fun i hi => by`.

Simplify using `at hi`. Use the proof step `omega)`. Rewrite using `[z.eq_of_tgt (_ ≫ _) 0]`. Simplify using the standard rewrite rules. Unfold `slantCo`.

Rewrite using `[single_congr (q' := -(m : ℤ)) _ _ _ (by omega) (by omega) (sch_d R X)]`. Use `congr 1`. Use `((chainsN R).obj (BX Γ X)).extend_d_eq ComplexShape.embeddingDownNat (i := m + 1) (j := m) (i' := -((m + 1 : ℕ) : ℤ)) (j' := -(m : ℤ)) (by simp) (by simp)` as an intermediate fact. Unfold `slantV`. Rewrite using `[← h R Γ X m b]`.

Use `erw [this, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem deltaCo_of (h : HomD) : DeltaCo := by
  intro R _ Γ _ X
  refine ⟨fun c => ?_, fun m b => ?_⟩
  · unfold slantCo
    rw [single_congr _ _ _ rfl rfl (sch_d R X)]
    have z : IsZero (((chains R).obj (BX Γ X)).X (-((0 : ℕ) : ℤ) + 1)) :=
      ((chainsN R).obj (BX Γ X)).isZero_extend_X ComplexShape.embeddingDownNat _ (fun i hi => by
        simp at hi; omega)
    rw [z.eq_of_tgt (_ ≫ _) 0]
    simp
  · unfold slantCo
    rw [single_congr (q' := -(m : ℤ)) _ _ _ (by omega) (by omega) (sch_d R X)]
    congr 1
    have := ((chainsN R).obj (BX Γ X)).extend_d_eq ComplexShape.embeddingDownNat (i := m + 1) (j := m)
      (i' := -((m + 1 : ℕ) : ℤ)) (j' := -(m : ℤ)) (by simp) (by simp)
    unfold slantV
    rw [← h R Γ X m b]
    erw [this, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
    rfl

/- English proof (translation)
Take `⟨a, _⟩` from `a`. Take `⟨b, _⟩` from `b`. Take `⟨c, hc⟩` from `c`. Take `rfl : a = c` from `ha`. Take `rfl : b = a + 1` from `hb`.

Conclude with `ComposableArrows.mkOfObjOfMapSucc_map_succ (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹) a hc`.
-/
theorem gmap1 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c : Fin n) (ha : a.val = c.val)
    (hb : b.val = c.val + 1) : (show Γ from (grpSimplex g).map f) = (g c)⁻¹ := by
  obtain ⟨a, _⟩ := a
  obtain ⟨b, _⟩ := b
  obtain ⟨c, hc⟩ := c
  obtain rfl : a = c := ha
  obtain rfl : b = a + 1 := hb
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹) a hc

/- English proof (translation)
Establish `h1 : a ≤ d.castSucc` using `by rw [Fin.le_def]; simp; omega`. Establish `h2 : d.castSucc ≤ b` using `by rw [Fin.le_def]; simp; omega`. Establish `e` using `(grpSimplex g).map_comp (homOfLE h1) (homOfLE h2)`. Establish `e1` using `gmap1 g _ _ (homOfLE h1) c ha (by simpa using hd)`. Establish `e2` using `gmap1 g _ _ (homOfLE h2) d (by simp) (by omega)`.

Rewrite using `[mul_inv_rev, ← e1, ← e2]`. Conclude with `e`.
-/
theorem gmap2 {Γ : Type} [Group Γ] {n : ℕ} (g : Fin n → Γ) (a b : Fin (n + 1)) (f : a ⟶ b) (c d : Fin n) (ha : a.val = c.val)
    (hd : d.val = c.val + 1) (hb : b.val = c.val + 2) : (show Γ from (grpSimplex g).map f) = (g c * g d)⁻¹ := by
  have h1 : a ≤ d.castSucc := by rw [Fin.le_def]; simp; omega
  have h2 : d.castSucc ≤ b := by rw [Fin.le_def]; simp; omega
  have e := (grpSimplex g).map_comp (homOfLE h1) (homOfLE h2)
  have e1 := gmap1 g _ _ (homOfLE h1) c ha (by simpa using hd)
  have e2 := gmap1 g _ _ (homOfLE h2) d (by simp) (by omega)
  rw [mul_inv_rev, ← e1, ← e2]
  exact e

/- English proof (translation)
Use `ComposableArrows.ext (fun _ => rfl) fun i hi => ?_` and prove the remaining obligations. Use `erw [Category.id_comp, Category.comp_id]`. Conclude with `(h ⟨i, hi⟩ _).trans (gmap1 g' _ _ _ ⟨i, hi⟩ rfl rfl).symm`.
-/
theorem nerve_ext {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : ∀ (i : Fin m) (f : j.succAbove i.castSucc ⟶ j.succAbove i.succ), (show Γ from (grpSimplex g).map f) = (g' i)⁻¹) :
    (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g' := by
  refine ComposableArrows.ext (fun _ => rfl) fun i hi => ?_
  erw [Category.id_comp, Category.comp_id]
  exact (h ⟨i, hi⟩ _).trans (gmap1 g' _ _ _ ⟨i, hi⟩ rfl rfl).symm

/- English proof (translation)
The claim follows from `nerve_ext g _ 0 fun i f => gmap1 g _ _ f i.succ (by simp) (by simp)`.
-/
theorem nerve_zero {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) :
    (nerve (SingleObj Γ)).δ 0 (grpSimplex g) = grpSimplex (fun i => g i.succ) :=
  nerve_ext g _ 0 fun i f => gmap1 g _ _ f i.succ (by simp) (by simp)

/- English proof (translation)
Unfold `Fin.succAbove`. Distinguish the cases in `h : i.val < j.val`. Rewrite using `[if_pos h, if_pos (show i.castSucc < j from h)]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, if_neg (show ¬ i.castSucc < j from h)]`.

Both sides reduce to the same expression.
-/
theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (i : Fin n) : (j.succAbove i).val = if i.val < j.val then i.val else i.val + 1 := by
  unfold Fin.succAbove
  by_cases h : i.val < j.val
  · rw [if_pos h, if_pos (show i.castSucc < j from h)]; rfl
  · rw [if_neg h, if_neg (show ¬ i.castSucc < j from h)]; rfl

/- English proof (translation)
Use `nerve_ext g _ _ fun i f => ?_` and prove the remaining obligations. Establish `a` using `val_succAbove j.succ i.castSucc`. Establish `b` using `val_succAbove j.succ i.succ`. Simplify using `only [Fin.val_succ, Fin.val_castSucc] at a b`. Break down `lt_trichotomy i.val j.val with h | h | h` into its components or cases.

Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ h]`. Conclude with `gmap1 g _ _ f _ (by rw [a, if_pos (by omega)]; rfl) (by rw [b, if_pos (by omega)]; rfl)`. Rewrite using `[Fin.contractNth_apply_of_eq _ _ _ _ h]`. Conclude with `gmap2 g _ _ f _ _ (by rw [a, if_pos (by omega)]; rfl) rfl (by rw [b, if_neg (by omega)]; rfl)`. Rewrite using `[Fin.contractNth_apply_of_gt _ _ _ _ h]`.

Conclude with `gmap1 g _ _ f _ (by rw [a, if_neg (by omega)]; rfl) (by rw [b, if_neg (by omega)]; rfl)`.
-/
theorem nerve_succ {Γ : Type} [Group Γ] {m : ℕ} (g : Fin (m + 1) → Γ) (j : Fin (m + 1)) :
    (nerve (SingleObj Γ)).δ j.succ (grpSimplex g) = grpSimplex (j.contractNth (· * ·) g) := by
  refine nerve_ext g _ _ fun i f => ?_
  have a := val_succAbove j.succ i.castSucc
  have b := val_succAbove j.succ i.succ
  simp only [Fin.val_succ, Fin.val_castSucc] at a b
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_pos (by omega)]; rfl) (by rw [b, if_pos (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h]
    exact gmap2 g _ _ f _ _ (by rw [a, if_pos (by omega)]; rfl) rfl (by rw [b, if_neg (by omega)]; rfl)
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    exact gmap1 g _ _ f _ (by rw [a, if_neg (by omega)]; rfl) (by rw [b, if_neg (by omega)]; rfl)

/- English proof (translation)
The claim follows from `(evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit`.
-/
theorem ev_pres (P Q : Spc) (n : SimplexCategoryᵒᵖ) : PreservesLimit (pair P Q) ((evaluation SimplexCategoryᵒᵖ PSh).obj n) :=
  (evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit

/- English proof (translation)
The claim follows from `ev_pres P Q n (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫ (prod.fst : P ⨯ Q ⟶ P).app n = u ∧ (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫ (prod.snd : P ⨯ Q ⟶ Q).app n = v := by …`.
-/
theorem lift_fst {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u : W ⟶ P.obj n) (v : W ⟶ Q.obj n) :
    haveI := ev_pres P Q n
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.fst : P ⨯ Q ⟶ P).app n = u ∧
    (prod.lift u v ≫ (PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q).inv) ≫
      (prod.snd : P ⨯ Q ⟶ Q).app n = v := by
  haveI := ev_pres P Q n
  constructor
  · erw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]
  · erw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

/- English proof (translation)
Use `haveI := ev_pres P Q n`. Conclude with `BinaryFan.IsLimit.hom_ext (isLimitOfHasBinaryProductOfPreservesLimit ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q) h1 h2`.
-/
theorem prod_ext {P Q : Spc} {n : SimplexCategoryᵒᵖ} {W : PSh} (u v : W ⟶ (P ⨯ Q).obj n)
    (h1 : u ≫ (prod.fst : P ⨯ Q ⟶ P).app n = v ≫ (prod.fst : P ⨯ Q ⟶ P).app n)
    (h2 : u ≫ (prod.snd : P ⨯ Q ⟶ Q).app n = v ≫ (prod.snd : P ⨯ Q ⟶ Q).app n) : u = v := by
  haveI := ev_pres P Q n
  exact BinaryFan.IsLimit.hom_ext
    (isLimitOfHasBinaryProductOfPreservesLimit ((evaluation SimplexCategoryᵒᵖ PSh).obj n) P Q) h1 h2

/- English proof (translation)
Establish `a` using `lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk (m + 1))) (W := yoneda.obj X) { app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))`. Establish `b` using `lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk m)) (W := yoneda.obj X) { app := fun U => TypeCat.ofHom fun _ => grpSimplex g', naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))`. Use `prod_ext _ _ ?_ ?_` and prove the remaining obligations. Use `Eq.trans ?_ b.1.symm` and prove the remaining obligations. Rewrite using `[Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]`.

Use `(congrArg (· ≫ (cst (SingleObj Γ)).δ j) a.1).trans ?_` and prove the remaining obligations. Use extensionality with `U x`. Conclude with `h`. Use `Eq.trans ?_ b.2.symm` and prove the remaining obligations. Rewrite using `[Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]`.

Conclude with `congrArg (· ≫ (sch.obj X).δ j) a.2`.
-/
theorem face_of {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (g : Fin (m + 1) → Γ) (g' : Fin m → Γ) (j : Fin (m + 2))
    (h : (nerve (SingleObj Γ)).δ j (grpSimplex g) = grpSimplex g') : grpPt X g ≫ (BX Γ X).δ j = grpPt X g' := by
  have a := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk (m + 1))) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  have b := lift_fst (P := cst (SingleObj Γ)) (Q := sch.obj X) (n := op (SimplexCategory.mk m)) (W := yoneda.obj X)
    { app := fun U => TypeCat.ofHom fun _ => grpSimplex g', naturality := fun _ _ _ => rfl } (𝟙 (yoneda.obj X))
  refine prod_ext _ _ ?_ ?_
  · refine Eq.trans ?_ b.1.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    refine (congrArg (· ≫ (cst (SingleObj Γ)).δ j) a.1).trans ?_
    ext U x
    exact h
  · refine Eq.trans ?_ b.2.symm
    rw [Category.assoc, SimplicialObject.δ_naturality, ← Category.assoc]
    exact congrArg (· ≫ (sch.obj X).δ j) a.2

/- English proof (translation)
Introduce `_ _ X _ g` and use `⟨face_of X g _ _ (nerve_zero g), fun j => face_of X g _ _ (nerve_succ g j)⟩`.
-/
theorem faces : Faces := fun _ _ X _ g =>
  ⟨face_of X g _ _ (nerve_zero g), fun j => face_of X g _ _ (nerve_succ g j)⟩

/- English proof (translation)
The claim follows from `goal_of (deltaCo_of (homD_of faces))`.
-/
theorem goal : LateralTheory.E.EtaleChapterDThree := goal_of (deltaCo_of (homD_of faces))

end LateralTheory.E.t_D3Cut
