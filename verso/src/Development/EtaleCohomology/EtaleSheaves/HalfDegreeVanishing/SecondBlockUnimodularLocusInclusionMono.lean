import Development.EtaleCohomology.EtaleSheaves.LeafGeomPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.HalfDegreeVanishing

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

def pv {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) : Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) :=
  ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x

def pe {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) : Sx E n X :=
  ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x

def pw {n : ℕ} {X : Scheme.{0}} (e : Sx E n X) : Fin (n + 1) ⥤ SingleObj (GL (Fin b) (Scheme.Γ.obj (op X))) :=
  (W.app (op (SimplexCategory.mk n))).app (op X) e

def pV {n : ℕ} {X : Scheme.{0}} (e : Sx E n X) : Fin (n + 1) ⥤ SingleObj (GL (Fin a) (Scheme.Γ.obj (op X))) :=
  (V.app (op (SimplexCategory.mk n))).app (op X) e

/- English proof (translation)
Establish `h` using `ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := bsumOf V W) (g := PGL.pr (a + b))) (op (SimplexCategory.mk n)) |> fun h => NatTrans.congr_app h (op X)) x`. Establish `h2` using `Functor.hcongr_hom h f`. Conclude with `(eq_of_heq h2).symm`.
-/
theorem cond {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    ((pv V W x).map f).1.1 = blockGL a b _ ((pV V (pe V W x)).map f) ((pw W (pe V W x)).map f) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := bsumOf V W) (g := PGL.pr (a + b)))
    (op (SimplexCategory.mk n)) |> fun h => NatTrans.congr_app h (op X)) x
  have h2 := Functor.hcongr_hom h f
  exact (eq_of_heq h2).symm

def wb {A : Type} (v : Fin (a + b) → A) : Fin b → A := fun i => v (Fin.natAdd a i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[blockGL_val]`. Simplify using `only [wb, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, Fin.sum_univ_add, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero …`.
-/
theorem wb_mulVec {A : Type} [CommRing A] (g : GL (Fin a) A) (h : GL (Fin b) A) (v : Fin (a + b) → A) :
    wb (a := a) ((blockGL a b A g h).val.mulVec v) = h.val.mulVec (wb (a := a) v) := by
  funext i
  rw [blockGL_val]
  simp only [wb, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, Fin.sum_univ_add,
    finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

/- English proof (translation)
Rewrite using `[eq_top_iff, ← hw, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[h]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ (M i j) (Ideal.subset_span (Set.mem_range_self j))`.
-/
theorem um_of {A : Type} [CommRing A] {m : ℕ} (w w' : Fin m → A) (M : Matrix (Fin m) (Fin m) A) (h : w = M.mulVec w')
    (hw : Ideal.span (Set.range w) = ⊤) : Ideal.span (Set.range w') = ⊤ := by
  rw [eq_top_iff, ← hw, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [h]
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ (M i j) (Ideal.subset_span (Set.mem_range_self j))

def AllSec {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) : Prop :=
  ∀ i, Ideal.span (Set.range (wb (a := a) ((pv V W x).obj i).1)) = ⊤

/- English proof (translation)
Introduce `i`. Establish `f : (0 : Fin (n + 1)) ⟶ i` using `homOfLE (Fin.zero_le i)`. Establish `e` using `((pv V W x).map f).2`. Rewrite `e` using `[cond]`. Establish `e2` using `congrArg (wb (a := a)) e`.

Rewrite `e2` using `[wb_mulVec]`. Set `gh : GL (Fin b) (Scheme.Γ.obj (op X))` to `(pw W (pe V W x)).map f`. Use `um_of _ _ (gh⁻¹.val * (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • (1 : Matrix (Fin b) (Fin b) _)) ?_ h` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `e3 : gh.val.mulVec (wb (a` using `a) ((pv V W x).obj 0).1) = (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj i).1 := e2`.

Rewrite using `[← e3, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Both sides reduce to the same expression.
-/
theorem allSec_of {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) (h : Second V W x) : AllSec V W x := by
  intro i
  have f : (0 : Fin (n + 1)) ⟶ i := homOfLE (Fin.zero_le i)
  have e := ((pv V W x).map f).2
  rw [cond] at e
  have e2 := congrArg (wb (a := a)) e
  rw [wb_mulVec] at e2
  let gh : GL (Fin b) (Scheme.Γ.obj (op X)) := (pw W (pe V W x)).map f
  refine um_of _ _ (gh⁻¹.val * (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • (1 : Matrix (Fin b) (Fin b) _)) ?_ h
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have e3 : gh.val.mulVec (wb (a := a) ((pv V W x).obj 0).1) =
      (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj i).1 := e2
  rw [← e3, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

/- English proof (translation)
Establish `h` using `ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x`. Unfold `pv`. Use `erw [h]`. Both sides reduce to the same expression.
-/
theorem pv_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (i : Fin (n + 1)) :
    ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).obj i).1 =
      Scheme.Γ.map k.op ∘ ((pv V W x).obj i).1 := by
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  unfold pv
  erw [h]
  rfl

/- English proof (translation)
Establish `h` using `ConcreteCategory.congr_hom (NatTrans.congr_app ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x`. Unfold `pv`. Use `erw [h]`. Both sides reduce to the same expression.
-/
theorem pv_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X)
    (i : Fin (m + 1)) :
    (pv V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x)).obj i = (pv V W x).obj (θ.toOrderHom i) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x
  unfold pv
  erw [h]
  rfl

/- English proof (translation)
Introduce `i`. Establish `e : wb (a` using `a) ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).obj i).1 = (Scheme.Γ.map k.op).hom ∘ wb (a := a) ((pv V W x).obj i).1 := by`. Rewrite using `[pv_res]`. Both sides reduce to the same expression. Rewrite using `[e, Set.range_comp, ← Ideal.map_span, hx i, Ideal.map_top]`.
-/
theorem allSec_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (hx : AllSec V W x) :
    AllSec V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) := by
  intro i
  have e : wb (a := a) ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).obj i).1 =
      (Scheme.Γ.map k.op).hom ∘ wb (a := a) ((pv V W x).obj i).1 := by
    rw [pv_res]; rfl
  rw [e, Set.range_comp, ← Ideal.map_span, hx i, Ideal.map_top]

/- English proof (translation)
Introduce `i`. Rewrite using `[pv_simp]`. Conclude with `hx _`.
-/
theorem allSec_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X)
    (hx : AllSec V W x) : AllSec V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x) := by
  intro i
  rw [pv_simp]
  exact hx _

def U2obj (n : SimplexCategoryᵒᵖ) : PSh where
  obj X := {x : ((PB (bsumOf V W)).obj n).obj X // AllSec V W (n := n.unop.len) (X := X.unop) x}
  map k := TypeCat.ofHom fun x => ⟨((PB (bsumOf V W)).obj n).map k x.1, allSec_res V W k.unop x.1 x.2⟩
  map_id X := by ext x; exact FunctorToTypes.map_id_apply _ _
  map_comp f g := by ext x; exact FunctorToTypes.map_comp_apply _ _ _ _

def U2 : Spc where
  obj := U2obj V W
  map θ :=
    { app := fun X => TypeCat.ofHom fun x => ⟨(((PB (bsumOf V W)).map θ).app X) x.1, allSec_simp V W θ.unop x.1 x.2⟩
      naturality := fun X Y k => by
        ext x
        apply Subtype.ext
        dsimp [U2obj]
        exact FunctorToTypes.naturality ((PB (bsumOf V W)).map θ) k x.1 }
  map_id n := by
    ext X x
    apply Subtype.ext
    dsimp [U2obj]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app ((PB (bsumOf V W)).map_id n) X) x.1
  map_comp f g := by
    ext X x
    apply Subtype.ext
    dsimp [U2obj]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app ((PB (bsumOf V W)).map_comp f g) X) x.1

def f2 : U2 V W ⟶ PB (bsumOf V W) where
  app n := { app := fun X => TypeCat.ofHom Subtype.val, naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

/- English proof (translation)
Use `@NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun n => ?_` and prove the remaining obligations. Use `@NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun X => ?_` and prove the remaining obligations. Rewrite using `[mono_iff_injective]`. Introduce `x y h`. Conclude with `Subtype.ext h`.
-/
theorem secondBlockUnimodularLocus_inclusion_mono : Mono (f2 V W) := by
  refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun n => ?_
  refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun X => ?_
  rw [mono_iff_injective]
  intro x y h
  exact Subtype.ext h

end LateralTheory.E.HalfDegreeVanishing

namespace LateralTheory.E.HalfDegreeVanishing

def LeafMapW : Prop := ∀ {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)),
  ∃ g : U2 V W ⟶ PGL b, g ≫ PGL.pr b = f2 V W ≫ PB.pr _ ≫ W ∧
    g ≫ PGL.line b = f2 V W ≫ pullback.snd (bsumOf V W) (PGL.pr (a + b)) ≫ PGL.line (a + b)

/- English proof (translation)
Introduce `E a b V W`. Take `⟨g, hg1, hg2⟩` from `hM V W`. Use `⟨U2 V W, f2 V W, pullback.lift (f2 V W ≫ PB.pr _) g (by rw [hg1, Category.assoc]), secondBlockUnimodularLocus_inclusion_mono V W, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `pullback.lift_fst _ _ _`. Rewrite using `[PB.line, ← Category.assoc, pullback.lift_snd, hg2]`.

Introduce `n X x h`. Conclude with `⟨⟨x, allSec_of V W x h⟩, rfl⟩`.
-/
theorem LeafHalf2_of (hM : LeafMapW) : LeafHalf2 := by
  intro E a b V W
  obtain ⟨g, hg1, hg2⟩ := hM V W
  refine ⟨U2 V W, f2 V W, pullback.lift (f2 V W ≫ PB.pr _) g (by rw [hg1, Category.assoc]), secondBlockUnimodularLocus_inclusion_mono V W, ?_, ?_, ?_⟩
  · exact pullback.lift_fst _ _ _
  · rw [PB.line, ← Category.assoc, pullback.lift_snd, hg2]
  · intro n X x h
    exact ⟨⟨x, allSec_of V W x h⟩, rfl⟩

end LateralTheory.E.HalfDegreeVanishing
