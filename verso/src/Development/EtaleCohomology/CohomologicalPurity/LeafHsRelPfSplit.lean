import Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPf

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex Pretriangulated

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

/- English proof (translation)
Take `⟨x, rfl⟩` from `x.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom f) x (zero_add n))) = _`. Rewrite using `[CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp]`. Use `congr 1`. Use extensionality with `p : 1`.

Simplify using `[zcomp, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]`. Both sides reduce to the same expression.
-/
theorem toHom_pull (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    CohomologyClass.toHom (HK.pull R f F n x) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.toHom (CohomologyClass.mk (zcomp (Cocycle.ofHom f) x (zero_add n))) = _
  rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp]
  congr 1
  ext p : 1
  simp [zcomp, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]
  rfl

/- English proof (translation)
Introduce `R _ K L g r hgr F n`. Establish `hT` using `HomotopyCategory.mappingCone_triangleh_distinguished g`. Set `Q` to `HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)`. Establish `z12 : Q.map g ≫ Q.map (mappingCone.inr g) = 0` using `comp_distTriang_mor_zero₁₂ _ hT`. Set `m3 : Q.obj (mappingCone g) ⟶ (Q.obj K)⟦(1 : ℤ)⟧` to `(mappingCone.triangleh g).mor₃`.

Establish `z31 : m3 ≫ (Q.map g)⟦(1 : ℤ)⟧' = 0` using `comp_distTriang_mor_zero₃₁ _ hT`. Establish `ex2 : ∀ {X} (f : Q.obj L ⟶ X), Q.map g ≫ f = 0 → ∃ w : Q.obj (mappingCone g) ⟶ X, f = Q.map (mappingCone.inr g) ≫ w` using `fun f hf => Triangle.yoneda_exact₂ _ hT f hf`. Establish `ex3 : ∀ {X} (f : Q.obj (mappingCone g) ⟶ X), Q.map (mappingCone.inr g) ≫ f = 0 → ∃ w : (Q.obj K)⟦(1 : ℤ)⟧ ⟶ X, f = m3 ≫ w` using `fun f hf => Triangle.yoneda_exact₃ _ hT f hf`. Establish `hinj : ∀ {M : Cx R} (a b : HK R M F n), CohomologyClass.toHom a = CohomologyClass.toHom b → a = b` using `fun a b h => (CohomologyClass.toHom_bijective _ _ _).1 h`. Use `⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩` and prove the remaining obligations.

Apply `hinj` to reduce the goal to its premises. Establish `h0 : Q.map (mappingCone.inr g) ≫ CohomologyClass.toHom x = 0`. Rewrite using `[← toHom_pull, hx, map_zero]`. Take `⟨w, hw⟩` from `ex3 _ h0`. Rewrite using `[hw, map_zero]`.

Establish `: w = (Q.map g)⟦(1 : ℤ)⟧' ≫ (Q.map r)⟦(1 : ℤ)⟧' ≫ w`. Rewrite using `[← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hgr, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]`. Rewrite using `[this, ← Category.assoc, z31, zero_comp]`. Establish `h0 : Q.map g ≫ CohomologyClass.toHom y = 0`. Rewrite using `[← toHom_pull, hy, map_zero]`.

Take `⟨w, hw⟩` from `ex2 _ h0`. Take `⟨x, hx⟩` from `(CohomologyClass.toHom_bijective (mappingCone g) _ _).2 w`. Use `⟨x, hinj _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[toHom_pull, hx, hw]`. Introduce and unpack `⟨x, rfl⟩`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[toHom_pull, toHom_pull, map_zero, ← Category.assoc, z12, zero_comp]`.
-/
theorem leafConeSplit : LeafConeSplit := by
  intro R _ K L g r hgr F n
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished g
  let Q := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
  have z12 : Q.map g ≫ Q.map (mappingCone.inr g) = 0 := comp_distTriang_mor_zero₁₂ _ hT
  let m3 : Q.obj (mappingCone g) ⟶ (Q.obj K)⟦(1 : ℤ)⟧ := (mappingCone.triangleh g).mor₃
  have z31 : m3 ≫ (Q.map g)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have ex2 : ∀ {X} (f : Q.obj L ⟶ X), Q.map g ≫ f = 0 → ∃ w : Q.obj (mappingCone g) ⟶ X,
      f = Q.map (mappingCone.inr g) ≫ w := fun f hf => Triangle.yoneda_exact₂ _ hT f hf
  have ex3 : ∀ {X} (f : Q.obj (mappingCone g) ⟶ X), Q.map (mappingCone.inr g) ≫ f = 0 →
      ∃ w : (Q.obj K)⟦(1 : ℤ)⟧ ⟶ X, f = m3 ≫ w :=
    fun f hf => Triangle.yoneda_exact₃ _ hT f hf
  have hinj : ∀ {M : Cx R} (a b : HK R M F n), CohomologyClass.toHom a = CohomologyClass.toHom b → a = b :=
    fun a b h => (CohomologyClass.toHom_bijective _ _ _).1 h
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · apply hinj
    have h0 : Q.map (mappingCone.inr g) ≫ CohomologyClass.toHom x = 0 := by
      rw [← toHom_pull, hx, map_zero]
    obtain ⟨w, hw⟩ := ex3 _ h0
    rw [hw, map_zero]
    have : w = (Q.map g)⟦(1 : ℤ)⟧' ≫ (Q.map r)⟦(1 : ℤ)⟧' ≫ w := by
      rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hgr, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    rw [this, ← Category.assoc, z31, zero_comp]
  · have h0 : Q.map g ≫ CohomologyClass.toHom y = 0 := by
      rw [← toHom_pull, hy, map_zero]
    obtain ⟨w, hw⟩ := ex2 _ h0
    obtain ⟨x, hx⟩ := (CohomologyClass.toHom_bijective (mappingCone g) _ _).2 w
    refine ⟨x, hinj _ _ ?_⟩
    rw [toHom_pull, hx, hw]
  · rintro ⟨x, rfl⟩
    apply hinj
    rw [toHom_pull, toHom_pull, map_zero, ← Category.assoc, z12, zero_comp]

def LeafDblCok : Prop := ∀ (R : Type) [CommRing R] (P : Arrow Spc), Mono P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (dbl_sq R P) n))

/- English proof (translation)
Introduce `R _ P h`. Establish `hi : Mono (dbl.inr P)` using `⟨fun a b e => by`. Use `congrArg (· ≫ dbl.fold P) e` as an intermediate fact. Simplify `this⟩` using `[Category.assoc, dbl.inr_fold]`. Conclude with `hC R _ _ _ _ (dbl_sq R P) (leafChainsMono R _ h) (leafChainsMono R _ hi) (hK R P h)`.
-/
theorem leafDblConeQI_of (hC : LeafConeCok) (hK : LeafDblCok) : LeafDblConeQI := by
  intro R _ P h
  have hi : Mono (dbl.inr P) := ⟨fun a b e => by
    have := congrArg (· ≫ dbl.fold P) e
    simpa [Category.assoc, dbl.inr_fold] using this⟩
  exact hC R _ _ _ _ (dbl_sq R P) (leafChainsMono R _ h) (leafChainsMono R _ hi) (hK R P h)

/- English proof (translation)
The claim follows from `leafHsRel_of (leafDblConeQI_of hC hK) leafConeSplit`.
-/
theorem etale_relative_cohomology_iso_of_cone_and_double_cokernel_isos (hC : LeafConeCok) (hK : LeafDblCok) : LeafHsRel :=
  leafHsRel_of (leafDblConeQI_of hC hK) leafConeSplit

end LateralTheory.CohomologicalPurity.Thom.ExcSp
