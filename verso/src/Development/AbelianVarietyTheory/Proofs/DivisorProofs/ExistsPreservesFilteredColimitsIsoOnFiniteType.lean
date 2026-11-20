import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeIntHomFilteredColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FinExt

def finTypeZ : ObjectProperty CommRingCat.{0} := fun A => Algebra.FiniteType ℤ A

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  (E : finTypeZ.ι.LeftExtension G)

/- English proof (translation)
Take `⟨k, a, b, -⟩` from `IsFilteredOrEmpty.cocone_objs j j'`. Establish `hk : (ψ ≫ D.map a) ≫ c.ι.app k = (ψ' ≫ D.map b) ≫ c.ι.app k`. Simplify `h` using `only [Category.assoc, Cocone.w]`. Take `⟨l, f, hf⟩` from `(GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj X) X.property J D c hc).2 k _ _ hk`. Establish `e1 : s.ι.app j = E.right.map (D.map (a ≫ f)) ≫ s.ι.app l` using `(s.w (a ≫ f)).symm`.

Establish `e2 : s.ι.app j' = E.right.map (D.map (b ≫ f)) ≫ s.ι.app l` using `(s.w (b ≫ f)).symm`. Rewrite using `[e1, e2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]`. Use `congr 3`. Simplify `hf` using `only [Functor.map_comp, Category.assoc]`.
-/
lemma comp_eq_of_fac {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
    {c : Cocone D} (hc : IsColimit c) (s : Cocone (D ⋙ E.right))
    (X : finTypeZ.FullSubcategory) {j j' : J} (ψ : finTypeZ.ι.obj X ⟶ D.obj j)
    (ψ' : finTypeZ.ι.obj X ⟶ D.obj j') (h : ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j') :
    E.hom.app X ≫ E.right.map ψ ≫ s.ι.app j = E.hom.app X ≫ E.right.map ψ' ≫ s.ι.app j' := by
  obtain ⟨k, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j j'
  have hk : (ψ ≫ D.map a) ≫ c.ι.app k = (ψ' ≫ D.map b) ≫ c.ι.app k := by
    simpa only [Category.assoc, Cocone.w] using h
  obtain ⟨l, f, hf⟩ := (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj X) X.property J D c hc).2 k _ _ hk
  have e1 : s.ι.app j = E.right.map (D.map (a ≫ f)) ≫ s.ι.app l := (s.w (a ≫ f)).symm
  have e2 : s.ι.app j' = E.right.map (D.map (b ≫ f)) ≫ s.ι.app l := (s.w (b ≫ f)).symm
  rw [e1, e2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 3
  simpa only [Functor.map_comp, Category.assoc] using hf

end

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  {E : finTypeZ.ι.LeftExtension G}

/- English proof (translation)
Use `⟨fun J _ _ => ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩` and prove the remaining obligations. Establish `hfac` using `fun (g : CostructuredArrow finTypeZ.ι c.pt) => (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj g.left) g.left.property J D c hc).1 g.hom`. Use `choose j ψ hψ using hfac`. Set `t : ∀ s : Cocone (D ⋙ E.right), Cocone (CostructuredArrow.proj finTypeZ.ι c.pt ⋙ G)` to `fun s => { pt := s.pt ι := { app := fun g => E.hom.app g.left ≫ E.right.map (ψ g) ≫ s.ι.app (j g) naturality := by`. Introduce `g g' f`.

Establish `hn` using `E.hom.naturality f.left`. Simplify using `at hn ⊢`. Simplify using `only [Category.comp_id]`. Express the relevant statement in the definitionally equal form `G.map f.left ≫ _ = _`. Use `erw [reassoc_of% hn, ← Functor.map_comp_assoc]`.

Conclude with `comp_eq_of_fac E hc s g.left _ _ (by rw [Category.assoc, hψ g', hψ g]; exact CostructuredArrow.w f) } }`. Establish `ht : ∀ (s : Cocone (D ⋙ E.right)) (X : finTypeZ.FullSubcategory) (φ : finTypeZ.ι.obj X ⟶ c.pt), E.hom.app X ≫ E.right.map φ ≫ (hE c.pt).desc (t s) = E.hom.app X ≫ E.right.map (ψ (CostructuredArrow.mk φ)) ≫ s.ι.app (j (CostructuredArrow.mk φ))`. Introduce `s X φ`. Use `(hE c.pt).fac (t s) (CostructuredArrow.mk φ)` as an intermediate fact. Conclude with `(Category.assoc _ _ _).symm.trans this`.

Use `exact`. Use the proof step `{ desc := fun s => (hE c.pt).desc (t s) fac := fun s k => by`. Apply `(hE (D.obj k)).hom_ext'` to reduce the goal to its premises. Introduce `X φ`. Establish `h1` using `ht s X (φ ≫ c.ι.app k)`.

Simplify using `only [Functor.mapCocone_ι_app]`. Use `erw [← Functor.map_comp_assoc, h1]`. Conclude with `comp_eq_of_fac E hc s X _ _ (hψ _)`. Use `uniq := fun s m hm => by`. Apply `(hE c.pt).hom_ext'` to reduce the goal to its premises.

Introduce `X φ`. Rewrite using `[ht s X φ]`. Establish `h2` using `hψ (CostructuredArrow.mk φ)`. Simplify using `at h2`. Use `conv_lhs => rw [← h2, Functor.map_comp, Category.assoc]`.

Establish `h3` using `hm (j (CostructuredArrow.mk φ))`. Simplify using `only [Functor.mapCocone_ι_app] at h3`. Rewrite using `[h3] }`.
-/
theorem preservesFilteredColimits_of_isPointwiseLeftKanExtension
    (hE : E.IsPointwiseLeftKanExtension) : PreservesFilteredColimitsOfSize.{0, 0} E.right := by
  refine ⟨fun J _ _ => ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  have hfac := fun (g : CostructuredArrow finTypeZ.ι c.pt) =>
    (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj g.left) g.left.property J D c hc).1 g.hom
  choose j ψ hψ using hfac
  let t : ∀ s : Cocone (D ⋙ E.right), Cocone (CostructuredArrow.proj finTypeZ.ι c.pt ⋙ G) :=
    fun s =>
    { pt := s.pt
      ι := { app := fun g => E.hom.app g.left ≫ E.right.map (ψ g) ≫ s.ι.app (j g)
             naturality := by
               intro g g' f
               have hn := E.hom.naturality f.left
               dsimp at hn ⊢
               simp only [Category.comp_id]
               change G.map f.left ≫ _ = _
               erw [reassoc_of% hn, ← Functor.map_comp_assoc]
               exact comp_eq_of_fac E hc s g.left _ _
                 (by rw [Category.assoc, hψ g', hψ g]; exact CostructuredArrow.w f) } }
  have ht : ∀ (s : Cocone (D ⋙ E.right)) (X : finTypeZ.FullSubcategory) (φ : finTypeZ.ι.obj X ⟶ c.pt),
      E.hom.app X ≫ E.right.map φ ≫ (hE c.pt).desc (t s) =
        E.hom.app X ≫ E.right.map (ψ (CostructuredArrow.mk φ)) ≫ s.ι.app (j (CostructuredArrow.mk φ)) := by
    intro s X φ
    have := (hE c.pt).fac (t s) (CostructuredArrow.mk φ)
    exact (Category.assoc _ _ _).symm.trans this
  exact
  { desc := fun s => (hE c.pt).desc (t s)
    fac := fun s k => by
      apply (hE (D.obj k)).hom_ext'
      intro X φ
      have h1 := ht s X (φ ≫ c.ι.app k)
      simp only [Functor.mapCocone_ι_app]
      erw [← Functor.map_comp_assoc, h1]
      exact comp_eq_of_fac E hc s X _ _ (hψ _)
    uniq := fun s m hm => by
      apply (hE c.pt).hom_ext'
      intro X φ
      rw [ht s X φ]
      have h2 := hψ (CostructuredArrow.mk φ)
      dsimp at h2
      conv_lhs => rw [← h2, Functor.map_comp, Category.assoc]
      have h3 := hm (j (CostructuredArrow.mk φ))
      simp only [Functor.mapCocone_ι_app] at h3
      rw [h3] }

end

/- English proof (translation)
Introduce `𝒜 _ _ M`. Use `haveI : HasColimitsOfSize.{0, 1} 𝒜 := hasColimitsOfSizeShrink.{0, 1, 1, 1} 𝒜`. Use `haveI : finTypeZ.ι.HasPointwiseLeftKanExtension (finTypeZ.ι ⋙ M) := fun _ => inferInstance`. Set `E` to `Functor.LeftExtension.mk _ (finTypeZ.ι.pointwiseLeftKanExtensionUnit (finTypeZ.ι ⋙ M))`. Establish `hE : E.IsPointwiseLeftKanExtension` using `finTypeZ.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _`.

Set `φ` to `hE.homFrom (Functor.LeftExtension.mk M (𝟙 _))`. Use `⟨E.right, φ.right, preservesFilteredColimits_of_isPointwiseLeftKanExtension hE, fun A hA => ?_⟩` and prove the remaining obligations. Set `X : finTypeZ.FullSubcategory` to `⟨A, hA⟩`. Establish `h1 : IsIso (E.hom.app X)` using `(hE (finTypeZ.ι.obj X)).isIso_hom_app`. Establish `h2 : E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X) = 𝟙 _`.

Use `congr_app (StructuredArrow.w φ) X` as an intermediate fact. Simplify using `using this`. Establish `h4 : IsIso (E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X))`. Rewrite using `[h2]`. Conclude with `⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩`.

Conclude with `IsIso.of_isIso_comp_left (E.hom.app X) (φ.right.app (finTypeZ.ι.obj X))`.
-/
theorem exists_preservesFilteredColimits_isIso :
    ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜),
      ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧
        (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) := by
  intro 𝒜 _ _ M
  haveI : HasColimitsOfSize.{0, 1} 𝒜 := hasColimitsOfSizeShrink.{0, 1, 1, 1} 𝒜
  haveI : finTypeZ.ι.HasPointwiseLeftKanExtension (finTypeZ.ι ⋙ M) := fun _ => inferInstance
  let E := Functor.LeftExtension.mk _ (finTypeZ.ι.pointwiseLeftKanExtensionUnit (finTypeZ.ι ⋙ M))
  have hE : E.IsPointwiseLeftKanExtension :=
    finTypeZ.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _
  let φ := hE.homFrom (Functor.LeftExtension.mk M (𝟙 _))
  refine ⟨E.right, φ.right, preservesFilteredColimits_of_isPointwiseLeftKanExtension hE,
    fun A hA => ?_⟩
  let X : finTypeZ.FullSubcategory := ⟨A, hA⟩
  have h1 : IsIso (E.hom.app X) := (hE (finTypeZ.ι.obj X)).isIso_hom_app
  have h2 : E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X) = 𝟙 _ := by
    have := congr_app (StructuredArrow.w φ) X
    simpa using this
  have h4 : IsIso (E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X)) := by
    rw [h2]; exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  exact IsIso.of_isIso_comp_left (E.hom.app X) (φ.right.app (finTypeZ.ι.obj X))

end GlobalTheory.FinExt
