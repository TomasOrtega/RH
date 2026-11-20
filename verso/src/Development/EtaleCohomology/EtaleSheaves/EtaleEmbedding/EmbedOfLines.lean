import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def LineChart : Prop := ∀ {L S : Scheme.{0}} (l : L ⟶ S), IsLine l → ∀ (R : Type) [CommRing R]
  (j0 : Spec (CommRingCat.of R) ⟶ S), IsOpenImmersion j0 →
    ∃ j : Spec (CommRingCat.of (Polynomial R)) ⟶ L, IsOpenImmersion j ∧
      j ≫ l = Spec.map (CommRingCat.ofHom Polynomial.C) ≫ j0

/- English proof (translation)
Introduce `A _ n`. Proceed by induction on `n with`. Consider the case `zero`. Set `E` to `(MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv.toCommRingCatIso`. Establish `hE : E.hom = CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin 0) A))`.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Conclude with `(MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.commutes a`. Use `⟨Spec (CommRingCat.of A), 𝟙 _, Spec.map E.hom, IterLine.iso _ inferInstance, inferInstance, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.comp_id, hE]`. Consider the case `succ n ih`. Take `⟨P, q, j, hq, hj, hjq⟩` from `ih`. Take `⟨L, l, hl⟩` from `hEx P`. Take `⟨j1, hj1, hj1l⟩` from `hLC l hl (MvPolynomial (Fin n) A) j hj`.

Set `F` to `(MvPolynomial.finSuccEquiv A n).symm`. Set `E` to `F.toRingEquiv.toCommRingCatIso`. Establish `hE : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom Polynomial.C ≫ E.hom = CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin (n + 1)) A))`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises.

Introduce `a`. Establish `h1 : (Polynomial.C (algebraMap A (MvPolynomial (Fin n) A) a)) = algebraMap A (Polynomial (MvPolynomial (Fin n) A)) a` using `rfl`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Rewrite using `[h1]`. Conclude with `F.commutes a`.

Establish `hj1'` using `hj1`. Use `⟨L, l ≫ q, Spec.map E.hom ≫ j1, IterLine.comp l q hl hq, inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, reassoc_of% hj1l, hjq, ← hE, Spec.map_comp, Spec.map_comp, Category.assoc]`.
-/
theorem chart_of (hEx : LineEx) (hLC : LineChart) : Chart := by
  intro A _ n
  induction n with
  | zero =>
    let E := (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv.toCommRingCatIso
    have hE : E.hom = CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin 0) A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.commutes a
    refine ⟨Spec (CommRingCat.of A), 𝟙 _, Spec.map E.hom, IterLine.iso _ inferInstance, inferInstance, ?_⟩
    rw [Category.comp_id, hE]
  | succ n ih =>
    obtain ⟨P, q, j, hq, hj, hjq⟩ := ih
    obtain ⟨L, l, hl⟩ := hEx P
    obtain ⟨j1, hj1, hj1l⟩ := hLC l hl (MvPolynomial (Fin n) A) j hj
    let F := (MvPolynomial.finSuccEquiv A n).symm
    let E := F.toRingEquiv.toCommRingCatIso
    have hE : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom Polynomial.C ≫ E.hom =
        CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin (n + 1)) A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have h1 : (Polynomial.C (algebraMap A (MvPolynomial (Fin n) A) a)) =
          algebraMap A (Polynomial (MvPolynomial (Fin n) A)) a := rfl
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      rw [h1]
      exact F.commutes a
    have hj1' := hj1
    refine ⟨L, l ≫ q, Spec.map E.hom ≫ j1, IterLine.comp l q hl hq, inferInstance, ?_⟩
    rw [Category.assoc, reassoc_of% hj1l, hjq, ← hE, Spec.map_comp, Spec.map_comp, Category.assoc]

end LateralTheory.E.EmbedPf
