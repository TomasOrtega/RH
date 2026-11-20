import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem pull_bij_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eqv_of_iso (R : Type) [CommRing R] {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (g : E₁' ⟶ E₂')
    (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') (w : f ≫ e₂.hom = e₁.hom ≫ g) (F : Shv R) (h : Eqv R g F) : Eqv R f F := by
  have hf : f = e₁.hom ≫ g ≫ e₂.inv := by rw [← Category.assoc, ← w, Category.assoc, e₂.hom_inv_id, Category.comp_id]
  have hE : ∀ {E E' : Spc} (u : E ⟶ E'), Eqv R u F ↔ ∀ n, Function.Bijective (pull R u F n) := fun _ => Iff.rfl
  rw [hE] at h ⊢
  intro n
  have key : pull R f F n = (pull R e₁.hom F n).comp ((pull R g F n).comp (pull R e₂.inv F n)) := by
    ext x; simp only [hf, pull_comp, AddMonoidHom.comp_apply]
  rw [key]
  exact (pull_bij_of_iso R e₁ F n).comp ((h n).comp (pull_bij_of_iso R e₂.symm F n))

def LeafTailRep : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (φ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : disc.obj ((PR (d + 1) 1 R).obj n) ≅ sch.obj (off (Polynomial A) (I.map Polynomial.C)))
      (e₂ : disc.obj ((PR d 0 R).obj n) ≅ sch.obj (off A I)),
      disc.map ((prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n) ≫ e₂.hom =
        e₁.hom ≫ sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem LeafTail_of (hRep : LeafTailRep) (hH : LeafHtpy) : LeafTail := by
  intro hyp q _ d R _ hq i
  obtain ⟨hA1, -, hA3, hA4, -, -, -, -, -, hC4, -, -⟩ := hyp
  apply hA3
  intro n
  obtain ⟨A, _, I, φ, hI, h, e₁, e₂, w⟩ := hRep d R n
  have hqA : IsUnit (q : A) := by simpa using hq.map φ
  exact eqv_of_iso _ _ _ e₁ e₂ w _ (hH hA1 hA4 hC4 q A I hI hqA h i)

end LateralTheory.CohomologicalPurity.Thom
