import Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev Uo (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Scheme.{0} :=
  (off (MvPolynomial (Fin d) R) I).toScheme

abbrev Gm : Scheme.{0} := Spec (CommRingCat.of (LaurentPolynomial ℤ))

def gmU (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Uo d R I ⨯ Gm ⟶ Uo d R I := prod.fst

def LeafWGm : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Smooth (gmU d R I) ∧ Surjective (gmU d R I)

def LeafWTors : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I →
  ∃ e : pullback (wb d R) (pr d R).hom ≅ cech (gmU d R I),
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → g ≫ e.hom ≫ cechAug (gmU d R I) = 𝟙 _

/- English proof (translation)
Introduce `n`. Use `Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, e.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, e.hom_inv_id, pull_id]`.
-/
theorem eqv_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

/- English proof (translation)
Introduce `n`. Establish `: ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n)` using `funext fun x => pull_comp R f g F n x`. Rewrite using `[this]`. Conclude with `(hf n).comp (hg n)`.
-/
theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

/- English proof (translation)
Introduce `n`. Establish `hid : ∀ x, pull R g F n (pull R s F n x) = x` using `fun x => by rw [← pull_comp, h, pull_id]`. Establish `hsurj : Function.Surjective (pull R g F n)` using `fun x => ⟨_, hid x⟩`. Use `⟨fun a b hab => ?_, hsurj⟩` and prove the remaining obligations. Take `⟨a', rfl⟩` from `(hs n).2 a`.

Take `⟨b', rfl⟩` from `(hs n).2 b`. Rewrite `hab` using `[hid, hid]`. Rewrite using `[hab]`.
-/
theorem eqv_of_section (R : Type) [CommRing R] {E E' : Spc} (g : E ⟶ E') (s : E' ⟶ E) (F : Shv R)
    (h : g ≫ s = 𝟙 _) (hs : Eqv R s F) : Eqv R g F := by
  intro n
  have hid : ∀ x, pull R g F n (pull R s F n x) = x := fun x => by rw [← pull_comp, h, pull_id]
  have hsurj : Function.Surjective (pull R g F n) := fun x => ⟨_, hid x⟩
  refine ⟨fun a b hab => ?_, hsurj⟩
  obtain ⟨a', rfl⟩ := (hs n).2 a
  obtain ⟨b', rfl⟩ := (hs n).2 b
  rw [hid, hid] at hab; rw [hab]

/- English proof (translation)
Introduce `hH q _ d R _ I hI hq g hg i`. Take `⟨e, he⟩` from `hT d R I hI`. Take `⟨hsm, hsu⟩` from `hGm d R I`. Establish `hA2 : Eqv _ (cechAug (gmU d R I)) (tw q i)` using `hH.2.1 _ (gmU d R I) (tw q i)`. Conclude with `eqv_of_section _ g _ _ (he g hg) (eqv_comp _ _ _ _ (eqv_of_iso _ e _) hA2)`.
-/
theorem LeafWEqvL_of (hGm : LeafWGm) (hT : LeafWTors) : LeafWEqvL := by
  intro hH q _ d R _ I hI hq g hg i
  obtain ⟨e, he⟩ := hT d R I hI
  obtain ⟨hsm, hsu⟩ := hGm d R I
  have hA2 : Eqv _ (cechAug (gmU d R I)) (tw q i) := hH.2.1 _ (gmU d R I) (tw q i)
  exact eqv_of_section _ g _ _ (he g hg) (eqv_comp _ _ _ _ (eqv_of_iso _ e _) hA2)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
