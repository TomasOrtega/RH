import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrdegResidueFieldEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldIsAlgebraicOfEtale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldIsoInvCompSpec

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RelDimFibCrit

/- English proof (translation)
Take `⟨g, rfl, hg⟩` from `hφ.exists_etale_mvPolynomial`. Establish `hQ : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ P.comap g → Q'.comap (MvPolynomial.C : R →+* _) = (P.comap g).comap MvPolynomial.C → Q' = P.comap g`. Introduce `Q' hQ' hle hc`. Use `letI := g.toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin r) R) B := hg`.

Use `haveI : Module.Flat (MvPolynomial (Fin r) R) B := inferInstance`. Use `haveI : P.LiesOver (P.comap g) := ⟨rfl⟩`. Take `⟨P', hP'le, hP'prime, hP'over⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := Q') P hle`. Establish `hP'Q : P'.comap g = Q'` using `hP'over.over.symm`. Use `hP P' hP'prime hP'le (by rw [← Ideal.comap_comap, hP'Q, hc, Ideal.comap_comap])` as an intermediate fact.

Rewrite using `[← hP'Q, this]`. Establish `h1` using `GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq r (P.comap g) hQ`. Establish `h2` using `GlobalTheory.residueField_isAlgebraic_of_etale g hg P`. Use `letI i12 := (Ideal.ResidueField.map ((P.comap g).comap MvPolynomial.C) (P.comap g) (MvPolynomial.C : R →+* _) rfl).toAlgebra`. Use `letI i23 := (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra`.

Use `letI i13 := (Ideal.ResidueField.map ((P.comap g).comap (MvPolynomial.C : R →+* _)) P (g.comp MvPolynomial.C) rfl).toAlgebra`. Use `haveI : IsScalarTower ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField (P.comap g).ResidueField P.ResidueField := by`. Use `IsScalarTower.of_algebraMap_eq' ?_` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]`.

Rewrite using `[Ideal.ResidueField.map_algebraMap _ (P.comap g) (MvPolynomial.C : R →+* _) rfl x, Ideal.ResidueField.map_algebraMap (P.comap g) P g rfl]`. Conclude with `Ideal.ResidueField.map_algebraMap ((P.comap g).comap (MvPolynomial.C : R →+* _)) P (g.comp MvPolynomial.C) rfl x`. Use `trdeg_add_eq ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField (P.comap g).ResidueField (A := P.ResidueField)` as an intermediate fact. Rewrite `this` using `[h1, trdeg_eq_zero, add_zero]`. Conclude with `this.symm`.
-/
theorem trdeg_residueField_of_minimal_in_fibre {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (r : ℕ)
    (hφ : φ.IsStandardSmoothOfRelativeDimension r) (P : Ideal B) [P.IsPrime]
    (hP : ∀ P' : Ideal B, P'.IsPrime → P' ≤ P → P'.comap φ = P.comap φ → P' = P) :
    @Algebra.trdeg (P.comap φ).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap φ) P φ rfl).toAlgebra = r := by
  obtain ⟨g, rfl, hg⟩ := hφ.exists_etale_mvPolynomial
  have hQ : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ P.comap g →
      Q'.comap (MvPolynomial.C : R →+* _) = (P.comap g).comap MvPolynomial.C → Q' = P.comap g := by
    intro Q' hQ' hle hc
    letI := g.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin r) R) B := hg
    haveI : Module.Flat (MvPolynomial (Fin r) R) B := inferInstance
    haveI : P.LiesOver (P.comap g) := ⟨rfl⟩
    obtain ⟨P', hP'le, hP'prime, hP'over⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Q') P hle
    have hP'Q : P'.comap g = Q' := hP'over.over.symm
    have := hP P' hP'prime hP'le (by rw [← Ideal.comap_comap, hP'Q, hc, Ideal.comap_comap])
    rw [← hP'Q, this]
  have h1 := GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq r (P.comap g) hQ
  have h2 := GlobalTheory.residueField_isAlgebraic_of_etale g hg P
  letI i12 := (Ideal.ResidueField.map ((P.comap g).comap MvPolynomial.C) (P.comap g)
    (MvPolynomial.C : R →+* _) rfl).toAlgebra
  letI i23 := (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra
  letI i13 := (Ideal.ResidueField.map ((P.comap g).comap (MvPolynomial.C : R →+* _)) P
    (g.comp MvPolynomial.C) rfl).toAlgebra
  haveI : IsScalarTower ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField
      (P.comap g).ResidueField P.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap _ (P.comap g) (MvPolynomial.C : R →+* _) rfl x,
      Ideal.ResidueField.map_algebraMap (P.comap g) P g rfl]
    exact Ideal.ResidueField.map_algebraMap ((P.comap g).comap (MvPolynomial.C : R →+* _)) P
      (g.comp MvPolynomial.C) rfl x
  have := trdeg_add_eq ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField
    (P.comap g).ResidueField (A := P.ResidueField)
  rw [h1, trdeg_eq_zero, add_zero] at this
  exact this.symm

end GlobalTheory.RelDimFibCrit

namespace GlobalTheory.RelDimFibCrit

/- English proof (translation)
Set `s : Set (Ideal B)ᵒᵈ` to `{Q | (OrderDual.ofDual Q).IsPrime ∧ OrderDual.ofDual Q ≤ P ∧ (OrderDual.ofDual Q).comap φ = P.comap φ}`. Take `⟨m, -, hm⟩` from `zorn_le_nonempty₀ s (fun c hcs hc y hy => by`. Establish `hyc : OrderDual.ofDual y ∈ OrderDual.ofDual '' c` using `Set.mem_image_of_mem _ hy`. Use `⟨OrderDual.toDual (sInf (OrderDual.ofDual '' c)), ⟨?_, ?_, ?_⟩, fun z hz => ?_⟩` and prove the remaining obligations. Use `Ideal.sInf_isPrime_of_isChain (s := OrderDual.ofDual '' c) ⟨_, hyc⟩ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab`. Break down `hc ha hb (fun h => hab (congrArg _ h)) with h | h` into its components or cases. Conclude with `Or.inr h`. Conclude with `Or.inl h`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `(hcs ha).1`. Conclude with `(sInf_le hyc).trans (hcs hy).2.1`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(Ideal.comap_mono (sInf_le hyc)).trans (hcs hy).2.2.le`. Introduce `a ha`.

Express the relevant statement in the definitionally equal form `φ a ∈ sInf (OrderDual.ofDual '' c)`. Rewrite using `[Submodule.mem_sInf]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[← Ideal.mem_comap, (hcs hz).2.2]`. Conclude with `ha`.

Conclude with `(sInf_le (Set.mem_image_of_mem OrderDual.ofDual hz) : sInf (OrderDual.ofDual '' c) ≤ OrderDual.ofDual z)) (OrderDual.toDual P) ⟨hP, le_rfl, rfl⟩`. Use `⟨OrderDual.ofDual m, hm.prop.1, hm.prop.2.1, hm.prop.2.2, fun P' h1 h2 h3 => ?_⟩` and prove the remaining obligations. Use `hm.eq_of_ge (y := OrderDual.toDual P') ⟨h1, h2.trans hm.prop.2.1, h3⟩ h2` as an intermediate fact. Conclude with `congrArg OrderDual.ofDual this`.
-/
theorem exists_minimal_in_fibre {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (P : Ideal B) (hP : P.IsPrime) :
    ∃ P₀ : Ideal B, P₀.IsPrime ∧ P₀ ≤ P ∧ P₀.comap φ = P.comap φ ∧
      ∀ P' : Ideal B, P'.IsPrime → P' ≤ P₀ → P'.comap φ = P.comap φ → P' = P₀ := by
  let s : Set (Ideal B)ᵒᵈ := {Q | (OrderDual.ofDual Q).IsPrime ∧ OrderDual.ofDual Q ≤ P ∧
    (OrderDual.ofDual Q).comap φ = P.comap φ}
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hyc : OrderDual.ofDual y ∈ OrderDual.ofDual '' c := Set.mem_image_of_mem _ hy
    refine ⟨OrderDual.toDual (sInf (OrderDual.ofDual '' c)), ⟨?_, ?_, ?_⟩, fun z hz => ?_⟩
    · refine Ideal.sInf_isPrime_of_isChain (s := OrderDual.ofDual '' c) ⟨_, hyc⟩ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        rcases hc ha hb (fun h => hab (congrArg _ h)) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro _ ⟨a, ha, rfl⟩
        exact (hcs ha).1
    · exact (sInf_le hyc).trans (hcs hy).2.1
    · apply le_antisymm
      · exact (Ideal.comap_mono (sInf_le hyc)).trans (hcs hy).2.2.le
      · intro a ha
        change φ a ∈ sInf (OrderDual.ofDual '' c)
        rw [Submodule.mem_sInf]
        rintro _ ⟨z, hz, rfl⟩
        rw [← Ideal.mem_comap, (hcs hz).2.2]
        exact ha
    · exact (sInf_le (Set.mem_image_of_mem OrderDual.ofDual hz) :
        sInf (OrderDual.ofDual '' c) ≤ OrderDual.ofDual z)) (OrderDual.toDual P) ⟨hP, le_rfl, rfl⟩
  refine ⟨OrderDual.ofDual m, hm.prop.1, hm.prop.2.1, hm.prop.2.2, fun P' h1 h2 h3 => ?_⟩
  have := hm.eq_of_ge (y := OrderDual.toDual P') ⟨h1, h2.trans hm.prop.2.1, h3⟩ h2
  exact congrArg OrderDual.ofDual this

/- English proof (translation)
Introduce `X Y X' Y' g f jX jY _ _ e x`. Establish `hpt : jY (g x) = f (jX x)`. Rewrite using `[← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]`. Establish `hc` using `Scheme.Hom.residueFieldMap_congr e x`. Rewrite `hc` using `[Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]`.

Set `C : Y.residueField (jY (g x)) ≅ Y.residueField (f (jX x))` to `Y.residueFieldCongr hpt`. Establish `hc' : jY.residueFieldMap (g x) ≫ g.residueFieldMap x = C.hom ≫ f.residueFieldMap (jX x) ≫ jX.residueFieldMap x` using `hc`. Set `eU : Y.residueField (f (jX x)) ≅ Y'.residueField (g x)` to `C.symm ≪≫ asIso (jY.residueFieldMap (g x))`. Set `eV : X.residueField (jX x) ≅ X'.residueField x` to `asIso (jX.residueFieldMap x)`. Use `GlobalTheory.trdeg_eq_of_ringEquiv_square _ _ eU.commRingCatIsoToRingEquiv eV.commRingCatIsoToRingEquiv ?_` and prove the remaining obligations.

Establish `key : C.inv ≫ jY.residueFieldMap (g x) ≫ g.residueFieldMap x = f.residueFieldMap (jX x) ≫ jX.residueFieldMap x`. Rewrite using `[hc']`. Simplify using the standard rewrite rules. Establish `key2` using `congrArg CommRingCat.Hom.hom key`. Simplify using `only [CommRingCat.hom_comp] at key2`.

Use extensionality with `y`. Establish `key3` using `congrArg (fun φ => φ y) key2`. Simplify `key3` using `[eU, eV]`.
-/
theorem trdeg_residueFieldMap_openImmersion_square :
    ∀ {X Y X' Y' : Scheme.{0}} (g : X' ⟶ Y') (f : X ⟶ Y) (jX : X' ⟶ X) (jY : Y' ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY], g ≫ jY = jX ≫ f → ∀ x : X',
    @Algebra.trdeg (Y.residueField (f (jX x))) (X.residueField (jX x)) _ _
      (f.residueFieldMap (jX x)).hom.toAlgebra =
    @Algebra.trdeg (Y'.residueField (g x)) (X'.residueField x) _ _
      (g.residueFieldMap x).hom.toAlgebra := by
  intro X Y X' Y' g f jX jY _ _ e x
  have hpt : jY (g x) = f (jX x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  have hc := Scheme.Hom.residueFieldMap_congr e x
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hc
  let C : Y.residueField (jY (g x)) ≅ Y.residueField (f (jX x)) := Y.residueFieldCongr hpt
  have hc' : jY.residueFieldMap (g x) ≫ g.residueFieldMap x =
      C.hom ≫ f.residueFieldMap (jX x) ≫ jX.residueFieldMap x := hc
  let eU : Y.residueField (f (jX x)) ≅ Y'.residueField (g x) :=
    C.symm ≪≫ asIso (jY.residueFieldMap (g x))
  let eV : X.residueField (jX x) ≅ X'.residueField x := asIso (jX.residueFieldMap x)
  refine GlobalTheory.trdeg_eq_of_ringEquiv_square _ _ eU.commRingCatIsoToRingEquiv
    eV.commRingCatIsoToRingEquiv ?_
  have key : C.inv ≫ jY.residueFieldMap (g x) ≫ g.residueFieldMap x =
      f.residueFieldMap (jX x) ≫ jX.residueFieldMap x := by
    rw [hc']; simp
  have key2 := congrArg CommRingCat.Hom.hom key
  simp only [CommRingCat.hom_comp] at key2
  ext y
  have key3 := congrArg (fun φ => φ y) key2
  simpa [eU, eV] using key3

open AlgebraicGeometry CategoryTheory Limits in
/- English proof (translation)
Use `haveI : ((Spec.map φ) p).asIdeal.IsPrime := PrimeSpectrum.isPrime _`. Establish `key : CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫ (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫ (Scheme.Spec.residueFieldIso S p).hom = CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫ …`. Rewrite using `[reassoc_of% Scheme.Spec.algebraMap_residueFieldIso_inv]`. Use `erw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p]`. Use `erw [Scheme.Spec.residue_residueFieldIso_hom]`.

Use `erw [Scheme.Hom.germ_stalkMap_assoc]`. Use `erw [Spec.germ_stalkMapIso_hom_assoc]`. Use `erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]`. Use extensionality with `r`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`.

Use `erw [Ideal.ResidueField.map_algebraMap]`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Use `ext1`. Apply `Ideal.ResidueField.ringHom_ext` to reduce the goal to its premises. Conclude with `congr_arg CommRingCat.Hom.hom key`.
-/
private lemma specMap_residueFieldMap_conj_eq_ofHom_map {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (p : PrimeSpectrum S) :
    (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
  haveI : ((Spec.map φ) p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have key : CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
    rw [reassoc_of% Scheme.Spec.algebraMap_residueFieldIso_inv]
    erw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p]
    erw [Scheme.Spec.residue_residueFieldIso_hom]
    erw [Scheme.Hom.germ_stalkMap_assoc]
    erw [Spec.germ_stalkMapIso_hom_assoc]
    erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    erw [Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply]
  ext1
  apply Ideal.ResidueField.ringHom_ext
  exact congr_arg CommRingCat.Hom.hom key

open AlgebraicGeometry CategoryTheory Limits in
/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[Scheme.residueFieldCongr_refl]`.
-/
private lemma residueFieldCongr_hom_hom_comp {Y : Scheme.{0}} {a b : Y} {Z : CommRingCat.{0}}
    (h : a = b) (h' : b = a) (g : Y.residueField a ⟶ Z) :
    (Y.residueFieldCongr h).hom ≫ (Y.residueFieldCongr h').hom ≫ g = g := by
  subst h
  simp [Scheme.residueFieldCongr_refl]

open AlgebraicGeometry CategoryTheory Limits in
/- English proof (translation)
The claim follows from `ciSup_le' fun s ↦ (s.2.ringHom_of_comp_eq e₁ e₂ e₁.surjective e₂.injective h).cardinalMk_le_trdeg`.
-/
private lemma trdeg_le_of_ringEquiv {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L ≤ Algebra.trdeg K' L' :=
  ciSup_le' fun s ↦ (s.2.ringHom_of_comp_eq e₁ e₂ e₁.surjective e₂.injective h).cardinalMk_le_trdeg

open AlgebraicGeometry CategoryTheory Limits in
/- English proof (translation)
Use `le_antisymm (trdeg_le_of_ringEquiv e₁ e₂ h) (trdeg_le_of_ringEquiv e₁.symm e₂.symm ?_)` and prove the remaining obligations. Use extensionality with `a`. Use `congr($h (e₁.symm a))` as an intermediate fact. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at this`. Simplify using `[this]`.
-/
private lemma trdeg_eq_of_ringEquiv {K L K' L' : Type} [Field K] [CommRing L] [Field K']
    [CommRing L'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  refine le_antisymm (trdeg_le_of_ringEquiv e₁ e₂ h) (trdeg_le_of_ringEquiv e₁.symm e₂.symm ?_)
  ext a
  have := congr($h (e₁.symm a))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at this
  simp [this]

open AlgebraicGeometry CategoryTheory Limits in

/- English proof (translation)
Take `⟨p, rfl⟩ : ∃ p' : Spec Γ(X, V), p' = p` from `⟨p, rfl⟩`. Use `haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (p : PrimeSpectrum Γ(X, V))`. Use `set φ := f.appLE U V e`. Use `haveI := hU.isOpenImmersion_fromSpec`. Use `haveI := hV.isOpenImmersion_fromSpec`.

Establish `h₁ : hU.fromSpec ((Spec.map φ) p) = f (hV.fromSpec p)` using `congr($(hU.SpecMap_appLE_fromSpec f hV e) p)`. Use `set q : Spec Γ(Y, U) := (Spec.map φ) p`. Set `eL` to `(asIso (hV.fromSpec.residueFieldMap p) ≪≫ Scheme.Spec.residueFieldIso _ p).commRingCatIsoToRingEquiv`. Set `eK` to `(Y.residueFieldCongr h₁.symm ≪≫ asIso (hU.fromSpec.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso _ q).commRingCatIsoToRingEquiv`. Establish `hsq : (Y.residueFieldCongr h₁.symm).hom ≫ hU.fromSpec.residueFieldMap q ≫ (Scheme.Spec.residueFieldIso _ q).hom ≫ CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) = f.residueFieldMap (hV.fromSpec p) ≫ hV.fromSpec.residueFieldMap p ≫ (Scheme.S …` using `by erw [← specMap_residueFieldMap_conj_eq_ofHom_map]`.

Rewrite using `[Iso.hom_inv_id_assoc, ← Category.assoc (hU.fromSpec.residueFieldMap q), ← Scheme.residueFieldMap_comp, ← Category.assoc (f.residueFieldMap _), ← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr (hU.SpecMap_appLE_fromSpec f hV e)]`. Conclude with `(congrArg _ (Category.assoc _ _ _)).trans (residueFieldCongr_hom_hom_comp _ _ _)`. Use `@trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (RingHom.toAlgebra _) (RingHom.toAlgebra _) eK eL ?_` and prove the remaining obligations. Use extensionality with `a`. Conclude with `congr((CommRingCat.Hom.hom $hsq) a)`.
-/
theorem _root_.GlobalTheory.RelDimFibCrit.trdeg_affine {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(X, V)) :
    @Algebra.trdeg (Y.residueField (f (hV.fromSpec p))) (X.residueField (hV.fromSpec p)) _ _
      (f.residueFieldMap (hV.fromSpec p)).hom.toAlgebra =
    @Algebra.trdeg (p.asIdeal.comap (f.appLE U V e).hom).ResidueField p.asIdeal.ResidueField _ _
      (Ideal.ResidueField.map _ p.asIdeal (f.appLE U V e).hom rfl).toAlgebra := by
  obtain ⟨p, rfl⟩ : ∃ p' : Spec Γ(X, V), p' = p := ⟨p, rfl⟩
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (p : PrimeSpectrum Γ(X, V))
  set φ := f.appLE U V e
  haveI := hU.isOpenImmersion_fromSpec
  haveI := hV.isOpenImmersion_fromSpec
  have h₁ : hU.fromSpec ((Spec.map φ) p) = f (hV.fromSpec p) :=
    congr($(hU.SpecMap_appLE_fromSpec f hV e) p)
  set q : Spec Γ(Y, U) := (Spec.map φ) p
  let eL := (asIso (hV.fromSpec.residueFieldMap p) ≪≫
    Scheme.Spec.residueFieldIso _ p).commRingCatIsoToRingEquiv
  let eK := (Y.residueFieldCongr h₁.symm ≪≫ asIso (hU.fromSpec.residueFieldMap q) ≪≫
    Scheme.Spec.residueFieldIso _ q).commRingCatIsoToRingEquiv
  have hsq : (Y.residueFieldCongr h₁.symm).hom ≫ hU.fromSpec.residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso _ q).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) =
      f.residueFieldMap (hV.fromSpec p) ≫ hV.fromSpec.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso _ p).hom := by
    erw [← specMap_residueFieldMap_conj_eq_ofHom_map]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc (hU.fromSpec.residueFieldMap q),
      ← Scheme.residueFieldMap_comp, ← Category.assoc (f.residueFieldMap _),
      ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr (hU.SpecMap_appLE_fromSpec f hV e)]
    exact (congrArg _ (Category.assoc _ _ _)).trans (residueFieldCongr_hom_hom_comp _ _ _)
  refine @trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (RingHom.toAlgebra _) (RingHom.toAlgebra _) eK eL ?_
  ext a
  exact congr((CommRingCat.Hom.hom $hsq) a)

/- English proof (translation)
Introduce `X S f n hf H`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, V, hV, hx, e, hs⟩` from `Smooth.exists_isStandardSmooth f x`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension r := by`. Take `⟨_, _, _, _, ⟨P⟩⟩` from `hs`.

Use `letI := (f.appLE U V e).hom.toAlgebra`. Conclude with `⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩`. Use `⟨U, hU, V, hV, hx, e, ?_⟩` and prove the remaining obligations. Take `⟨P₀, hP₀, -, hcomap, hmin⟩` from `exists_minimal_in_fibre (f.appLE U V e).hom (hV.primeIdealOf ⟨x, hx⟩).asIdeal inferInstance`. Set `p₀ : PrimeSpectrum Γ(X, V)` to `⟨P₀, hP₀⟩`.

Establish `key` using `trdeg_residueField_of_minimal_in_fibre (f.appLE U V e).hom r hr P₀ (fun P' h1 h2 h3 => hmin P' h1 h2 (h3.trans hcomap))`. Establish `h3` using `trdeg_affine f U hU V hV e p₀`. Establish `hm : ∀ x' : X, f x' = f (hV.fromSpec p₀) → x' ⤳ hV.fromSpec p₀ → x' = hV.fromSpec p₀`. Introduce `x' hfx hsp`. Establish `hx'V : x' ∈ Set.range hV.fromSpec` using `hV.range_fromSpec ▸ hsp.mem_open V.isOpen (hV.range_fromSpec ▸ ⟨p₀, rfl⟩)`.

Take `⟨p', rfl⟩` from `hx'V`. Establish `hle : p'.asIdeal ≤ P₀` using `(PrimeSpectrum.le_iff_specializes p' p₀).2 (hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 hsp)`. Establish `h1 : ∀ q : PrimeSpectrum Γ(X, V), hU.fromSpec (Spec.map (f.appLE U V e) q) = f (hV.fromSpec q)` using `fun q => by show (Spec.map (f.appLE U V e) ≫ hU.fromSpec) q = (hV.fromSpec ≫ f) q`. Rewrite using `[IsAffineOpen.SpecMap_appLE_fromSpec]`. Establish `h2` using `hU.fromSpec.isOpenEmbedding.injective ((h1 p').trans (hfx.trans (h1 p₀).symm))`.

Establish `hc : p'.asIdeal.comap (f.appLE U V e).hom = P₀.comap (f.appLE U V e).hom` using `congrArg PrimeSpectrum.asIdeal h2`. Use `hmin p'.asIdeal p'.isPrime hle (hc.trans hcomap)` as an intermediate fact. Conclude with `congrArg hV.fromSpec (PrimeSpectrum.ext this)`. Establish `hn` using `H _ hm`. Establish `: (r : Cardinal) = n` using `key.symm.trans (h3.symm.trans hn)`.

Take `rfl : r = n` from `by exact_mod_cast this`. Conclude with `hr`.
-/
theorem smoothOfRelativeDimension_of_trdeg : ∀ {X S : Scheme.{0}} (f : X ⟶ S) (n : ℕ), Smooth f →
    (∀ x : X, (∀ x' : X, f x' = f x → x' ⤳ x → x' = x) →
      @Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _ (f.residueFieldMap x).hom.toAlgebra = n) →
    SmoothOfRelativeDimension n f := by
  intro X S f n hf H
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨r, hr⟩ : ∃ r, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension r := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := hs
    letI := (f.appLE U V e).hom.toAlgebra
    exact ⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  obtain ⟨P₀, hP₀, -, hcomap, hmin⟩ :=
    exists_minimal_in_fibre (f.appLE U V e).hom (hV.primeIdealOf ⟨x, hx⟩).asIdeal inferInstance
  let p₀ : PrimeSpectrum Γ(X, V) := ⟨P₀, hP₀⟩
  have key := trdeg_residueField_of_minimal_in_fibre (f.appLE U V e).hom r hr P₀ (fun P' h1 h2 h3 => hmin P' h1 h2 (h3.trans hcomap))
  have h3 := trdeg_affine f U hU V hV e p₀
  have hm : ∀ x' : X, f x' = f (hV.fromSpec p₀) → x' ⤳ hV.fromSpec p₀ → x' = hV.fromSpec p₀ := by
    intro x' hfx hsp
    have hx'V : x' ∈ Set.range hV.fromSpec :=
      hV.range_fromSpec ▸ hsp.mem_open V.isOpen (hV.range_fromSpec ▸ ⟨p₀, rfl⟩)
    obtain ⟨p', rfl⟩ := hx'V
    have hle : p'.asIdeal ≤ P₀ := (PrimeSpectrum.le_iff_specializes p' p₀).2
      (hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 hsp)
    have h1 : ∀ q : PrimeSpectrum Γ(X, V),
        hU.fromSpec (Spec.map (f.appLE U V e) q) = f (hV.fromSpec q) := fun q => by
      show (Spec.map (f.appLE U V e) ≫ hU.fromSpec) q = (hV.fromSpec ≫ f) q
      rw [IsAffineOpen.SpecMap_appLE_fromSpec]
    have h2 := hU.fromSpec.isOpenEmbedding.injective ((h1 p').trans (hfx.trans (h1 p₀).symm))
    have hc : p'.asIdeal.comap (f.appLE U V e).hom = P₀.comap (f.appLE U V e).hom :=
      congrArg PrimeSpectrum.asIdeal h2
    have := hmin p'.asIdeal p'.isPrime hle (hc.trans hcomap)
    exact congrArg hV.fromSpec (PrimeSpectrum.ext this)
  have hn := H _ hm
  have : (r : Cardinal) = n := key.symm.trans (h3.symm.trans hn)
  obtain rfl : r = n := by exact_mod_cast this
  exact hr

end GlobalTheory.RelDimFibCrit
