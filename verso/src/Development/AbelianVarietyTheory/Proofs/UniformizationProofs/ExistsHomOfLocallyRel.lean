import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry

noncomputable section

namespace GlobalTheory.SmoothLocusAdd

open GlobalTheory.WeierstrassCurve

/- English proof (translation)
Use `choose V j hj f hz hs hf using H`. Set `𝒰 : T.OpenCover` to `Scheme.Cover.mkOfCovers T V j (fun z => ⟨z, hz z⟩) hj`. Establish `hc : ∀ a b, pullback.fst (j a) (j b) ≫ f a = pullback.snd _ _ ≫ f b`. Introduce `a b`. Establish `: IsReduced (pullback (j a) (j b))` using `isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)`.

Use `(hom_eq_iff_forall_field s ?_).mpr fun k _ x => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hs, hs, pullback.condition_assoc]`. Establish `h₁` using `hf a k (x ≫ pullback.fst (j a) (j b))`. Establish `h₂` using `hf b k (x ≫ pullback.snd (j a) (j b))`. Rewrite `h₁`, `h₂` using `[Category.assoc, Category.assoc]`.

Rewrite `h₂` using `[← pullback.condition]`. Conclude with `huniq k _ _ _ h₁ h₂`. Establish `hg : ∀ z, j z ≫ 𝒰.glueMorphisms f hc = f z` using `𝒰.ι_glueMorphisms f hc`. Use `⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun z => ?_, fun k _ x => ?_⟩` and prove the remaining obligations. Conclude with `((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s) (hg z))).trans (hs z)`.

Set `z : T` to `x (IsLocalRing.closedPoint k)`. Establish `hr : Set.range x ⊆ Set.range (j z)`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `rfl : y = IsLocalRing.closedPoint k` from `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Conclude with `hz z`.

Establish `hy : IsOpenImmersion.lift (j z) x hr ≫ j z = x` using `IsOpenImmersion.lift_fac ..`. Use `hf z k (IsOpenImmersion.lift (j z) x hr)` as an intermediate fact. Rewrite `this` using `[← hg z, ← Category.assoc, hy]`. Conclude with `this`.
-/
theorem exists_hom_of_locally_rel {T Y S : Scheme.{0}} [IsReduced T] (t : T ⟶ S) (s : Y ⟶ S)
    [IsSeparated s]
    (Rel : ∀ (k : Type) [Field k], (Spec (.of k) ⟶ T) → (Spec (.of k) ⟶ Y) → Prop)
    (huniq : ∀ (k : Type) [Field k] x y y', Rel k x y → Rel k x y' → y = y')
    (H : ∀ z : T, ∃ (V : Scheme.{0}) (j : V ⟶ T) (_ : IsOpenImmersion j) (f : V ⟶ Y),
      z ∈ Set.range j ∧ f ≫ s = j ≫ t ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V), Rel k (x ≫ j) (x ≫ f)) :
    ∃ f : T ⟶ Y, f ≫ s = t ∧ ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), Rel k x (x ≫ f) := by
  choose V j hj f hz hs hf using H
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T V j (fun z => ⟨z, hz z⟩) hj
  have hc : ∀ a b, pullback.fst (j a) (j b) ≫ f a = pullback.snd _ _ ≫ f b := by
    intro a b
    have : IsReduced (pullback (j a) (j b)) :=
      isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
    refine (hom_eq_iff_forall_field s ?_).mpr fun k _ x => ?_
    · rw [Category.assoc, Category.assoc, hs, hs, pullback.condition_assoc]
    · have h₁ := hf a k (x ≫ pullback.fst (j a) (j b))
      have h₂ := hf b k (x ≫ pullback.snd (j a) (j b))
      rw [Category.assoc, Category.assoc] at h₁ h₂
      rw [← pullback.condition] at h₂
      exact huniq k _ _ _ h₁ h₂
  have hg : ∀ z, j z ≫ 𝒰.glueMorphisms f hc = f z := 𝒰.ι_glueMorphisms f hc
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun z => ?_, fun k _ x => ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ s) (hg z))).trans (hs z)
  · let z : T := x (IsLocalRing.closedPoint k)
    have hr : Set.range x ⊆ Set.range (j z) := by
      rintro _ ⟨y, rfl⟩
      obtain rfl : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hz z
    have hy : IsOpenImmersion.lift (j z) x hr ≫ j z = x := IsOpenImmersion.lift_fac ..
    have := hf z k (IsOpenImmersion.lift (j z) x hr)
    rw [← hg z, ← Category.assoc, hy] at this
    exact this

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def IsSumAt {k : Type} [Field k] (a b c : Spec (.of k) ⟶ scheme W) : Prop :=
  ∀ (ρ : R →+* k) (P Q : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P)
    (hQ : IsUnimodularSol (W.map ρ) Q), a = ptHom W ρ P hP → b = ptHom W ρ Q hQ →
    ∃ h : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), c = ptHom W ρ _ h

def IsNonsingularAt {k : Type} [Field k] (a : Spec (.of k) ⟶ scheme W) : Prop :=
  ∀ (ρ : R →+* k) (P : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P),
    a = ptHom W ρ P hP → (W.map ρ).toProjective.Nonsingular P

/- English proof (translation)
Take `⟨φ, hφ⟩` from `Spec.map_surjective (a ≫ toSpec W)`. Take `⟨P, hP, eP⟩` from `exists_eq_ptHom W φ.hom a hφ.symm`. Take `⟨Q, hQ, eQ⟩` from `exists_eq_ptHom W φ.hom b (hab.symm.trans hφ.symm)`. Conclude with `⟨φ.hom, P, Q, hP, hQ, eP, eQ⟩`.
-/
theorem exists_triples {k : Type} [Field k] (a b : Spec (.of k) ⟶ scheme W)
    (hab : a ≫ toSpec W = b ≫ toSpec W) :
    ∃ (ρ : R →+* k) (P Q : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P)
      (hQ : IsUnimodularSol (W.map ρ) Q), a = ptHom W ρ P hP ∧ b = ptHom W ρ Q hQ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec W)
  obtain ⟨P, hP, eP⟩ := exists_eq_ptHom W φ.hom a hφ.symm
  obtain ⟨Q, hQ, eQ⟩ := exists_eq_ptHom W φ.hom b (hab.symm.trans hφ.symm)
  exact ⟨φ.hom, P, Q, hP, hQ, eP, eQ⟩

/- English proof (translation)
Take `⟨ρ, P, Q, hP, hQ, eP, eQ⟩` from `exists_triples W a b hab`. Take `⟨_, e⟩` from `h ρ P Q hP hQ eP eQ`. Take `⟨_, e'⟩` from `h' ρ P Q hP hQ eP eQ`. Conclude with `e.trans e'.symm`.
-/
theorem IsSumAt.unique {k : Type} [Field k] {a b c c' : Spec (.of k) ⟶ scheme W}
    (hab : a ≫ toSpec W = b ≫ toSpec W) (h : IsSumAt W a b c) (h' : IsSumAt W a b c') :
    c = c' := by
  obtain ⟨ρ, P, Q, hP, hQ, eP, eQ⟩ := exists_triples W a b hab
  obtain ⟨_, e⟩ := h ρ P Q hP hQ eP eQ
  obtain ⟨_, e'⟩ := h' ρ P Q hP hQ eP eQ
  exact e.trans e'.symm

open WeierstrassCurve.Projective in

/- English proof (translation)
Introduce `ρ' P' Q' hP' hQ' eP eQ`. Choose the witnesses or unpack the hypotheses as in `rfl : ρ = ρ' := by`. Use `congrArg (· ≫ toSpec W) eP` as an intermediate fact. Simplify using `only [ptHom_toSpec] at this`. Conclude with `congrArg (·.hom) (Spec.map_injective this)`.

Take `⟨u, hu⟩` from `(ptHom_eq_ptHom_iff W hP' hP).mp eP.symm`. Take `⟨v, hv⟩` from `(ptHom_eq_ptHom_iff W hQ' hQ).mp eQ.symm`. Establish `e₁ : P ≈ P'` using `⟨u, hu.symm⟩`. Establish `e₂ : Q ≈ Q'` using `⟨v, hv.symm⟩`. Establish `nP'` using `(nonsingular_of_equiv e₁).mp nP`.

Establish `nQ'` using `(nonsingular_of_equiv e₂).mp nQ`. Establish `hA : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P' Q')` using `.of_nonsingular (nonsingular_add nP' nQ')`. Use `⟨hA, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `Setoid.trans e (add_equiv e₁ e₂)`. Conclude with `((ptHom_eq_ptHom_iff W hA hS).mpr ⟨w, hw.symm⟩).symm`.
-/
theorem isSumAt_ptHom {k : Type} [Field k] (ρ : R →+* k) {P Q S : Fin 3 → k}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hS : IsUnimodularSol (W.map ρ) S) (nP : (W.map ρ).toProjective.Nonsingular P)
    (nQ : (W.map ρ).toProjective.Nonsingular Q)
    (e : S ≈ (W.map ρ).toProjective.add P Q) :
    IsSumAt W (ptHom W ρ P hP) (ptHom W ρ Q hQ) (ptHom W ρ S hS) := by
  intro ρ' P' Q' hP' hQ' eP eQ
  obtain rfl : ρ = ρ' := by
    have := congrArg (· ≫ toSpec W) eP
    simp only [ptHom_toSpec] at this
    exact congrArg (·.hom) (Spec.map_injective this)
  obtain ⟨u, hu⟩ := (ptHom_eq_ptHom_iff W hP' hP).mp eP.symm
  obtain ⟨v, hv⟩ := (ptHom_eq_ptHom_iff W hQ' hQ).mp eQ.symm
  have e₁ : P ≈ P' := ⟨u, hu.symm⟩
  have e₂ : Q ≈ Q' := ⟨v, hv.symm⟩
  have nP' := (nonsingular_of_equiv e₁).mp nP
  have nQ' := (nonsingular_of_equiv e₂).mp nQ
  have hA : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P' Q') :=
    .of_nonsingular (nonsingular_add nP' nQ')
  refine ⟨hA, ?_⟩
  obtain ⟨w, hw⟩ := Setoid.trans e (add_equiv e₁ e₂)
  exact ((ptHom_eq_ptHom_iff W hA hS).mpr ⟨w, hw.symm⟩).symm

open WeierstrassCurve.Projective in

/- English proof (translation)
Establish `hS' : ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q)` using `fun k _ φ => hS k φ fun h0 => (hi.map φ).ne_zero (congrFun h0 i)`. Establish `h : IsUnimodularSol (W.map ρ) S` using `.of_isUnit (equation_of_forall_field fun k _ φ => ((nonsingular_of_equiv (hS' k φ)).mpr (nonsingular_add (nP k φ) (nQ k φ))).left) i hi`. Use `⟨h, fun k _ x => ?_⟩` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `Spec.map_surjective x`. Take `⟨φ, rfl⟩ : ∃ ψ : C →+* k, CommRingCat.ofHom ψ = φ` from `⟨φ.hom, rfl⟩`.

Rewrite using `[SpecMap_ptHom, SpecMap_ptHom, SpecMap_ptHom]`. Conclude with `isSumAt_ptHom W _ _ _ _ (nP k φ) (nQ k φ) (hS' k φ)`.
-/
theorem exists_sum_of_isUnit {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q S : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q))
    (hS : ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q))
    (i : Fin 3) (hi : IsUnit (S i)) :
    ∃ h : IsUnimodularSol (W.map ρ) S, ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Spec (.of C)),
      IsSumAt W (x ≫ ptHom W ρ P hP) (x ≫ ptHom W ρ Q hQ) (x ≫ ptHom W ρ S h) := by
  have hS' : ∀ (k : Type) [Field k] (φ : C →+* k),
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q) := fun k _ φ =>
    hS k φ fun h0 => (hi.map φ).ne_zero (congrFun h0 i)
  have h : IsUnimodularSol (W.map ρ) S := .of_isUnit (equation_of_forall_field fun k _ φ =>
    ((nonsingular_of_equiv (hS' k φ)).mpr (nonsingular_add (nP k φ) (nQ k φ))).left) i hi
  refine ⟨h, fun k _ x => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  obtain ⟨φ, rfl⟩ : ∃ ψ : C →+* k, CommRingCat.ofHom ψ = φ := ⟨φ.hom, rfl⟩
  rw [SpecMap_ptHom, SpecMap_ptHom, SpecMap_ptHom]
  exact isSumAt_ptHom W _ _ _ _ (nP k φ) (nQ k φ) (hS' k φ)

open WeierstrassCurve.Projective in

/- English proof (translation)
Establish `key : ∃ (S : Fin 3 → C) (i : Fin 3), S i ∉ z.asIdeal ∧ ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 → φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q)`. Establish `eA : ∀ (k : Type) [Field k] (φ : C →+* k), (W.map (φ.comp ρ)).toProjective.addXYZ (φ ∘ P) (φ ∘ Q) = φ ∘ (W.map ρ).toProjective.addXYZ P Q` using `fun k _ φ => map_addXYZ (W' := (W.map ρ).toProjective) φ P Q`. Establish `eD : ∀ (k : Type) [Field k] (φ : C →+* k), AddLaw.diagXYZ (W.map (φ.comp ρ)).toProjective (φ ∘ P) (φ ∘ Q) = φ ∘ AddLaw.diagXYZ (W.map ρ).toProjective P Q` using `fun k _ φ => AddLaw.map_diagXYZ (W := (W.map ρ).toProjective) φ P Q`. Use `z.isPrime` as an intermediate fact. Set `κ` to `algebraMap C z.asIdeal.ResidueField`.

Break down `AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero (nP _ κ) (nQ _ κ) with h | h` into its components or cases. Rewrite `h` using `[eA]`. Take `⟨i, hi⟩` from `Function.ne_iff.mp h`. Use `⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩` and prove the remaining obligations. Rewrite `h`, the goal using `[← eA]`.

Conclude with `AddLaw.addXYZ_equiv_add (nP k φ) (nQ k φ) h`. Rewrite `h` using `[eD]`. Take `⟨i, hi⟩` from `Function.ne_iff.mp h`. Use `⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩` and prove the remaining obligations. Rewrite `h`, the goal using `[← eD]`.

Conclude with `AddLaw.diagXYZ_equiv_add (nP k φ) (nQ k φ) h`. Take `⟨S, i, hi, hS⟩` from `key`. Set `C'` to `Localization.Away (S i)`. Set `g : C →+* C'` to `algebraMap C C'`. Establish `: _root_.IsReduced C'` using `inferInstanceAs (_root_.IsReduced (Localization (.powers (S i))))`.

Take `⟨h, hsum⟩` from `exists_sum_of_isUnit W (g.comp ρ) (S := g ∘ S) (hP.map_comp g) (hQ.map_comp g) (fun k _ φ => nP k (φ.comp g)) (fun k _ φ => nQ k (φ.comp g)) (fun k _ φ => hS k (φ.comp g)) i (IsLocalization.Away.algebraMap_isUnit (S i))`. Use `⟨Spec (.of C'), Spec.map (CommRingCat.ofHom g), IsOpenImmersion.of_isLocalization (S i), ptHom W _ _ h, ?_, ?_, fun k _ x => ?_⟩` and prove the remaining obligations. Conclude with `(PrimeSpectrum.localization_away_comap_range C' (S i)).ge hi`. Rewrite using `[ptHom_toSpec, ← Spec.map_comp, CommRingCat.ofHom_comp]`. Rewrite using `[SpecMap_ptHom, SpecMap_ptHom]`.

Conclude with `hsum k x`.
-/
theorem exists_sum_near_prime {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q)) (z : Spec (.of C)) :
    ∃ (V : Scheme.{0}) (j : V ⟶ Spec (.of C)) (_ : IsOpenImmersion j) (f : V ⟶ scheme W),
      z ∈ Set.range j ∧ f ≫ toSpec W = j ≫ Spec.map (CommRingCat.ofHom ρ) ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V),
          IsSumAt W (x ≫ j ≫ ptHom W ρ P hP) (x ≫ j ≫ ptHom W ρ Q hQ) (x ≫ f) := by
  have key : ∃ (S : Fin 3 → C) (i : Fin 3), S i ∉ z.asIdeal ∧
      ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
        φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q) := by
    have eA : ∀ (k : Type) [Field k] (φ : C →+* k),
        (W.map (φ.comp ρ)).toProjective.addXYZ (φ ∘ P) (φ ∘ Q) =
          φ ∘ (W.map ρ).toProjective.addXYZ P Q := fun k _ φ =>
      map_addXYZ (W' := (W.map ρ).toProjective) φ P Q
    have eD : ∀ (k : Type) [Field k] (φ : C →+* k),
        AddLaw.diagXYZ (W.map (φ.comp ρ)).toProjective (φ ∘ P) (φ ∘ Q) =
          φ ∘ AddLaw.diagXYZ (W.map ρ).toProjective P Q := fun k _ φ =>
      AddLaw.map_diagXYZ (W := (W.map ρ).toProjective) φ P Q
    have := z.isPrime
    let κ := algebraMap C z.asIdeal.ResidueField
    rcases AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero (nP _ κ) (nQ _ κ) with h | h
    · rw [eA] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine ⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩
      rw [← eA] at h ⊢
      exact AddLaw.addXYZ_equiv_add (nP k φ) (nQ k φ) h
    · rw [eD] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine ⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩
      rw [← eD] at h ⊢
      exact AddLaw.diagXYZ_equiv_add (nP k φ) (nQ k φ) h
  obtain ⟨S, i, hi, hS⟩ := key
  let C' := Localization.Away (S i)
  let g : C →+* C' := algebraMap C C'
  have : _root_.IsReduced C' := inferInstanceAs (_root_.IsReduced (Localization (.powers (S i))))
  obtain ⟨h, hsum⟩ := exists_sum_of_isUnit W (g.comp ρ) (S := g ∘ S) (hP.map_comp g)
    (hQ.map_comp g) (fun k _ φ => nP k (φ.comp g)) (fun k _ φ => nQ k (φ.comp g))
    (fun k _ φ => hS k (φ.comp g)) i (IsLocalization.Away.algebraMap_isUnit (S i))
  refine ⟨Spec (.of C'), Spec.map (CommRingCat.ofHom g),
    IsOpenImmersion.of_isLocalization (S i), ptHom W _ _ h, ?_, ?_, fun k _ x => ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range C' (S i)).ge hi
  · rw [ptHom_toSpec, ← Spec.map_comp, CommRingCat.ofHom_comp]
  · rw [SpecMap_ptHom, SpecMap_ptHom]
    exact hsum k x

/- English proof (translation)
Use `exists_hom_of_locally_rel (p ≫ toSpec W) (toSpec W) (fun k _ x y => IsSumAt W (x ≫ p) (x ≫ q) y) (fun k _ x y y' h h' => h.unique W (by simp only [Category.assoc, hpq]) h') fun z => ?_` and prove the remaining obligations. Establish `hc : ∀ e : scheme W, ∃ i, e ∈ coordOpen W i` using `fun e => by`. Break down `(coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ e) with h | h` into its components or cases. Use `exacts [⟨_, h⟩, ⟨_, h⟩]`. Take `⟨a, ha⟩` from `hc (p z)`.

Take `⟨b, hb⟩` from `hc (q z)`. Take `⟨C, ι, _, ⟨z', rfl⟩, hr⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := z) (U := p ⁻¹ᵁ coordOpen W a ⊓ q ⁻¹ᵁ coordOpen W b) ⟨ha, hb⟩`. Establish `: _root_.IsReduced C` using `(affine_isReduced_iff C).mp (isReduced_of_isOpenImmersion ι)`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (ι ≫ p ≫ toSpec W)`. Take `⟨P, hP, -, eP⟩` from `exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ p) (by rw [Category.assoc]; exact hφ.symm) a (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).1)`.

Take `⟨Q, hQ, -, eQ⟩` from `exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ q) (by rw [Category.assoc, ← hpq]; exact hφ.symm) b (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).2)`. Take `⟨V, j, _, f, ⟨v, rfl⟩, hf, hsum⟩` from `exists_sum_near_prime W (C := C) φ.hom hP hQ (fun k _ ψ => np k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hP.map_comp ψ) (by`. Rewrite using `[Category.assoc, ← SpecMap_ptHom W _ _ hP, ← eP]))`. Use the proof step `(fun k _ ψ => nq k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hQ.map_comp ψ) (by`. Rewrite using `[Category.assoc, ← SpecMap_ptHom W _ _ hQ, ← eQ])) z'`.

Use `⟨V, j ≫ ι, inferInstance, f, ⟨v, by simp⟩, ?_, fun k _ x => ?_⟩` and prove the remaining obligations. Rewrite using `[hf, Category.assoc, ← hφ]`. Both sides reduce to the same expression. Use `hsum k x` as an intermediate fact. Rewrite `this` using `[← eP, ← eQ]`.

Simplify `this` using `only [Category.assoc]`.
-/
theorem exists_sum {T : Scheme.{0}} [IsReduced T] (p q : T ⟶ scheme W)
    (hpq : p ≫ toSpec W = q ≫ toSpec W)
    (np : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ p))
    (nq : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ q)) :
    ∃ s : T ⟶ scheme W, s ≫ toSpec W = p ≫ toSpec W ∧
      ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsSumAt W (x ≫ p) (x ≫ q) (x ≫ s) := by
  refine exists_hom_of_locally_rel (p ≫ toSpec W) (toSpec W)
    (fun k _ x y => IsSumAt W (x ≫ p) (x ≫ q) y)
    (fun k _ x y y' h h' => h.unique W (by simp only [Category.assoc, hpq]) h') fun z => ?_
  have hc : ∀ e : scheme W, ∃ i, e ∈ coordOpen W i := fun e => by
    rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ e) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨a, ha⟩ := hc (p z)
  obtain ⟨b, hb⟩ := hc (q z)
  obtain ⟨C, ι, _, ⟨z', rfl⟩, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := z) (U := p ⁻¹ᵁ coordOpen W a ⊓ q ⁻¹ᵁ coordOpen W b) ⟨ha, hb⟩
  have : _root_.IsReduced C := (affine_isReduced_iff C).mp (isReduced_of_isOpenImmersion ι)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (ι ≫ p ≫ toSpec W)
  obtain ⟨P, hP, -, eP⟩ := exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ p)
    (by rw [Category.assoc]; exact hφ.symm) a (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).1)
  obtain ⟨Q, hQ, -, eQ⟩ := exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ q)
    (by rw [Category.assoc, ← hpq]; exact hφ.symm) b (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).2)
  obtain ⟨V, j, _, f, ⟨v, rfl⟩, hf, hsum⟩ := exists_sum_near_prime W (C := C) φ.hom hP hQ
    (fun k _ ψ => np k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hP.map_comp ψ) (by
      rw [Category.assoc, ← SpecMap_ptHom W _ _ hP, ← eP]))
    (fun k _ ψ => nq k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hQ.map_comp ψ) (by
      rw [Category.assoc, ← SpecMap_ptHom W _ _ hQ, ← eQ])) z'
  refine ⟨V, j ≫ ι, inferInstance, f, ⟨v, by simp⟩, ?_, fun k _ x => ?_⟩
  · rw [hf, Category.assoc, ← hφ]; rfl
  · have := hsum k x
    rw [← eP, ← eQ] at this
    simpa only [Category.assoc] using this

end GlobalTheory.SmoothLocusAdd

namespace GlobalTheory

open MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open SmoothLocusAdd in

/- English proof (translation)
Introduce `R _ _ _ W U hU hs hg`. Set `G : Over (Spec (.of R))` to `Over.mk (U.ι ≫ WeierstrassCurve.toSpec W)`. Establish `hG : IsIntegral (U : Scheme)` using `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)`. Establish `hN : IsLocallyNoetherian (U : Scheme)` using `LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)`. Establish `hGG : IsIntegral (G ⊗ G).left` using `inferInstanceAs (IsIntegral (pullback (U.ι ≫ WeierstrassCurve.toSpec W) (U.ι ≫ WeierstrassCurve.toSpec W)))`.

Establish `hns : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ (U : Scheme)), IsNonsingularAt W (x ≫ U.ι)` using `fun k _ x ρ P hP e => (hU k ρ P hP).mp (by`. Rewrite using `[← e]`. Introduce `y _`. Conclude with `(x y).2)`. Set `p : (G ⊗ G).left ⟶ (U : Scheme)` to `(fst G G).left`.

Set `q : (G ⊗ G).left ⟶ (U : Scheme)` to `(snd G G).left`. Establish `hp : p ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom` using `Over.w (fst G G)`. Establish `hq : q ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom` using `Over.w (snd G G)`. Establish `hpq : (p ≫ U.ι) ≫ WeierstrassCurve.toSpec W = (q ≫ U.ι) ≫ WeierstrassCurve.toSpec W`. Rewrite using `[Category.assoc, Category.assoc, hp, hq]`.

Take `⟨s, hs₁, hs₂⟩` from `exists_sum W (p ≫ U.ι) (q ≫ U.ι) hpq (fun k _ x => by rw [← Category.assoc]; exact hns k _) (fun k _ x => by rw [← Category.assoc]; exact hns k _)`. Establish `hr : Set.range s ⊆ Set.range U.ι`. Introduce and unpack `_ ⟨z, rfl⟩`. Set `x` to `(G ⊗ G).left.fromSpecResidueField z`. Take `⟨ρ, P, Q, hP, hQ, eP, eQ⟩` from `exists_triples W (k := (G ⊗ G).left.residueField z) (x ≫ p ≫ U.ι) (x ≫ q ≫ U.ι) (by rw [Category.assoc, Category.assoc x, hpq])`.

Take `⟨h, e⟩` from `hs₂ ((G ⊗ G).left.residueField z) x ρ P Q hP hQ eP eQ`. Establish `nP` using `hns ((G ⊗ G).left.residueField z) (x ≫ p) ρ P hP ((Category.assoc _ _ _).trans eP)`. Establish `nQ` using `hns ((G ⊗ G).left.residueField z) (x ≫ q) ρ Q hQ ((Category.assoc _ _ _).trans eQ)`. Use `(hU _ ρ _ h).mpr (WeierstrassCurve.Projective.nonsingular_add nP nQ)` as an intermediate fact. Rewrite `this` using `[← e]`.

Establish `h2 : s (x (IsLocalRing.closedPoint _)) ∈ U` using `this (Set.mem_univ _)`. Establish `h3 : x (IsLocalRing.closedPoint _) = z` using `Scheme.fromSpecResidueField_apply z _`. Rewrite `h2` using `[h3]`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `h2`.

Establish `hl : IsOpenImmersion.lift U.ι s hr ≫ U.ι = s` using `IsOpenImmersion.lift_fac ..`. Use `⟨Over.homMk (IsOpenImmersion.lift U.ι s hr) ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsOpenImmersion.lift U.ι s hr ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom`. Rewrite using `[← Category.assoc, hl, hs₁, Category.assoc, hp]`. Introduce `k _ ρ x y P Q hP hQ ex ey`.

Set `w : Spec (.of k) ⟶ (G ⊗ G).left` to `(lift x y).left`. Establish `e₁ : w ≫ p = x.left` using `congrArg (·.left) (lift_fst x y)`. Establish `e₂ : w ≫ q = y.left` using `congrArg (·.left) (lift_snd x y)`. Take `⟨h, e⟩` from `hs₂ k w ρ P Q hP hQ (by rw [← Category.assoc, e₁]; exact ex) (by rw [← Category.assoc, e₂]; exact ey)`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(w ≫ IsOpenImmersion.lift U.ι s hr) ≫ U.ι = _`. Rewrite using `[Category.assoc, hl, e]`.
-/
theorem exists_add_smoothLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∃ add : (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⊗ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ add).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) := by
  intro R _ _ _ W U hU hs hg
  let G : Over (Spec (.of R)) := Over.mk (U.ι ≫ WeierstrassCurve.toSpec W)
  have hG : IsIntegral (U : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)
  have hN : IsLocallyNoetherian (U : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ WeierstrassCurve.toSpec W)
  have hGG : IsIntegral (G ⊗ G).left := inferInstanceAs (IsIntegral
    (pullback (U.ι ≫ WeierstrassCurve.toSpec W) (U.ι ≫ WeierstrassCurve.toSpec W)))
  have hns : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ (U : Scheme)),
      IsNonsingularAt W (x ≫ U.ι) := fun k _ x ρ P hP e => (hU k ρ P hP).mp (by
    rw [← e]
    intro y _
    exact (x y).2)
  let p : (G ⊗ G).left ⟶ (U : Scheme) := (fst G G).left
  let q : (G ⊗ G).left ⟶ (U : Scheme) := (snd G G).left
  have hp : p ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom := Over.w (fst G G)
  have hq : q ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom := Over.w (snd G G)
  have hpq : (p ≫ U.ι) ≫ WeierstrassCurve.toSpec W = (q ≫ U.ι) ≫ WeierstrassCurve.toSpec W := by
    rw [Category.assoc, Category.assoc, hp, hq]
  obtain ⟨s, hs₁, hs₂⟩ := exists_sum W (p ≫ U.ι) (q ≫ U.ι) hpq
    (fun k _ x => by rw [← Category.assoc]; exact hns k _)
    (fun k _ x => by rw [← Category.assoc]; exact hns k _)
  have hr : Set.range s ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    let x := (G ⊗ G).left.fromSpecResidueField z
    obtain ⟨ρ, P, Q, hP, hQ, eP, eQ⟩ := exists_triples W (k := (G ⊗ G).left.residueField z)
      (x ≫ p ≫ U.ι) (x ≫ q ≫ U.ι) (by rw [Category.assoc, Category.assoc x, hpq])
    obtain ⟨h, e⟩ := hs₂ ((G ⊗ G).left.residueField z) x ρ P Q hP hQ eP eQ
    have nP := hns ((G ⊗ G).left.residueField z) (x ≫ p) ρ P hP ((Category.assoc _ _ _).trans eP)
    have nQ := hns ((G ⊗ G).left.residueField z) (x ≫ q) ρ Q hQ ((Category.assoc _ _ _).trans eQ)
    have := (hU _ ρ _ h).mpr (WeierstrassCurve.Projective.nonsingular_add nP nQ)
    rw [← e] at this
    have h2 : s (x (IsLocalRing.closedPoint _)) ∈ U := this (Set.mem_univ _)
    have h3 : x (IsLocalRing.closedPoint _) = z := Scheme.fromSpecResidueField_apply z _
    rw [h3] at h2
    rw [Scheme.Opens.range_ι]
    exact h2
  have hl : IsOpenImmersion.lift U.ι s hr ≫ U.ι = s := IsOpenImmersion.lift_fac ..
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι s hr) ?_, ?_⟩
  · change IsOpenImmersion.lift U.ι s hr ≫ U.ι ≫ WeierstrassCurve.toSpec W = (G ⊗ G).hom
    rw [← Category.assoc, hl, hs₁, Category.assoc, hp]
  · intro k _ ρ x y P Q hP hQ ex ey
    let w : Spec (.of k) ⟶ (G ⊗ G).left := (lift x y).left
    have e₁ : w ≫ p = x.left := congrArg (·.left) (lift_fst x y)
    have e₂ : w ≫ q = y.left := congrArg (·.left) (lift_snd x y)
    obtain ⟨h, e⟩ := hs₂ k w ρ P Q hP hQ
      (by rw [← Category.assoc, e₁]; exact ex) (by rw [← Category.assoc, e₂]; exact ey)
    refine ⟨h, ?_⟩
    change (w ≫ IsOpenImmersion.lift U.ι s hr) ≫ U.ι = _
    rw [Category.assoc, hl, e]

end GlobalTheory
