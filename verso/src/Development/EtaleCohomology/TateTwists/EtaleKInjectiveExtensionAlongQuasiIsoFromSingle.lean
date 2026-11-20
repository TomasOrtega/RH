import Development.EtaleCohomology.TateTwists.EtaleTwistResolutionUniversalExtension

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε],
    (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F

def LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (φ ψ : tw q i ⟶ M),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) → φ = ψ

def LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], FlatS M

def LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) [Injective M] (U : Scheme.{0}), Module.Injective (ULift.{1} R) (Sec M U)

def LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (N : Type 1) [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N],
    Module.Injective (ULift.{1} (ZMod q)) N → Module.Flat (ULift.{1} (ZMod q)) N

/- English proof (translation)
Introduce `q _ M _`. Use `⟨M.obj, 𝟙 _, fun U y => ?_, fun U x hx => ?_, fun U _ => hQ q _ (hS _ M U)⟩` and prove the remaining obligations. Conclude with `⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g y, rfl⟩⟩`. Use `⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩` and prove the remaining obligations. Establish `hx0 : x = 0` using `hx`.

Substitute `hx0` using the available equality. Conclude with `map_zero _`.
-/
theorem LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective)
    (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) : LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat := by
  intro q _ M _
  refine ⟨M.obj, 𝟙 _, fun U y => ?_, fun U x hx => ?_, fun U _ => hQ q _ (hS _ M U)⟩
  · exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g y, rfl⟩⟩
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
    have hx0 : x = 0 := hx
    subst hx0
    exact map_zero _

namespace LateralTheory.EtaleFoundations.TwResExt

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard in
/- English proof (translation)
Establish `: IsIso (DerivedCategory.Q.map ε)` using `inferInstance`. Conclude with `(NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) ε).2 this`.
-/
theorem qh_iso {S T : CochainComplex C ℤ} (ε : S ⟶ T) [QuasiIso ε] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ε)) := by
  have : IsIso (DerivedCategory.Q.map ε) := inferInstance
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) ε).2 this

attribute [local instance] HasDerivedCategory.standard in
/- English proof (translation)
Use `qh_iso ε` as an intermediate fact. Use `set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)`. Take `⟨g, hg⟩` from `(CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).2 (inv (DerivedCategory.Qh.map (qt.map ε)) ≫ DerivedCategory.Qh.map (qt.map a))`. Take `⟨m, rfl⟩` from `qt.map_surjective g`. Use `⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩` and prove the remaining obligations.

Apply `(CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) I).1` to reduce the goal to its premises. Rewrite using `[Functor.map_comp, Functor.map_comp]`. Use `erw [hg]`. Conclude with `IsIso.hom_inv_id_assoc _ _`.
-/
theorem kinj_lift {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ I) :
    ∃ m : T ⟶ I, Nonempty (Homotopy (ε ≫ m) a) := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).2
    (inv (DerivedCategory.Qh.map (qt.map ε)) ≫ DerivedCategory.Qh.map (qt.map a))
  obtain ⟨m, rfl⟩ := qt.map_surjective g
  refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) I).1
  rw [Functor.map_comp, Functor.map_comp]
  erw [hg]
  exact IsIso.hom_inv_id_assoc _ _

attribute [local instance] HasDerivedCategory.standard in
/- English proof (translation)
Use `qh_iso ε` as an intermediate fact. Use `set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)`. Use `⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩` and prove the remaining obligations. Apply `(CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).1` to reduce the goal to its premises. Rewrite using `[← cancel_epi (DerivedCategory.Qh.map (qt.map ε)), ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, h]`.
-/
theorem kinj_uniq {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (m m' : T ⟶ I)
    (h : ε ≫ m = ε ≫ m') : Nonempty (Homotopy m m') := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).1
  rw [← cancel_epi (DerivedCategory.Qh.map (qt.map ε)), ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, h]

/- English proof (translation)
Establish `hz : ∀ i j, h.hom i j = 0`. Introduce `i j`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Distinguish the cases in `hr : (ComplexShape.up ℤ).Rel j 0`.

Establish `hj : j < 0` using `by simp [ComplexShape.up_Rel] at hr; omega`. Conclude with `(I.isZero_of_isStrictlyGE 0 j hj).eq_of_tgt _ _`. Conclude with `h.zero _ _ hr`. Conclude with `(HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _`. Use extensionality with `n`.

Rewrite using `[h.comm n]`. Establish `: h.hom = 0` using `by funext i j; exact hz i j`. Simplify using `[this]`.
-/
theorem homotopy_single_eq {F : C} {I : CochainComplex C ℤ} [I.IsStrictlyGE 0]
    (f g : (CochainComplex.singleFunctor C 0).obj F ⟶ I) (h : Homotopy f g) : f = g := by
  have hz : ∀ i j, h.hom i j = 0 := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      by_cases hr : (ComplexShape.up ℤ).Rel j 0
      · have hj : j < 0 := by simp [ComplexShape.up_Rel] at hr; omega
        exact (I.isZero_of_isStrictlyGE 0 j hj).eq_of_tgt _ _
      · exact h.zero _ _ hr
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  ext n
  rw [h.comm n]
  have : h.hom = 0 := by funext i j; exact hz i j
  simp [this]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

/- English proof (translation)
Introduce `R _ F T I _ _ ε _`. Use `⟨fun a => ?_, fun m m' h => kinj_uniq ε m m' h⟩` and prove the remaining obligations. Take `⟨m, ⟨hm⟩⟩` from `kinj_lift ε a`. Conclude with `⟨m, homotopy_single_eq _ _ hm⟩`.
-/
theorem ext_hom_pf : LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => kinj_uniq ε m m' h⟩
  obtain ⟨m, ⟨hm⟩⟩ := kinj_lift ε a
  exact ⟨m, homotopy_single_eq _ _ hm⟩

/- English proof (translation)
Introduce `R _ F`. Use `⟨?_, fun n => ?_, ?_, ?_, rfl⟩` and prove the remaining obligations. Conclude with `inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)`. Conclude with `inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))`. Conclude with `inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)`.

Conclude with `inferInstanceAs (QuasiIso (injectiveResolution F).ι')`.
-/
theorem res_pf : LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties := by
  intro R _ F
  refine ⟨?_, fun n => ?_, ?_, ?_, rfl⟩
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)
  · exact inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  · exact inferInstanceAs (QuasiIso (injectiveResolution F).ι')

end LateralTheory.EtaleFoundations.TwResExt

/- English proof (translation)
Rewrite using `[map_smul, map_smul, map_smul, h]`.
-/
theorem LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq {S A B C : Type*} [Ring S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (t : A →ₗ[S] B) (f g : B →ₗ[S] C) (x : A) (b : S)
    (h : f (t x) = g (t x)) : f (t (b • x)) = g (t (b • x)) := by
  rw [map_smul, map_smul, map_smul, h]

/- English proof (translation)
Introduce `q _ i M φ ψ h`. Apply `Sheaf.hom_ext` to reduce the goal to its premises. Use `CategoryTheory.sheafify_hom_ext (J := Scheme.etaleTopology) (P := Scheme.Γ ⋙ twF q i) φ.hom ψ.hom M.cond ?_` and prove the remaining obligations. Use `NatTrans.ext (funext fun U => ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_)))` and prove the remaining obligations. Establish `h1` using `h (unop U) ζ`.

Express the relevant statement in the definitionally equal form `(φ.hom.app U).hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i) |>.app U).hom (Submodule.Quotient.mk (Finsupp.single ζ b))) = (ψ.hom.app U).hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i) |>.app U).hom (Submodule.Quotient.mk (Finsupp.single ζ b)))`. Rewrite using `[← Finsupp.smul_single_one, Submodule.Quotient.mk_smul]`. Conclude with `LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq _ _ _ _ b h1`.
-/
theorem LateralTheory.EtaleFoundations.TwResExt.twuniq_pf : LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators := by
  intro q _ i M φ ψ h
  apply Sheaf.hom_ext
  refine CategoryTheory.sheafify_hom_ext (J := Scheme.etaleTopology) (P := Scheme.Γ ⋙ twF q i) φ.hom ψ.hom M.cond ?_
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_)))
  have h1 := h (unop U) ζ
  change (φ.hom.app U).hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i) |>.app U).hom
      (Submodule.Quotient.mk (Finsupp.single ζ b))) = (ψ.hom.app U).hom ((toSheafify Scheme.etaleTopology
      (Scheme.Γ ⋙ twF q i) |>.app U).hom (Submodule.Quotient.mk (Finsupp.single ζ b)))
  rw [← Finsupp.smul_single_one, Submodule.Quotient.mk_smul]
  exact LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq _ _ _ _ b h1

open LateralTheory.EtaleFoundations.TwResExt in
/- English proof (translation)
Establish `hF` using `LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat hS hQ`. Establish `hE` using `ext_hom_pf`. Establish `hR` using `res_pf`. Establish `hU` using `twuniq_pf`. Introduce `q _ i`.

Take `⟨hK, hInj, hGE, hQ, hι⟩` from `hR (ZMod q) (tw q i)`. Establish `hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map ((resAug (tw q i)).f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = resGen i ζ`. Introduce `U ζ`. Rewrite using `[← sec_map_comp, hι]`. Both sides reduce to the same expression.

Use `⟨⟨hGE, resAug _, hQ, hgen⟩, fun t => ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hInj t`. Conclude with `hF q _`. Introduce `T e hT`. Take `⟨_, ε, hε, he⟩` from `hT`.

Use `hε` as an intermediate fact. Use `hK` as an intermediate fact. Use `hGE` as an intermediate fact. Take `⟨hex, huniq⟩` from `hE (ZMod q) (tw q i) T (res _ (tw q i)) ε`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨m, hm⟩` from `hex (resAug _)`. Use `⟨m, fun U ζ => ?_⟩` and prove the remaining obligations. Rewrite using `[← he, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]`. Conclude with `hgen U ζ`. Introduce `u u' h`.

Apply `huniq` to reduce the goal to its premises. Apply `HomologicalComplex.from_single_hom_ext` to reduce the goal to its premises. Establish `hφ : sglι (tw q i) ≫ (ε ≫ u).f 0 = sglι (tw q i) ≫ (ε ≫ u').f 0`. Apply `hU q i` to reduce the goal to its premises. Introduce `U ζ`.

Simplify using `only [sec_map_comp, HomologicalComplex.comp_f]`. Establish `h1` using `h U ζ`. Rewrite `h1` using `[← he]`. Conclude with `h1`. Establish `hiso : IsIso (sglι (tw q i))` using `Iso.isIso_inv _`.

Conclude with `(cancel_epi (sglι (tw q i))).1 hφ`.
-/
theorem LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective) (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) :
    LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  have hF := LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat hS hQ
  have hE := ext_hom_pf
  have hR := res_pf
  have hU := twuniq_pf
  intro q _ i
  obtain ⟨hK, hInj, hGE, hQ, hι⟩ := hR (ZMod q) (tw q i)
  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map ((resAug (tw q i)).f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = resGen i ζ := by
    intro U ζ
    rw [← sec_map_comp, hι]
    rfl
  refine ⟨⟨hGE, resAug _, hQ, hgen⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact hF q _
  · intro T e hT
    obtain ⟨_, ε, hε, he⟩ := hT
    have := hε
    have := hK
    have := hGE
    obtain ⟨hex, huniq⟩ := hE (ZMod q) (tw q i) T (res _ (tw q i)) ε
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hm⟩ := hex (resAug _)
      refine ⟨m, fun U ζ => ?_⟩
      rw [← he, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
      exact hgen U ζ
    · intro u u' h
      apply huniq
      apply HomologicalComplex.from_single_hom_ext
      have hφ : sglι (tw q i) ≫ (ε ≫ u).f 0 = sglι (tw q i) ≫ (ε ≫ u').f 0 := by
        apply hU q i
        intro U ζ
        simp only [sec_map_comp, HomologicalComplex.comp_f]
        have h1 := h U ζ
        rw [← he] at h1
        exact h1
      have hiso : IsIso (sglι (tw q i)) := Iso.isIso_inv _
      exact (cancel_epi (sglι (tw q i))).1 hφ
