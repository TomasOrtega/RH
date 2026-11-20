import Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsResolutionHomExistsOfEx

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Unfold `restr`. Conclude with `(Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))).isRightAdjoint`.
-/
lemma restr_isRightAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsRightAdjoint := by
  unfold restr
  exact (Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
    ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))).isRightAdjoint

/- English proof (translation)
Unfold `restr`. Use `set f := ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom))`. Establish `hpl : PreservesLimitsOfSize.{0, 1} (ModuleCat.coextendScalars.{1, 1, 1} f)` using `(ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).rightAdjoint_preservesLimits`. Establish `: Scheme.etaleTopology.{0}.HasSheafCompose (ModuleCat.coextendScalars.{1, 1, 1} f)` using `hasSheafCompose_of_preservesLimitsOfSize _`. Establish `adj` using `Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f)`.

Use `(sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit_isIso_of_R_fully_faithful` as an intermediate fact. Establish `e : Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) ≅ sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)` using `NatIso.ofComponents (fun X => (asIso (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).obj X)) (by`. Introduce `X Y g`. Conclude with `(sheafificationAdjunction _ _).counit.naturality ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).map g))`. Conclude with `⟨_, ⟨adj.ofNatIsoLeft e⟩⟩`.
-/
lemma restr_isLeftAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsLeftAdjoint := by
  unfold restr
  set f := ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom))
  have hpl : PreservesLimitsOfSize.{0, 1} (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).rightAdjoint_preservesLimits
  have : Scheme.etaleTopology.{0}.HasSheafCompose (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have adj := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f)
  have := (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit_isIso_of_R_fully_faithful
  have e : Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) ≅
      sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) :=
    NatIso.ofComponents (fun X => (asIso (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
      ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).obj X)) (by
        intro X Y g
        exact (sheafificationAdjunction _ _).counit.naturality
          ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).map g))
  exact ⟨_, ⟨adj.ofNatIsoLeft e⟩⟩

/- English proof (translation)
Introduce `R S _ _ φ`. Use `restr_isRightAdjoint R S φ` as an intermediate fact. Use `restr_isLeftAdjoint R S φ` as an intermediate fact. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem etaleSheaf_restrictScalars_functor_exact_of_adjoints : EtaleSheafRestrictScalarsFunctorExact := by
  intro R S _ _ φ
  have := restr_isRightAdjoint R S φ
  have := restr_isLeftAdjoint R S φ
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleFoundations
