import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FormallyUnramifiedOfIsFinite
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVRStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivGeneric

/- English proof (translation)
Establish `h₁ : IsDominant (jK V)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩`. Establish `h₂ : IsDominant (jFK (R` using `V) F) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (FractionRing V) F).injective).le.trans bot_le)⟩`. Establish `h₃ : IsDominant (TF (R` using `V) F).hom := inferInstanceAs (IsDominant (jFK (R := V) F ≫ jK V))`. Establish `h₄ : IsReduced (Spec (CommRingCat.of V))` using `inferInstance`. Conclude with `IsSchemeTheoreticallyDominant.of_isDominant _`.
-/
theorem dominant_field (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] :
    IsSchemeTheoreticallyDominant (TF (R := V) F).hom := by
  have h₁ : IsDominant (jK V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have h₂ : IsDominant (jFK (R := V) F) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (FractionRing V) F).injective).le.trans bot_le)⟩
  have h₃ : IsDominant (TF (R := V) F).hom := inferInstanceAs (IsDominant (jFK (R := V) F ≫ jK V))
  have h₄ : IsReduced (Spec (CommRingCat.of V)) := inferInstance
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/- English proof (translation)
Introduce `hG V _ _ _ _ B _ _ hB L c hL hx`. Establish `hLB : L.L.IsLB` using `L.isLB`. Take `⟨d, -, n, s, hs⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L.L hLB).1 hL`. Establish `hP : IsProjBy B.hom` using `⟨_, isLB_pw hLB _, n, s, hs⟩`. Take `⟨hO, hu, hK⟩` from `GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L.L hLB`.

Take `⟨H, j, hj, hH⟩` from `GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB hP L.L (pw L.L 0) hLB hO`. Establish `hfin : IsFinite H.hom` using `GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L.L (pw L.L 0) hLB hO hL H j hj hH`. Establish `hflat : Flat H.hom` using `GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hG V B hB hP L c (pw L.L 0) hO hu H j hj hH hfin`. Establish `hrep : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), InK B L.L x ↔ ∃ y : T ⟶ H, y ≫ j = x` using `fun T x => (hK _ rfl T x).trans (hH T x)`. Establish `hm : Mono j` using `(Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))`.

Establish `hchar : CharZero (AlgebraicClosure (FractionRing V))` using `inferInstance`. Establish `key` using `GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hrep _ _).1 (inK_one hLB _)) (fun T x y => (hrep _ _).1 (InK.mul hLB ((hrep _ _).2 ⟨x, rfl⟩) (InK.inv hLB ((hrep _ _).2 ⟨y, rfl⟩)))) (AlgebraicClosure (FractionRing V)) (TF (R := V) (AlgebraicClosure (FractionRing V))).hom (fun x …`. Establish `hd` using `dominant_field V (AlgebraicClosure (FractionRing V))`. Establish `hsep : IsSeparated B.hom`. Use `hB.proper` as an intermediate fact.

Use `infer_instance`. Establish `hj1 : j = 1`. Set `T` to `TF (R := V) (AlgebraicClosure (FractionRing V))`. Establish `h1 : fst H T ≫ j = fst H T ≫ 1`. Rewrite using `[MonObj.comp_one]`.

Conclude with `key (H ⊗ T) (snd H T) (fst H T)`. Establish `h0 : QuasiCompact T.hom` using `inferInstanceAs (QuasiCompact (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V))`. Establish `h2 : IsSchemeTheoreticallyDominant (fst H T).left` using `IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback H.hom T.hom).flip`. Conclude with `GlobalTheory.over_ext_of_schemeTheoreticallyDominant (fst H T).left (congrArg (fun q => q.left) h1)`. Use `kTriv_iff_forall.2 fun T x hxK => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `(hrep T x).1 hxK`. Rewrite using `[hj1, MonObj.comp_one]`.
-/
theorem kTriv_of_generic : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L), RelAmple B L.L → (∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ B, InK B L.L x → x = 1) → KTriv B L.L := by
  intro hG V _ _ _ _ B _ _ hB L c hL hx
  have hLB : L.L.IsLB := L.isLB
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L.L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L.L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB hP L.L (pw L.L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L.L (pw L.L 0) hLB hO hL H j hj hH
  have hflat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hG V B hB hP L c (pw L.L 0) hO hu H j hj hH hfin
  have hrep : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), InK B L.L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have hchar : CharZero (AlgebraicClosure (FractionRing V)) := inferInstance
  have key := GlobalTheory.FiniteOnePoint.main _ B H j hm hfin ((hrep _ _).1 (inK_one hLB _))
    (fun T x y => (hrep _ _).1 (InK.mul hLB ((hrep _ _).2 ⟨x, rfl⟩) (InK.inv hLB ((hrep _ _).2 ⟨y, rfl⟩))))
    (AlgebraicClosure (FractionRing V)) (TF (R := V) (AlgebraicClosure (FractionRing V))).hom
    (fun x => hx _ ((hrep _ _).2 ⟨x, rfl⟩))
  have hd := dominant_field V (AlgebraicClosure (FractionRing V))
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have hj1 : j = 1 := by
    let T := TF (R := V) (AlgebraicClosure (FractionRing V))
    have h1 : fst H T ≫ j = fst H T ≫ 1 := by
      rw [MonObj.comp_one]
      exact key (H ⊗ T) (snd H T) (fst H T)
    have h0 : QuasiCompact T.hom :=
      inferInstanceAs (QuasiCompact (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V))
    have h2 : IsSchemeTheoreticallyDominant (fst H T).left :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback H.hom T.hom).flip
    exact GlobalTheory.over_ext_of_schemeTheoreticallyDominant (fst H T).left (congrArg (fun q => q.left) h1)
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivGeneric
