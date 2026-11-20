import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KTrivAndPolAtTensAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalOfGenericFibreDvr
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperAfterLocalizationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem pull_ample_kTriv {S S' : Scheme.{0}} [IsAffine S] {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) :
    Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S)
    (fun _ => trivial) hA, kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem ample_kTriv_of_iso {S S' : Scheme.{0}} [IsAffine S'] {t : SAB H S} {u : SAB H S'} {j : S' ⟶ S} [IsIso j]
    (m : SABMap u t j) (hA : Out.RelAmple u.G u.PP.L) (hK : Out.KTriv u.G u.PP.L) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac m n (g := inv j) (by simp)
  exact pull_ample_kTriv m' hA hK

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (hf : Function.Bijective f) :
    IsIso (spMap f) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hf).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isProper_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (hp : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback m.cart.1 hp

end GlobalTheory.PolLocal

namespace GlobalTheory.PolLocal

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem algebraMap_fractionRing_bijective (O : Type) [CommRing O] [IsDomain O] (hf : IsField O) :
    Function.Bijective (algebraMap O (FractionRing O)) := by
  refine ⟨IsFractionRing.injective O (FractionRing O), fun z => ?_⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) z
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel (nonZeroDivisors.ne_zero y.2)
  refine ⟨x * b, ?_⟩
  calc algebraMap O (FractionRing O) (x * b) = z * algebraMap O (FractionRing O) (y * b) := by
        rw [map_mul, map_mul, ← mul_assoc, ← hxy]
    _ = z := by rw [hb, map_one, mul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem algebraMap_away_bijective {O : Type} [CommRing O] (r : O) (hr : IsUnit r) :
    Function.Bijective (algebraMap O (Localization.Away r)) := by
  have e := IsLocalization.atUnit O (Localization.Away r) r hr
  have h : ⇑(algebraMap O (Localization.Away r)) = ⇑e := funext fun x => by
    simpa using (e.commutes x).symm
  rw [h]
  exact e.bijective

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem relAmple_kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type)
    [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O], IsIntegrallyClosed O →
    ∀ (t : SAB H (Sp O)), IsProper t.G.hom → GlobalTheory.LN.PolAt t (Out.jK O) →
      Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  intro E _ _ _ H O _ _ _ _ _ hIC t hprop hpol
  by_cases hf : IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := isIso_spMap _ (algebraMap_fractionRing_bijective O hf)
    exact ample_kTriv_of_iso mu hA hK
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull (spMap (algebraMap V (FractionRing V))) tV
  let ψ : FractionRing O →+* FractionRing V := IsLocalization.map (M := nonZeroDivisors O) (T := nonZeroDivisors V)
    (FractionRing V) ρ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ hρ)
  have heq : spMap ψ ≫ Out.jK O = Out.jK V ≫ spMap ρ := by
    show spMap ψ ≫ spMap (algebraMap O (FractionRing O)) = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp, IsLocalization.map_comp]
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.DatUniq.polAt_pull mV hpol (Out.jK V) (spMap ψ) heq
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, t', m', -, hA', hK'⟩ := GlobalTheory.T.proper_after_localization E H O hIC t hpol (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  haveI := isIso_spMap _ (algebraMap_away_bijective r hu)
  exact ample_kTriv_of_iso m' hA' hK'

end GlobalTheory.PolLocal
