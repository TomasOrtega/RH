import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointExtendsAlongThetaMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapAbelianSchemeNormalCharZeroBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapPullO1PowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapFiniteGeometricFibresOfLargeLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsProjectivelyIntegralNormalModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeCoefficientFieldNormalNoetherianSepaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteNormalNormalisationProjectiveSpaceArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMorphismValuativeLiftingNormalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMinTop

/- English proof (translation)
Use `haveI : NumberField F := ⟨⟩`. Establish `h3 : (N : 𝓞 F) ≠ 0` using `by exact_mod_cast hN`. Establish `hM : Submonoid.powers (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F)` using `powers_le_nonZeroDivisors_of_noZeroDivisors h3`. Establish `hg : ∀ y : Submonoid.powers (N : 𝓞 F), IsUnit (algebraMap (𝓞 F) F y)` using `fun y => IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero (hM y.2)))`. Set `o` to `Localization.Away (N : 𝓞 F)`.

Set `b : o →+* F` to `IsLocalization.lift (M := Submonoid.powers (N : 𝓞 F)) hg`. Establish `hb : ∀ a : 𝓞 F, b (algebraMap (𝓞 F) o a) = algebraMap (𝓞 F) F a` using `fun a => IsLocalization.lift_eq (M := Submonoid.powers (N : 𝓞 F)) hg a`. Use `haveI : IsDomain o := IsLocalization.isDomain_localization hM`. Use `⟨o, inferInstance, b, ?_, IsLocalization.isDedekindDomain (𝓞 F) hM o, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.lift_injective_iff]`.

Introduce `x y`. Rewrite using `[(IsLocalization.injective o hM).eq_iff, (IsFractionRing.injective (𝓞 F) F).eq_iff]`. Establish `: Algebra.FiniteType (𝓞 F) o` using `IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (N : 𝓞 F)) o`. Conclude with `@Algebra.FiniteType.trans ℤ (𝓞 F) o _ _ _ _ (Ring.toIntAlgebra o) _ _ inferInstance this`. Simplify `IsLocalization.Away.algebraMap_isUnit (S := o) (N : 𝓞 F)` using `only [map_intCast]`.

Introduce `x`. Take `⟨⟨a, d⟩, h⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 F)) x`. Use `⟨algebraMap (𝓞 F) o a, algebraMap (𝓞 F) o d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero d.2)`.

Rewrite using `[hb, hb]`. Conclude with `h`.
-/
theorem exists_baseRing_away (F : IntermediateField ℚ ℂ) (hF : FiniteDimensional ℚ F) (N : ℤ) (hN : N ≠ 0) :
    ∃ (o : Type) (_ : CommRing o) (b : o →+* F), Function.Injective b ∧ IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧
      IsUnit (N : o) ∧ ∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a := by
  haveI : NumberField F := ⟨⟩
  have h3 : (N : 𝓞 F) ≠ 0 := by exact_mod_cast hN
  have hM : Submonoid.powers (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors h3
  have hg : ∀ y : Submonoid.powers (N : 𝓞 F), IsUnit (algebraMap (𝓞 F) F y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2
      (nonZeroDivisors.ne_zero (hM y.2)))
  let o := Localization.Away (N : 𝓞 F)
  let b : o →+* F := IsLocalization.lift (M := Submonoid.powers (N : 𝓞 F)) hg
  have hb : ∀ a : 𝓞 F, b (algebraMap (𝓞 F) o a) = algebraMap (𝓞 F) F a := fun a =>
    IsLocalization.lift_eq (M := Submonoid.powers (N : 𝓞 F)) hg a
  haveI : IsDomain o := IsLocalization.isDomain_localization hM
  refine ⟨o, inferInstance, b, ?_, IsLocalization.isDedekindDomain (𝓞 F) hM o, ?_, ?_, ?_⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective o hM).eq_iff, (IsFractionRing.injective (𝓞 F) F).eq_iff]
  · have : Algebra.FiniteType (𝓞 F) o :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (N : 𝓞 F)) o
    exact @Algebra.FiniteType.trans ℤ (𝓞 F) o _ _ _ _ (Ring.toIntAlgebra o) _ _ inferInstance this
  · simpa only [map_intCast] using IsLocalization.Away.algebraMap_isUnit (S := o) (N : 𝓞 F)
  · intro x
    obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) x
    refine ⟨algebraMap (𝓞 F) o a, algebraMap (𝓞 F) o d, ?_, ?_⟩
    · rw [hb]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero d.2)
    · rw [hb, hb]; exact h

/- English proof (translation)
Introduce `o F _ _ _ _ _ _ b n X s f hb hfr hX hsep hlft hqc hcomm hfin`. Use `haveI : IsProper (PSpace.str o n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o n`. Use `haveI : QuasiCompact (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance`. Use `haveI : QuasiSeparated (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance`. Use `haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o n)`.

Use `haveI : QuasiSeparated f := QuasiSeparated.of_comp f (PSpace.str o n)`. Establish `hw : f.toNormalization ≫ (f.fromNormalization ≫ PSpace.str o n) = s ≫ spMap b`. Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hcomm]`. Take `⟨h1, h2⟩` from `GlobalTheory.T.isFinite_normal_normalisation_projectiveSpace_arith o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin`. Take `⟨h3, h4⟩` from `GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin (pullback.lift _ _ hw) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)`.

Use `⟨f.normalization, f.fromNormalization, pullback.lift _ _ hw, h1, h2, h3, h4, pullback.lift_snd _ _ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pullback.lift_fst_assoc, Scheme.Hom.toNormalization_fromNormalization]`. Rewrite using `[pullback.lift_fst]`. Conclude with `f.toNormalization.denseRange`.
-/
theorem integral_normal_model_dense : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n), Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o n) (iF : X ⟶ pullback (p ≫ PSpace.str o n) (spMap b)), IsFinite p ∧ Geo.Tor.IsNormalScheme Z ∧ IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = s ∧ iF ≫ pullback.fst _ _ ≫ p = f ∧ Dense (Set.range (iF ≫ pullback.fst _ _)) := by
  intro o F _ _ _ _ _ _ b n X s f hb hfr hX hsep hlft hqc hcomm hfin
  haveI : IsProper (PSpace.str o n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o n
  haveI : QuasiCompact (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance
  haveI : QuasiSeparated (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o n)
  haveI : QuasiSeparated f := QuasiSeparated.of_comp f (PSpace.str o n)
  have hw : f.toNormalization ≫ (f.fromNormalization ≫ PSpace.str o n) = s ≫ spMap b := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hcomm]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isFinite_normal_normalisation_projectiveSpace_arith o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin
  obtain ⟨h3, h4⟩ := GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin
    (pullback.lift _ _ hw) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨f.normalization, f.fromNormalization, pullback.lift _ _ hw, h1, h2, h3, h4,
    pullback.lift_snd _ _ _, ?_, ?_⟩
  · rw [pullback.lift_fst_assoc, Scheme.Hom.toNormalization_fromNormalization]
  · rw [pullback.lift_fst]
    exact f.toNormalization.denseRange

end GlobalTheory.UMinTop

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `h_dim` using `@GlobalTheory.UMin.polFib_univ`. Establish `h_xf` using `GlobalTheory.T.moduliScheme_coefficientField_normal_noetherian_separated`. Establish `h_map_gen` using `GlobalTheory.T.thetaMap_abelianScheme_normal_charZero_base`. Establish `h_qf` using `GlobalTheory.T.thetaMap_finite_geometricFibres_of_large_level`. Establish `h_zb` using `GlobalTheory.UMinTop.integral_normal_model_dense`.

Establish `h_zb_amp` using `@GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB`. Establish `h_zb_lift` using `GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain`. Establish `h_ext_P` using `GlobalTheory.T.uniformisedPoint_extends_along_thetaMap`. Establish `h_thint_P` using `GlobalTheory.T.thetaConstants_projectively_integral_normalModels`. Establish `h_om_P` using `GlobalTheory.T.theta_map_pull_O1_power`.

Introduce `E _ _ _ H Dw _ l Xo c`. Establish `hM'0 : l.M' ≠ 0` using `Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'`. Establish `hd0 : H.d ≠ 0` using `H.d_prime.ne_zero`. Establish `hD0 : NumberField.discr E ≠ 0` using `NumberField.discr_ne_zero E`. Take `⟨o, _, b, hb, hded, hft, hNu, hfr⟩` from `GlobalTheory.UMinTop.exists_baseRing_away c.F c.fin (3 * (l.M' : ℤ) * (H.d : ℤ) * NumberField.discr E) (by`.

Apply the tactic sequence `refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) hD0 <;> exact_mod_cast ‹_›)`. Establish `hNu' : IsUnit ((3 : o) * (l.M' : o) * (H.d : o) * ((NumberField.discr E : ℤ) : o))`. Simplify `hNu` using `[Int.cast_mul]`. Establish `h3 : IsUnit (3 : o)` using `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))`. Establish `hM'u : IsUnit (l.M' : o)` using `isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))`.

Establish `hdu : IsUnit (H.d : o)` using `isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hNu')`. Establish `hDu : IsUnit ((NumberField.discr E : ℤ) : o)` using `isUnit_of_mul_isUnit_right hNu'`. Use `haveI := hded`. Use `haveI := hft`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j : ℕ, 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 := by`.

Use `⟨81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial, ?_⟩` and prove the remaining obligations. Conclude with `lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 3)) (Nat.le_mul_of_pos_right _ (by norm_num))`. Take `⟨n, hn⟩ : ∃ n : ℕ, n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))` from `⟨_, Nat.succ_pred_eq_of_pos (by positivity)⟩`. Establish `hodd : Odd (3 ^ j * 81)` using `(Odd.pow (by decide)).mul (by decide)`. Establish `h3m : 3 ≤ 3 ^ j * 81` using `le_trans (by norm_num) (Nat.le_mul_of_pos_left 81 (by positivity))`.

Establish `hu : IsUnit ((3 ^ j * 81 : ℕ) : o)`. Establish `: ((3 ^ j * 81 : ℕ) : o) = 3 ^ (j + 4)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `h3.pow _`. Take `⟨hN, hno, hch, hsep, hlft, hqc⟩` from `h_xf E H Dw l Xo c`.

Take `⟨f, hf, hT⟩` from `h_map_gen Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ _ n o (Xo.XF c) (pullback.snd _ _ ≫ spMap b) (pullback.fst _ _) hodd h3m hu hn hN hno hch (fun R _ x => h_dim E H Dw l Xo c R _)`. Take `⟨Z, p, iF, hp, hZ, hio, hd, hs, hif, hdense⟩` from `h_zb o c.F b n (Xo.XF c) (pullback.snd _ _) f hb hfr hN hsep hlft hqc hf (h_qf E H Dw l Xo c o j n f hj hn hT)`. Establish `hD : 1 ≤ (n + 1).factorial` using `Nat.factorial_pos _`. Take `⟨hpr, hlb, ham, hpull⟩` from `h_zb_amp o n (8 * (n + 1).factorial) Z p (by omega) hp`. Use `⟨{ o := o, b := b, inj := hb, frac := ?_, ded := hded, ft := hft, unit_level := hM'u, unit_d := hdu, unit_discr := hDu, Z := Z, z := p ≫ PSpace.str o n, proj := hpr, normal := GlobalTheory.IsNormalScheme.of_pred hZ, iF := iF, iF_open := hio, iF_dense := hd, iF_over := hs, i_dense …` and prove the remaining obligations.

Use `omega := ?_, ext := ?_, thetaInt := ?_ }⟩`. Introduce `x`. Take `⟨a, d, hbd, e⟩` from `hfr x`. Conclude with `⟨a, d, eq_div_of_mul_eq hbd e⟩`. Introduce `Y g hg hY`.

Establish `e₂` using `h_om_P E H Dw l Xo c o _ n f hodd h3m hu hn hT Y ((g ≫ pullback.fst _ _) ≫ p) (by rw [Category.assoc, reassoc_of% hg, hif]) hY`. Conclude with `LBIso.trans (pull_isLB hlb _) (isLB_lbPow (pull_isLB (ProjSpace.O1_isLB o n) _) _) (isLB_lbPow hY _) (hpull _ (g ≫ pullback.fst _ _)) e₂`. Introduce `R _ _ _ hR t ht y hy σ hσ`. Take `⟨ξ₀, h₁, h₂⟩` from `h_ext_P E H Dw l Xo c o _ n f hodd h3m hu hn hT b hf R hR t ht y hy σ hσ`. Use `haveI := hR.1.2.2.1`.

Take `⟨ξ, h₃, h₄⟩` from `h_zb_lift R Z _ p ξ₀ (y ≫ iF ≫ pullback.fst _ _) hp (by simp only [Category.assoc, hif, h₁])`. Conclude with `⟨ξ, h₃, by rw [reassoc_of% h₄, h₂]⟩`. Introduce `o' Ω _ _ _ _ S ρ u hu' _ M π hM hπ`. Conclude with `h_thint_P E H Dw l Xo c o _ n f hodd h3m hu hn hT o' Ω S ρ u hu' M (π ≫ p) (@GlobalTheory.IsNormalScheme.pred _ hM) (by rw [reassoc_of% hπ]; simp only [Category.assoc, hif])`.
-/
theorem umin_theta_compactification_exists : UMinSt := by
  have h_dim := @GlobalTheory.UMin.polFib_univ
  have h_xf := GlobalTheory.T.moduliScheme_coefficientField_normal_noetherian_separated
  have h_map_gen := GlobalTheory.T.thetaMap_abelianScheme_normal_charZero_base
  have h_qf := GlobalTheory.T.thetaMap_finite_geometricFibres_of_large_level
  have h_zb := GlobalTheory.UMinTop.integral_normal_model_dense
  have h_zb_amp := @GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB
  have h_zb_lift := GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain
  have h_ext_P := GlobalTheory.T.uniformisedPoint_extends_along_thetaMap
  have h_thint_P := GlobalTheory.T.thetaConstants_projectively_integral_normalModels
  have h_om_P := GlobalTheory.T.theta_map_pull_O1_power
  intro E _ _ _ H Dw _ l Xo c
  have hM'0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hd0 : H.d ≠ 0 := H.d_prime.ne_zero
  have hD0 : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨o, _, b, hb, hded, hft, hNu, hfr⟩ := GlobalTheory.UMinTop.exists_baseRing_away c.F c.fin
    (3 * (l.M' : ℤ) * (H.d : ℤ) * NumberField.discr E) (by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) hD0 <;> exact_mod_cast ‹_›)
  have hNu' : IsUnit ((3 : o) * (l.M' : o) * (H.d : o) * ((NumberField.discr E : ℤ) : o)) := by
    simpa [Int.cast_mul] using hNu
  have h3 : IsUnit (3 : o) := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))
  have hM'u : IsUnit (l.M' : o) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))
  have hdu : IsUnit (H.d : o) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hNu')
  have hDu : IsUnit ((NumberField.discr E : ℤ) : o) := isUnit_of_mul_isUnit_right hNu'
  haveI := hded
  haveI := hft
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 := by
    refine ⟨81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 3)) (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) :=
    ⟨_, Nat.succ_pred_eq_of_pos (by positivity)⟩
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide)).mul (by decide)
  have h3m : 3 ≤ 3 ^ j * 81 := le_trans (by norm_num) (Nat.le_mul_of_pos_left 81 (by positivity))
  have hu : IsUnit ((3 ^ j * 81 : ℕ) : o) := by
    have : ((3 ^ j * 81 : ℕ) : o) = 3 ^ (j + 4) := by push_cast; ring
    rw [this]; exact h3.pow _
  obtain ⟨hN, hno, hch, hsep, hlft, hqc⟩ := h_xf E H Dw l Xo c
  obtain ⟨f, hf, hT⟩ := h_map_gen Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen
    _ _ n o (Xo.XF c) (pullback.snd _ _ ≫ spMap b) (pullback.fst _ _) hodd h3m hu hn hN hno hch
    (fun R _ x => h_dim E H Dw l Xo c R _)
  obtain ⟨Z, p, iF, hp, hZ, hio, hd, hs, hif, hdense⟩ := h_zb o c.F b n (Xo.XF c) (pullback.snd _ _) f hb hfr hN hsep hlft hqc hf
    (h_qf E H Dw l Xo c o j n f hj hn hT)
  have hD : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
  obtain ⟨hpr, hlb, ham, hpull⟩ := h_zb_amp o n (8 * (n + 1).factorial) Z p (by omega) hp
  refine ⟨{ o := o, b := b, inj := hb, frac := ?_, ded := hded, ft := hft, unit_level := hM'u, unit_d := hdu,
            unit_discr := hDu, Z := Z, z := p ≫ PSpace.str o n, proj := hpr, normal := GlobalTheory.IsNormalScheme.of_pred hZ,
            iF := iF, iF_open := hio, iF_dense := hd, iF_over := hs, i_dense := hdense, OZ := _, OZ_lb := hlb, OZ_ample := ham,
            N := 4 * (n + 1).factorial * (n + 1).factorial, N_pos := Nat.mul_pos (by omega) hD,
            omega := ?_, ext := ?_, thetaInt := ?_ }⟩
  · intro x
    obtain ⟨a, d, hbd, e⟩ := hfr x
    exact ⟨a, d, eq_div_of_mul_eq hbd e⟩
  · intro Y g hg hY
    have e₂ := h_om_P E H Dw l Xo c o _ n f hodd h3m hu hn hT Y ((g ≫ pullback.fst _ _) ≫ p)
      (by rw [Category.assoc, reassoc_of% hg, hif]) hY
    exact LBIso.trans (pull_isLB hlb _)
      (isLB_lbPow (pull_isLB (ProjSpace.O1_isLB o n) _) _) (isLB_lbPow hY _) (hpull _ (g ≫ pullback.fst _ _)) e₂
  · intro R _ _ _ hR t ht y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := h_ext_P E H Dw l Xo c o _ n f hodd h3m hu hn hT b hf R hR t ht y hy σ hσ
    haveI := hR.1.2.2.1
    obtain ⟨ξ, h₃, h₄⟩ := h_zb_lift R Z _ p ξ₀ (y ≫ iF ≫ pullback.fst _ _) hp (by simp only [Category.assoc, hif, h₁])
    exact ⟨ξ, h₃, by rw [reassoc_of% h₄, h₂]⟩
  · intro o' Ω _ _ _ _ S ρ u hu' _ M π hM hπ
    exact h_thint_P E H Dw l Xo c o _ n f hodd h3m hu hn hT o' Ω S ρ u hu' M (π ≫ p) (@GlobalTheory.IsNormalScheme.pred _ hM)
      (by rw [reassoc_of% hπ]; simp only [Category.assoc, hif])

end GlobalTheory
