import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.FourierExpansionCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralScalarEqWhittakerScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasseNormGroupProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSupportProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedDatumValueAtZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalWhittakerCentralCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormGlobalCentralScalarEqOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepresentativesForAdmissibleDataStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNormOneUnitsTrivialValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumOverCosetRepresentativesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionDiagonalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionUnitRotationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaGlobalCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaModulusRationalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormEqualsComplexAbsSqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIntegralUnitShiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnitTranslateValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaZeroTermUnipotentInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientHasSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitIntegralAlmostEverywhereStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationVectorHomomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalThetaCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedLocalThetaCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCoefficientUnitInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLocalCoefficientValuesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCoefficientVanishesAtLargeOrderStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCoefficientNormOneTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldCoefficientNormOneTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWhittakerDiagonalNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWhittakerDiagonalNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaZeroTermNormInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductCharacterNormOneTrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharactersTrivialOfNonzeroAverageStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver

open GlobalTheory.CompanionTheory.FexTheta

noncomputable section
namespace GlobalTheory.CompanionTheory.FexMain

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_representatives_for_admissible_data`.
-/
theorem L_reps : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → ∃ R : Finset (Pl →₀ ℤ), IsReps M R := GlobalTheory.T.exists_representatives_for_admissible_data

/- English proof (translation)
The claim follows from `GlobalTheory.T.finite_norm_one_units_trivial_valuation`.
-/
theorem L_stab : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → Finite {κ : K1 K // vK M (κ : Kˣ) = 0} := GlobalTheory.T.finite_norm_one_units_trivial_valuation

/- English proof (translation)
The claim follows from `GlobalTheory.T.hasSum_over_coset_representatives`.
-/
theorem L_unfold : ∀ {H A : Type} [CommGroup H] [AddCommGroup A] (T : AddSubgroup A) (φ : H → A), (∀ h, φ h ∈ T) →
  (∀ a b, φ (a * b) = φ a + φ b) → ∀ R : Finset A, (∀ r ∈ R, r ∈ T) →
  (∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ h, m = r + φ h) → Finite {h : H // φ h = 0} →
  ∀ (F : A → ℂ) (s : ℂ), HasSum (fun m : T => F m) s →
    HasSum (fun h : H => ∑ r ∈ R, F (r + φ h)) ((Nat.card {h : H // φ h = 0} : ℂ) * s) := GlobalTheory.T.hasSum_over_coset_representatives

/- English proof (translation)
The claim follows from `GlobalTheory.T.real_weil_action_diagonal`.
-/
theorem L_rsim : ∀ (n : ℤ) (t : ℝ) (z : ℂˣ) (a : ℝˣ), (a : ℝ) = ‖(z : ℂ)‖ ^ 2 → ∀ (g : GL (Fin 2) ℝ) (x : ℂ),
  piRc (chC n (Complex.I * t)) (dg2 a 1 * g) (PhiInf n) x =
    chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * piRc (chC n (Complex.I * t)) g (PhiInf n) (x * z) := GlobalTheory.T.real_weil_action_diagonal

/- English proof (translation)
The claim follows from `GlobalTheory.T.real_weil_action_unit_rotation`.
-/
theorem L_riso : ∀ (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (x u : ℂ), ‖u‖ = 1 →
  piRc (chC n (Complex.I * t)) g (PhiInf n) (x * u) = u ^ (-n) * piRc (chC n (Complex.I * t)) g (PhiInf n) x := GlobalTheory.T.real_weil_action_unit_rotation

/- English proof (translation)
The claim follows from `GlobalTheory.T.product_formula_global_character`.
-/
theorem L_hecke : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, (∀ v, (M v).ok) → ∀ κ : Kˣ,
    (Function.mulSupport fun v : Pl => cW (M v) κ).Finite ∧
      (∏ᶠ v : Pl, cW (M v) κ) * chC n (Complex.I * t) (embU κ) = 1 := GlobalTheory.T.product_formula_global_character

/- English proof (translation)
The claim follows from `GlobalTheory.T.product_formula_modulus_rational`.
-/
theorem L_pf : ∀ α : ℚˣ, (Function.mulSupport fun v : Pl => mp (Ad3.R.lc v (pri α)) (1 / 2)).Finite ∧
  (∏ᶠ v : Pl, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((|(α : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := GlobalTheory.T.product_formula_modulus_rational

/- English proof (translation)
The claim follows from `GlobalTheory.T.norm_equals_complex_abs_sq`.
-/
theorem L_normemb : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ κ : Kˣ,
  (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 ∧
  ((RationalIdeles.realPart (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) : ℝˣ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 := GlobalTheory.T.norm_equals_complex_abs_sq

/- English proof (translation)
The claim follows from `GlobalTheory.T.product_integral_unit_shift`.
-/
theorem L_prodsum : ∀ (Sp : Pl → Prop) (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∈ Sv, Sp v) → (∀ v, Measurable (f v)) →
  (∀ v, ∃ C : ℝ, ∀ x, ‖f v x‖ ≤ C) → (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  (∃ B : Finset Pl, ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1 ∧ (Sp v → ∀ k : ℤ, k ≠ 0 → f v (unifUnit (Qv v) ^ k) = 0)) →
  (∀ v, Sp v → ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v, f v (unifUnit (Qv v) ^ k * u) = 0) →
  (Function.mulSupport (locF Sp f)).Finite ∧
    HasSum (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} => ∫ u, ∏ᶠ v, f v (tu Sv m.1 u v) ∂muU Sv) (∏ᶠ v, locF Sp f v) := GlobalTheory.T.product_integral_unit_shift

/- English proof (translation)
The claim follows from `GlobalTheory.T.integral_unit_translate_valuation`.
-/
theorem L_shift : ∀ (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  ∀ (k : ∀ v : Pl, (Qv v)ˣ) (m' : Pl →₀ ℤ), (∀ v, ord ((k v : (Qv v)ˣ) : Qv v) = m' v) → ∀ m : Pl →₀ ℤ,
    ∫ u, ∏ᶠ v, f v (tu Sv m u v * k v) ∂muU Sv = ∫ u, ∏ᶠ v, f v (tu Sv (m + m') u v) ∂muU Sv := GlobalTheory.T.integral_unit_translate_valuation

/- English proof (translation)
The claim follows from `GlobalTheory.T.theta_zero_term_unipotent_invariant`.
-/
theorem L_thn : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ (x : 𝔸[ℚ]) (g : G2), thT n t M (uni2 x * g) 0 = thT n t M g 0 := GlobalTheory.T.theta_zero_term_unipotent_invariant

/- English proof (translation)
The claim follows from `GlobalTheory.T.theta_fourier_coefficient_hasSum`.
-/
theorem L_summ : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K)
  (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ), ∀ g ∈ Gp M,
    HasSum (fun ξ : K => aT n t M Sv g m ξ) (∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv) := GlobalTheory.T.theta_fourier_coefficient_hasSum

/- English proof (translation)
The claim follows from `GlobalTheory.T.valuation_vector_homomorphism`.
-/
theorem L_vk : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
    (∀ (κ : Kˣ) (v : Pl), vK M κ v = ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)) ∧ (∀ κ : Kˣ, vK M κ ∈ Tm M) ∧
      ∀ a b : Kˣ, vK M (a * b) = vK M a + vK M b := GlobalTheory.T.valuation_vector_homomorphism

/- English proof (translation)
The claim follows from `GlobalTheory.T.theta_zero_term_norm_invariance`.
-/
theorem L_th0diag : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → (∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1) → ∀ (κ : Kˣ) (g : G2),
    thT n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) 0 = thT n t M g 0 := GlobalTheory.T.theta_zero_term_norm_invariance
/- English proof (translation)
Introduce `K _ _ h2 c v L hL g ξ κ hκ x`. Distinguish the cases in `hs : L.IsSp`. Conclude with `GlobalTheory.T.split_coefficient_norm_one_twist K h2 c v L hL hs g ξ κ hκ x`. Conclude with `GlobalTheory.T.field_coefficient_norm_one_twist K h2 c v L hL hs g ξ κ hκ x`.
-/
theorem L_liso : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (κ : Kˣ), κ ∈ K1 K → ∀ x : (Qv v)ˣ,
    fL L g (ξ * κ) x * cW L κ = fL L g ξ (x * k1 L κ) := by
  intro K _ _ h2 c v L hL g ξ κ hκ x
  by_cases hs : L.IsSp
  · exact GlobalTheory.T.split_coefficient_norm_one_twist K h2 c v L hL hs g ξ κ hκ x
  · exact GlobalTheory.T.field_coefficient_norm_one_twist K h2 c v L hL hs g ξ κ hκ x

/- English proof (translation)
Introduce `K _ _ h2 c v L hL g κ`. Distinguish the cases in `hs : L.IsSp`. Conclude with `GlobalTheory.T.split_whittaker_diagonal_norm K h2 c v L hL hs g κ`. Conclude with `GlobalTheory.T.field_whittaker_diagonal_norm K h2 c v L hL hs g κ`.
-/
theorem L_lsim : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  intro K _ _ h2 c v L hL g κ
  by_cases hs : L.IsSp
  · exact GlobalTheory.T.split_whittaker_diagonal_norm K h2 c v L hL hs g κ
  · exact GlobalTheory.T.field_whittaker_diagonal_norm K h2 c v L hL hs g κ

/- English proof (translation)
Introduce `K _ _ h2 c M hM Sv hS g κ`. Use `⟨fun v => GlobalTheory.T.measurable_local_theta_coefficient K h2 c v (M v) (hM.1 v) _ _, fun v => GlobalTheory.T.bounded_local_theta_coefficient K h2 c v (M v) (hM.1 v) _ _, fun v hv x e he => GlobalTheory.T.local_theta_coefficient_unit_invariant K h2 c v (M v) (hM.1 v) ?_ _ _ x …` and prove the remaining obligations. Distinguish the cases in `hs : (M v).IsSp`. Conclude with `Or.inr (hS.2 v hv hs)`. Conclude with `Or.inl hs`.

Take `⟨hok, S0, hS0⟩` from `hM`. Take `⟨S1, hS1⟩` from `GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g`. Take `⟨S2, hS2⟩` from `GlobalTheory.T.global_unit_integral_almost_everywhere K κ`. Use `⟨S0 ∪ S1 ∪ S2 ∪ Sv, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_union, not_or] at hv`.

Take `⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩` from `hv`. Use `GlobalTheory.T.standard_local_coefficient_values K h2 c v (M v) (hok v) (hS0 v h0).1 (hS0 v h0).2 _ (hS1 v h1) κ (hS2 v h2')` as an intermediate fact. Conclude with `⟨h3, this.1, this.2⟩`.
-/
theorem L_fam : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ Sv : Finset Pl, GoodSv M Sv → ∀ (g : G2) (κ : Kˣ),
    (∀ v, Measurable (fL (M v) (finAt v g) (κ : K))) ∧
    (∀ v, ∃ C : ℝ, ∀ x, ‖fL (M v) (finAt v g) (κ : K) x‖ ≤ C) ∧
    (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, fL (M v) (finAt v g) (κ : K) (x * e) = fL (M v) (finAt v g) (κ : K) x) ∧
    (∃ B : Finset Pl, ∀ v ∉ B, v ∉ Sv ∧ fL (M v) (finAt v g) (κ : K) 1 = 1 ∧
      ((M v).IsSp → ∀ k : ℤ, k ≠ 0 → fL (M v) (finAt v g) (κ : K) (unifUnit (Qv v) ^ k) = 0)) ∧
    (∀ v, (M v).IsSp → ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v,
      fL (M v) (finAt v g) (κ : K) (unifUnit (Qv v) ^ k * u) = 0) := by
  classical
  intro K _ _ h2 c M hM Sv hS g κ
  refine ⟨fun v => GlobalTheory.T.measurable_local_theta_coefficient K h2 c v (M v) (hM.1 v) _ _, fun v => GlobalTheory.T.bounded_local_theta_coefficient K h2 c v (M v) (hM.1 v) _ _,
    fun v hv x e he => GlobalTheory.T.local_theta_coefficient_unit_invariant K h2 c v (M v) (hM.1 v) ?_ _ _ x e he, ?_,
    fun v hs => GlobalTheory.T.split_coefficient_vanishes_at_large_order K h2 c v (M v) (hM.1 v) hs _ _⟩
  · by_cases hs : (M v).IsSp
    · exact Or.inr (hS.2 v hv hs)
    · exact Or.inl hs
  · obtain ⟨hok, S0, hS0⟩ := hM
    obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
    obtain ⟨S2, hS2⟩ := GlobalTheory.T.global_unit_integral_almost_everywhere K κ
    refine ⟨S0 ∪ S1 ∪ S2 ∪ Sv, fun v hv => ?_⟩
    simp only [Finset.mem_union, not_or] at hv
    obtain ⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩ := hv
    have := GlobalTheory.T.standard_local_coefficient_values K h2 c v (M v) (hok v) (hS0 v h0).1 (hS0 v h0).2 _ (hS1 v h1) κ (hS2 v h2')
    exact ⟨h3, this.1, this.2⟩

variable {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K}

/- English proof (translation)
Apply the tactic sequence `cases L <;> simp [LM.ct]`.
-/
theorem ct_base {v : Pl} (L : LM c v) : L.ct 1 = 1 := by
  cases L <;> simp [LM.ct]

/- English proof (translation)
Simplify using `[tu, h1, h2]`.
-/
theorem tu_off (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (v : Pl) (h1 : v ∉ Sv) (h2 : m v = 0) :
    tu Sv m u v = 1 := by
  simp [tu, h1, h2]

/- English proof (translation)
Unfold `ctM`. Use `(finprod_eq_prod_of_mulSupport_subset _ ?_).symm` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises.

Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn`. Use `show (M v).ct (tu Sv m u v) = 1`. Rewrite using `[tu_off Sv m u v hn.2 hn.1, ct_base]`.
-/
theorem ctM_eq (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) :
    ctM M Sv m u = ∏ᶠ v, (M v).ct (tu Sv m u v) := by
  classical
  unfold ctM
  refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro v hv
  by_contra hn
  apply hv
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
  show (M v).ct (tu Sv m u v) = 1
  rw [tu_off Sv m u v hn.2 hn.1, ct_base]

/- English proof (translation)
Take `⟨-, -, -, ⟨B, hB⟩, -⟩` from `L_fam K h2 c M hM Sv hS g κ`. Unfold `aT`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `show ctM M Sv m u * thT n t (twM M Sv m u) g (κ : K) = _ * ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v)`.

Establish `hct : (Function.mulSupport fun v => (M v).ct (tu Sv m u v)).Finite`. Use `(m.support ∪ Sv).finite_toSet.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn`.

Use `show (M v).ct (tu Sv m u v) = 1`. Rewrite using `[tu_off Sv m u v hn.2 hn.1, ct_base]`. Establish `hval : (Function.mulSupport fun v => ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)).Finite`. Use `(B ∪ m.support ∪ Sv).finite_toSet.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Apply `hv` to reduce the goal to its premises. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn`. Establish `h1` using `(hB v hn.1.1).2.1`. Use `show ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K) = 1`. Rewrite using `[tu_off Sv m u v hn.2 hn.1.2]`.

Simplify `h1` using `[fL, ct_base]`. Establish `e : (∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v)) = (∏ᶠ v, (M v).ct (tu Sv m u v)) * ∏ᶠ v, ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)` using `finprod_mul_distrib hct hval`. Rewrite using `[e, ← ctM_eq, thT]`. Use `show _ * (_ * ∏ᶠ v, ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fact (h2 : Module.finrank ℚ K = 2) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (Sv : Finset Pl)
    (hS : GoodSv M Sv) (g : G2) (κ : Kˣ) (m : Pl →₀ ℤ) :
    aT n t M Sv g m (κ : K) = piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K (κ : K)) *
      ∫ u, ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v) ∂muU Sv := by
  classical
  obtain ⟨-, -, -, ⟨B, hB⟩, -⟩ := L_fam K h2 c M hM Sv hS g κ
  unfold aT
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ctM M Sv m u * thT n t (twM M Sv m u) g (κ : K) = _ * ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v)
  have hct : (Function.mulSupport fun v => (M v).ct (tu Sv m u v)).Finite := by
    refine (m.support ∪ Sv).finite_toSet.subset fun v hv => ?_
    by_contra hn
    apply hv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
    show (M v).ct (tu Sv m u v) = 1
    rw [tu_off Sv m u v hn.2 hn.1, ct_base]
  have hval : (Function.mulSupport fun v => ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)).Finite := by
    refine (B ∪ m.support ∪ Sv).finite_toSet.subset fun v hv => ?_
    by_contra hn
    apply hv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
    have h1 := (hB v hn.1.1).2.1
    show ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K) = 1
    rw [tu_off Sv m u v hn.2 hn.1.2]
    simpa [fL, ct_base] using h1
  have e : (∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v)) =
      (∏ᶠ v, (M v).ct (tu Sv m u v)) * ∏ᶠ v, ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K) :=
    finprod_mul_distrib hct hval
  rw [e, ← ctM_eq, thT]
  show _ * (_ * ∏ᶠ v, ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)) = _
  ring

/- English proof (translation)
Simplify using `[chC, ha]`.
-/
theorem chC_norm_one (n : ℤ) (s : ℂ) (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) : chC n s a = (a : ℂ) ^ n := by
  simp [chC, ha]

/- English proof (translation)
Establish `h` using `(L_normemb K h2 hC κ).1`. Establish `h1 : Units.map (Algebra.norm ℚ : K →* ℚ) κ = 1` using `hκ`. Rewrite `h` using `[h1]`. Establish `h3 : ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 = 1` using `by simpa using h.symm`. Establish `h4` using `norm_nonneg ((embU κ : ℂˣ) : ℂ)`.

Use polynomial arithmetic with `[sq_nonneg (‖((embU κ : ℂˣ) : ℂ)‖ - 1)]`.
-/
theorem norm_complex_embedding_norm_one (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) (κ : Kˣ) (hκ : κ ∈ K1 K) :
    ‖((embU κ : ℂˣ) : ℂ)‖ = 1 := by
  have h := (L_normemb K h2 hC κ).1
  have h1 : Units.map (Algebra.norm ℚ : K →* ℚ) κ = 1 := hκ
  rw [h1] at h
  have h3 : ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 = 1 := by simpa using h.symm
  have h4 := norm_nonneg ((embU κ : ℂˣ) : ℂ)
  nlinarith [sq_nonneg (‖((embU κ : ℂˣ) : ℂ)‖ - 1)]

/- English proof (translation)
Simplify using `[embC, embU]`.
-/
theorem embC_mul (a b : Kˣ) : embC K ((a * b : Kˣ) : K) = embC K (a : K) * ((embU b : ℂˣ) : ℂ) := by
  simp [embC, embU]

/- English proof (translation)
Take `⟨-, -, hinv, -, -⟩` from `L_fam K h2 c M hM Sv hS g ξ`. Take `⟨-, -, -, ⟨B, hB⟩, -⟩` from `L_fam K h2 c M hM Sv hS g (ξ * κ)`. Take `⟨hcf, hP⟩` from `L_hecke K h2 hC DK c n t S hA M hM.1 κ`. Establish `hnorm` using `norm_complex_embedding_norm_one h2 hC κ hκ`. Establish `hu0 : ((embU κ : ℂˣ) : ℂ) ≠ 0` using `(embU κ).ne_zero`.

Rewrite `hP` using `[chC_norm_one n _ _ hnorm]`. Rewrite using `[fact h2 n t M hM Sv hS g (ξ * κ) m, fact h2 n t M hM Sv hS g ξ (m + vK M κ)]`. Rewrite using `[← L_shift Sv _ hinv (fun v => k1 (M v) κ) (vK M κ) (fun v => ((L_vk K h2 c M hM).1 κ v).symm) m]`. Establish `hpt : ∀ u, ∏ᶠ v, fL (M v) (finAt v g) (ξ : K) (tu Sv m u v * k1 (M v) κ) = (∏ᶠ v, fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v)) * ∏ᶠ v, cW (M v) κ`. Introduce `u`.

Establish `hf : (Function.mulSupport fun v => fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v)).Finite`. Use `(B ∪ m.support ∪ Sv).finite_toSet.subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Simplify using `only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn`.

Use `show fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v) = 1`. Rewrite using `[tu_off Sv m u v hn.2 hn.1.2]`. Conclude with `(hB v hn.1.1).2.1`. Rewrite using `[← finprod_mul_distrib hf hcf]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, L_liso K h2 c v (M v) (hM.1 v) (finAt v g) (ξ : K) κ hκ]`. Simplify using `only [hpt]`. Rewrite using `[integral_mul_const, embC_mul, L_riso n t _ _ _ hnorm]`. Establish `hz : ((embU κ : ℂˣ) : ℂ) ^ (-n) = ∏ᶠ v, cW (M v) κ`. Rewrite using `[zpow_neg]`.

Conclude with `(eq_inv_of_mul_eq_one_left hP).symm`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem equiv (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) {DK : DatK K} {n : ℤ} {t : ℝ}
    {S : Finset (PlK K)} (hA : AdmK DK c n t S) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (Sv : Finset Pl)
    (hS : GoodSv M Sv) (g : G2) (ξ κ : Kˣ) (hκ : κ ∈ K1 K) (m : Pl →₀ ℤ) :
    aT n t M Sv g m ((ξ * κ : Kˣ) : K) = aT n t M Sv g (m + vK M κ) (ξ : K) := by
  classical
  obtain ⟨-, -, hinv, -, -⟩ := L_fam K h2 c M hM Sv hS g ξ
  obtain ⟨-, -, -, ⟨B, hB⟩, -⟩ := L_fam K h2 c M hM Sv hS g (ξ * κ)
  obtain ⟨hcf, hP⟩ := L_hecke K h2 hC DK c n t S hA M hM.1 κ
  have hnorm := norm_complex_embedding_norm_one h2 hC κ hκ
  have hu0 : ((embU κ : ℂˣ) : ℂ) ≠ 0 := (embU κ).ne_zero
  rw [chC_norm_one n _ _ hnorm] at hP
  rw [fact h2 n t M hM Sv hS g (ξ * κ) m, fact h2 n t M hM Sv hS g ξ (m + vK M κ)]
  rw [← L_shift Sv _ hinv (fun v => k1 (M v) κ) (vK M κ) (fun v => ((L_vk K h2 c M hM).1 κ v).symm) m]
  have hpt : ∀ u, ∏ᶠ v, fL (M v) (finAt v g) (ξ : K) (tu Sv m u v * k1 (M v) κ) =
      (∏ᶠ v, fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v)) * ∏ᶠ v, cW (M v) κ := by
    intro u
    have hf : (Function.mulSupport fun v => fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v)).Finite := by
      refine (B ∪ m.support ∪ Sv).finite_toSet.subset fun v hv => ?_
      by_contra hn
      apply hv
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
      show fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v) = 1
      rw [tu_off Sv m u v hn.2 hn.1.2]
      exact (hB v hn.1.1).2.1
    rw [← finprod_mul_distrib hf hcf]
    refine finprod_congr fun v => ?_
    rw [Units.val_mul, L_liso K h2 c v (M v) (hM.1 v) (finAt v g) (ξ : K) κ hκ]
  simp only [hpt]
  rw [integral_mul_const, embC_mul, L_riso n t _ _ _ hnorm]
  have hz : ((embU κ : ℂˣ) : ℂ) ^ (-n) = ∏ᶠ v, cW (M v) κ := by
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_left hP).symm
  rw [hz]
  ring

open Classical in
/- English proof (translation)
Consider the cases of `L with`. Consider the case `sp w₁ w₂ Φ => simp [locI, LM.IsSp]`. Consider the case `ns w σ η Φ => simp [locI, LM.IsSp, fL, LM.ct, LM.tw]`.
-/
theorem locI_eq' {v : Pl} (L : LM c v) (g : GL (Fin 2) (Qv v)) (ξ : K) :
    locI L g ξ = if L.IsSp then ∫ x, fL L g ξ x ∂multHaar (Qv v) else fL L g ξ 1 := by
  cases L with
  | sp w₁ w₂ Φ => simp [locI, LM.IsSp]
  | ns w σ η Φ => simp [locI, LM.IsSp, fL, LM.ct, LM.tw]

/- English proof (translation)
Rewrite using `[locI_eq']`. Both sides reduce to the same expression.
-/
theorem locI_eq (M : ∀ v : Pl, LM c v) (g : G2) (ξ : K) (v : Pl) :
    locI (M v) (finAt v g) ξ = locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) ξ) v := by
  rw [locI_eq']
  rfl

/- English proof (translation)
Establish `h : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ)` using `by push_cast; ring`. Rewrite using `[← h, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]`.
-/
theorem cpow_half_sq (r : ℝ) (hr : 0 ≤ r) : (((r ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (r : ℂ) := by
  have h : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [← h, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

/- English proof (translation)
Take `⟨hm, hb, hinv, hfin, hsupp⟩` from `L_fam K h2 c M hM Sv hS g κ`. Take `⟨hmul, hsum⟩` from `L_prodsum (fun v => (M v).IsSp) Sv (fun v => fL (M v) (finAt v g) (κ : K)) hS.1 hm hb hinv hfin hsupp`. Take `⟨hcf, hP⟩` from `L_hecke K h2 hC DK c n t S hA M hM.1 κ`. Take `⟨hmp, hQ⟩` from `L_pf (Units.map (Algebra.norm ℚ : K →* ℚ) κ)`. Take `⟨hn1, hn2⟩` from `L_normemb K h2 hC κ`.

Take `⟨hc1, hc2, hc3, -⟩` from `GlobalTheory.T.adelic_realPart_properties`. Use `set R := piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K (κ : K)) with hR`. Use `set α := Units.map (Algebra.norm ℚ : K →* ℚ) κ with hα`. Use `set z := embU κ with hz`. Establish `hW : WM n t M (dg2 (pri α) 1 * g) = R * ∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v`.

Establish `hloc : ∀ v, (M v).W (finAt v (dg2 (pri α) 1 * g)) = cW (M v) κ * mp (Ad3.R.lc v (pri α)) (1 / 2) * locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v`. Introduce `v`. Establish `h1 : finAt v (dg2 (pri α) 1 * g) = dg2 (nv v κ) 1 * finAt v g`. Rewrite using `[GroundTheory.Automorphic.Reduction.finAt_mul, hc1]`. Simplify using `[nv, hα, Ad3.R.lc]`.

Rewrite using `[h1, L_lsim K h2 c v (M v) (hM.1 v), locI_eq]`. Both sides reduce to the same expression. Establish `hre : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart (dg2 (pri α) 1 * g)) = chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * R`. Establish `h1 : GL2Classical.realPart (dg2 (pri α) 1 * g) = dg2 (RationalIdeles.realPart (pri α)) 1 * GL2Classical.realPart g`. Rewrite using `[hc2, hc3, map_one]`.

Rewrite using `[h1]`. Establish `h2'` using `L_rsim n t z (RationalIdeles.realPart (pri α)) hn2 (GL2Classical.realPart g) 1`. Rewrite `h2'` using `[one_mul]`. Conclude with `h2'`. Unfold `WM pw2`.

Rewrite using `[hre, finprod_congr hloc, finprod_mul_distrib ((hcf.union hmp).subset (Function.mulSupport_mul _ _)) hmul, finprod_mul_distrib hcf hmp]`. Establish `hq : ((|(((α : ℚˣ) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ)`. Establish `: |(((α : ℚˣ) : ℚ) : ℝ)| = ‖(z : ℂ)‖ ^ 2`. Rewrite using `[hn1, abs_of_nonneg (by positivity)]`. Rewrite using `[this]`.

Conclude with `cpow_half_sq _ (norm_nonneg _)`. Rewrite `hQ` using `[hq]`. Take the linear combination `(R * (∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v) * (∏ᶠ v, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((‖(z : ℂ)‖ : ℝ) : ℂ)) * hP + (R * ∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v) * hQ`. Rewrite using `[hW]`. Set `e : Tm M ≃ {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → (M v).IsSp}` to `Equiv.subtypeEquivRight fun _ => Iff.rfl`.

Establish `h3` using `hsum.mul_left R`. Establish `h4` using `(e.hasSum_iff).2 h3`. Establish `e2 : (fun m : Tm M => aT n t M Sv g m (κ : K)) = (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → (M v).IsSp} => R * ∫ u, ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m.1 u v) ∂muU Sv) ∘ e`. Use function extensionality and compare the values at `m`. Conclude with `fact h2 n t M hM Sv hS g κ m.1`.

Rewrite using `[e2]`. Conclude with `h4`.
-/
theorem sumt (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) {DK : DatK K} {n : ℤ} {t : ℝ}
    {S : Finset (PlK K)} (hA : AdmK DK c n t S) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (Sv : Finset Pl)
    (hS : GoodSv M Sv) (g : G2) (κ : Kˣ) :
    HasSum (fun m : Tm M => aT n t M Sv g m (κ : K))
      (WM n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g)) := by
  classical
  obtain ⟨hm, hb, hinv, hfin, hsupp⟩ := L_fam K h2 c M hM Sv hS g κ
  obtain ⟨hmul, hsum⟩ := L_prodsum (fun v => (M v).IsSp) Sv (fun v => fL (M v) (finAt v g) (κ : K)) hS.1 hm hb hinv hfin hsupp
  obtain ⟨hcf, hP⟩ := L_hecke K h2 hC DK c n t S hA M hM.1 κ
  obtain ⟨hmp, hQ⟩ := L_pf (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
  obtain ⟨hn1, hn2⟩ := L_normemb K h2 hC κ
  obtain ⟨hc1, hc2, hc3, -⟩ := GlobalTheory.T.adelic_realPart_properties
  set R := piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K (κ : K)) with hR
  set α := Units.map (Algebra.norm ℚ : K →* ℚ) κ with hα
  set z := embU κ with hz
  have hW : WM n t M (dg2 (pri α) 1 * g) = R * ∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v := by
    have hloc : ∀ v, (M v).W (finAt v (dg2 (pri α) 1 * g)) =
        cW (M v) κ * mp (Ad3.R.lc v (pri α)) (1 / 2) * locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v := by
      intro v
      have h1 : finAt v (dg2 (pri α) 1 * g) = dg2 (nv v κ) 1 * finAt v g := by
        rw [GroundTheory.Automorphic.Reduction.finAt_mul, hc1]
        simp [nv, hα, Ad3.R.lc]
      rw [h1, L_lsim K h2 c v (M v) (hM.1 v), locI_eq]
      rfl
    have hre : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart (dg2 (pri α) 1 * g)) =
        chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * R := by
      have h1 : GL2Classical.realPart (dg2 (pri α) 1 * g) = dg2 (RationalIdeles.realPart (pri α)) 1 * GL2Classical.realPart g := by
        rw [hc2, hc3, map_one]
      rw [h1]
      have h2' := L_rsim n t z (RationalIdeles.realPart (pri α)) hn2 (GL2Classical.realPart g) 1
      rw [one_mul] at h2'
      exact h2'
    unfold WM pw2
    rw [hre, finprod_congr hloc, finprod_mul_distrib ((hcf.union hmp).subset (Function.mulSupport_mul _ _)) hmul,
      finprod_mul_distrib hcf hmp]
    have hq : ((|(((α : ℚˣ) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) := by
      have : |(((α : ℚˣ) : ℚ) : ℝ)| = ‖(z : ℂ)‖ ^ 2 := by
        rw [hn1, abs_of_nonneg (by positivity)]
      rw [this]
      exact cpow_half_sq _ (norm_nonneg _)
    rw [hq] at hQ
    linear_combination (R * (∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v) *
        (∏ᶠ v, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((‖(z : ℂ)‖ : ℝ) : ℂ)) * hP +
      (R * ∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v) * hQ
  rw [hW]
  let e : Tm M ≃ {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → (M v).IsSp} := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have h3 := hsum.mul_left R
  have h4 := (e.hasSum_iff).2 h3
  have e2 : (fun m : Tm M => aT n t M Sv g m (κ : K)) =
      (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → (M v).IsSp} => R * ∫ u, ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m.1 u v) ∂muU Sv) ∘ e := by
    funext m
    exact fact h2 n t M hM Sv hS g κ m.1
  rw [e2]
  exact h4

/- English proof (translation)
Rewrite using `[map_mul]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[dg2, Matrix.det_fin_two]`.
-/
theorem det_diagonal_one_mul (a : Jd) (g : G2) :
    Matrix.GeneralLinearGroup.det (dg2 a 1 * g) = a * Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  congr 1
  apply Units.ext
  simp [dg2, Matrix.det_fin_two]

/- English proof (translation)
Take `⟨D, -, hGp, hDN⟩` from `GlobalTheory.CompanionTheory.HasseGp.gpd K h2 hC c M hM`. Use `GlobalTheory.CompanionTheory.WSupport.wsup K h2 c n t M hM _ fun h => hα ?_` and prove the remaining obligations. Rewrite `h`, `hg` using `[hGp]`. Establish `h1 : pri α * Matrix.GeneralLinearGroup.det g ∈ D`. Establish `: Matrix.GeneralLinearGroup.det (dg2 (pri α) 1 * g) ∈ D` using `h`.

Rewrite `this` using `[det_diagonal_one_mul]`. Then use the resulting hypothesis. Establish `h3 : pri α ∈ D`. Use `D.mul_mem h1 (D.inv_mem hg)` as an intermediate fact. Simplify using `using this`. Conclude with `(hDN α).1 h3`.
-/
theorem wvanish (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v)
    (hM : AdmM M) (g : G2) (hg : g ∈ Gp M) (α : ℚˣ) (hα : α ∉ NmK K) : WM n t M (dg2 (pri α) 1 * g) = 0 := by
  obtain ⟨D, -, hGp, hDN⟩ := GlobalTheory.CompanionTheory.HasseGp.gpd K h2 hC c M hM
  refine GlobalTheory.CompanionTheory.WSupport.wsup K h2 c n t M hM _ fun h => hα ?_
  rw [hGp] at h hg
  have h1 : pri α * Matrix.GeneralLinearGroup.det g ∈ D := by
    have : Matrix.GeneralLinearGroup.det (dg2 (pri α) 1 * g) ∈ D := h
    rwa [det_diagonal_one_mul] at this
  have h3 : pri α ∈ D := by
    have := D.mul_mem h1 (D.inv_mem hg)
    simpa using this
  exact (hDN α).1 h3

/- English proof (translation)
Use `set I : K → ℂ := fun ξ => ∑ m ∈ R, aT n t M Sv g m ξ with hI`. Establish `hIs : HasSum I (thA R Sv n t M g)` using `hasSum_sum fun m _ => L_summ K h2 hC c n t M hM Sv m g hg`. Establish `hI0 : I 0 = th0 R Sv n t M g` using `rfl`. Establish `h1` using `hIs.update 0 0`. Establish `h1' : HasSum (Function.update I 0 0) (thA R Sv n t M g - th0 R Sv n t M g)`.

Establish `e0 : (0 : ℂ) - I 0 + thA R Sv n t M g = thA R Sv n t M g - th0 R Sv n t M g`. Rewrite using `[hI0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e0]`. Then use the resulting hypothesis. Establish `hU : HasSum (fun κ : Kˣ => I (κ : K)) (thA R Sv n t M g - th0 R Sv n t M g)`.

Establish `hinj : Function.Injective ((↑) : Kˣ → K)` using `Units.val_injective`. Establish `h2'` using `(hinj.hasSum_iff (f := Function.update I 0 0) (by`. Introduce `x hx`. Distinguish the cases in `h0 : x = 0`. Simplify using `[h0]`.

Conclude with `absurd ⟨Units.mk0 x h0, rfl⟩ hx)).2 h1'`. Establish `e : (Function.update I 0 0 ∘ ((↑) : Kˣ → K)) = fun κ : Kˣ => I (κ : K)`. Use function extensionality and compare the values at `κ`. Simplify using `[Function.update_of_ne κ.ne_zero]`. Rewrite `h2'` using `[e]`. Then use the resulting hypothesis.

Establish `hF` using `hU.tsum_fiberwise (Units.map (Algebra.norm ℚ : K →* ℚ))`. Establish `hst` using `L_stab K h2 hC c M hM`. Take `⟨hvk1, hvkT, hvkA⟩` from `L_vk K h2 c M hM`. Establish `hfun : (fun α : ℚˣ => (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ) * WM n t M (dg2 (pri α) 1 * g)) = fun α : ℚˣ => ∑' b : (Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {α}, I ((b : Kˣ) : K)`. Use function extensionality and compare the values at `α`.

Distinguish the cases in `hα : α ∈ NmK K`. Take `⟨ξ₀, rfl⟩` from `MonoidHom.mem_range.1 hα`. Set `e : K1 K ≃ ((Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {Units.map (Algebra.norm ℚ : K →* ℚ) ξ₀})` to `{ toFun := fun κ => ⟨ξ₀ * (κ : Kˣ), by`. Establish `h3 : Units.map (Algebra.norm ℚ : K →* ℚ) (κ : Kˣ) = 1` using `κ.2`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, h3, mul_one]⟩`.

Use `invFun := fun b => ⟨ξ₀⁻¹ * (b : Kˣ), by`. Establish `h3 : Units.map (Algebra.norm ℚ : K →* ℚ) (b : Kˣ) = Units.map (Algebra.norm ℚ : K →* ℚ) ξ₀` using `b.2`. Use `show Units.map (Algebra.norm ℚ : K →* ℚ) (ξ₀⁻¹ * (b : Kˣ)) = 1`. Rewrite using `[map_mul, h3, map_inv, inv_mul_cancel]⟩`. Use `left_inv := fun κ => Subtype.ext (by simp)`.

Use `right_inv := fun b => Subtype.ext (by simp) }`. Establish `hsum` using `L_unfold (Tm M) (fun h : K1 K => vK M (h : Kˣ)) (fun h => hvkT _) (fun a b => hvkA _ _) R hR.1 (fun m hm => by`. Take `⟨r, ⟨hr, κ, hκ, e1⟩, hu⟩` from `hR.2 m hm`. Conclude with `⟨r, ⟨hr, ⟨κ, hκ⟩, e1⟩, fun r' h' => by`. Take `⟨hr', κ', e'⟩` from `h'`.

Conclude with `hu r' ⟨hr', κ'.1, κ'.2, e'⟩⟩) hst`. Use the proof step `(fun m => aT n t M Sv g m (ξ₀ : K)) _ (sumt h2 hC hA M hM Sv hS g ξ₀)`. Rewrite using `[← e.tsum_eq, ← hsum.tsum_eq]`. Use `tsum_congr fun κ => ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Conclude with `(equiv h2 hC hA M hM Sv hS g ξ₀ κ κ.2 r).symm`. Establish `hemp : IsEmpty ((Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {α})` using `⟨fun b => hα (MonoidHom.mem_range.2 ⟨b.1, b.2⟩)⟩`. Rewrite using `[wvanish h2 hC n t M hM g hg α hα, tsum_empty, mul_zero]`. Rewrite using `[hfun]`. Conclude with `hF`.
-/
theorem expansion (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) {DK : DatK K} {n : ℤ} {t : ℝ}
    {S : Finset (PlK K)} (hA : AdmK DK c n t S) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (R : Finset (Pl →₀ ℤ))
    (hR : IsReps M R) (Sv : Finset Pl) (hS : GoodSv M Sv) (g : G2) (hg : g ∈ Gp M) :
    HasSum (fun α : ℚˣ => (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ) * WM n t M (dg2 (pri α) 1 * g))
      (thA R Sv n t M g - th0 R Sv n t M g) := by
  classical
  set I : K → ℂ := fun ξ => ∑ m ∈ R, aT n t M Sv g m ξ with hI
  have hIs : HasSum I (thA R Sv n t M g) := hasSum_sum fun m _ => L_summ K h2 hC c n t M hM Sv m g hg
  have hI0 : I 0 = th0 R Sv n t M g := rfl
  have h1 := hIs.update 0 0
  have h1' : HasSum (Function.update I 0 0) (thA R Sv n t M g - th0 R Sv n t M g) := by
    have e0 : (0 : ℂ) - I 0 + thA R Sv n t M g = thA R Sv n t M g - th0 R Sv n t M g := by
      rw [hI0]; ring
    rwa [e0] at h1
  have hU : HasSum (fun κ : Kˣ => I (κ : K)) (thA R Sv n t M g - th0 R Sv n t M g) := by
    have hinj : Function.Injective ((↑) : Kˣ → K) := Units.val_injective
    have h2' := (hinj.hasSum_iff (f := Function.update I 0 0) (by
      intro x hx
      by_cases h0 : x = 0
      · simp [h0]
      · exact absurd ⟨Units.mk0 x h0, rfl⟩ hx)).2 h1'
    have e : (Function.update I 0 0 ∘ ((↑) : Kˣ → K)) = fun κ : Kˣ => I (κ : K) := by
      funext κ
      simp [Function.update_of_ne κ.ne_zero]
    rwa [e] at h2'
  have hF := hU.tsum_fiberwise (Units.map (Algebra.norm ℚ : K →* ℚ))
  have hst := L_stab K h2 hC c M hM
  obtain ⟨hvk1, hvkT, hvkA⟩ := L_vk K h2 c M hM
  have hfun : (fun α : ℚˣ => (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ) * WM n t M (dg2 (pri α) 1 * g)) =
      fun α : ℚˣ => ∑' b : (Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {α}, I ((b : Kˣ) : K) := by
    funext α
    by_cases hα : α ∈ NmK K
    · obtain ⟨ξ₀, rfl⟩ := MonoidHom.mem_range.1 hα
      let e : K1 K ≃ ((Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {Units.map (Algebra.norm ℚ : K →* ℚ) ξ₀}) :=
        { toFun := fun κ => ⟨ξ₀ * (κ : Kˣ), by
            have h3 : Units.map (Algebra.norm ℚ : K →* ℚ) (κ : Kˣ) = 1 := κ.2
            simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, h3, mul_one]⟩
          invFun := fun b => ⟨ξ₀⁻¹ * (b : Kˣ), by
            have h3 : Units.map (Algebra.norm ℚ : K →* ℚ) (b : Kˣ) = Units.map (Algebra.norm ℚ : K →* ℚ) ξ₀ := b.2
            show Units.map (Algebra.norm ℚ : K →* ℚ) (ξ₀⁻¹ * (b : Kˣ)) = 1
            rw [map_mul, h3, map_inv, inv_mul_cancel]⟩
          left_inv := fun κ => Subtype.ext (by simp)
          right_inv := fun b => Subtype.ext (by simp) }
      have hsum := L_unfold (Tm M) (fun h : K1 K => vK M (h : Kˣ)) (fun h => hvkT _)
        (fun a b => hvkA _ _) R hR.1 (fun m hm => by
          obtain ⟨r, ⟨hr, κ, hκ, e1⟩, hu⟩ := hR.2 m hm
          exact ⟨r, ⟨hr, ⟨κ, hκ⟩, e1⟩, fun r' h' => by
            obtain ⟨hr', κ', e'⟩ := h'
            exact hu r' ⟨hr', κ'.1, κ'.2, e'⟩⟩) hst
        (fun m => aT n t M Sv g m (ξ₀ : K)) _ (sumt h2 hC hA M hM Sv hS g ξ₀)
      rw [← e.tsum_eq, ← hsum.tsum_eq]
      refine tsum_congr fun κ => ?_
      refine Finset.sum_congr rfl fun r _ => ?_
      exact (equiv h2 hC hA M hM Sv hS g ξ₀ κ κ.2 r).symm
    · have hemp : IsEmpty ((Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {α}) :=
        ⟨fun b => hα (MonoidHom.mem_range.2 ⟨b.1, b.2⟩)⟩
      rw [wvanish h2 hC n t M hM g hg α hα, tsum_empty, mul_zero]
  rw [hfun]
  exact hF

/- English proof (translation)
Simplify using `only [thT]`. Use `congr 1`. Conclude with `finprod_congr fun v => GlobalTheory.CompanionTheory.TwistZero.val_tw_zero K c v (M v) _ _`.
-/
theorem theta_twisted_data_value_at_zero (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (g : G2) :
    thT n t (twM M Sv m u) g 0 = thT n t M g 0 := by
  simp only [thT]
  congr 1
  exact finprod_congr fun v => GlobalTheory.CompanionTheory.TwistZero.val_tw_zero K c v (M v) _ _

/- English proof (translation)
Simplify using `only [th0, theta_twisted_data_value_at_zero, Finset.sum_mul, integral_mul_const]`.
-/
theorem thetaZero_periodLattice_eq (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (g : G2) :
    th0 R Sv n t M g = (∑ m ∈ R, ∫ u, ctM M Sv m u ∂muU Sv) * thT n t M g 0 := by
  simp only [th0, theta_twisted_data_value_at_zero, Finset.sum_mul, integral_mul_const]

/- English proof (translation)
Introduce `K _ _ h2 hC DK c n t S hA M hM R hR Sv hS g h`. Rewrite `h` using `[thetaZero_periodLattice_eq]`. Establish `h1` using `left_ne_zero_of_mul h`. Establish `h3` using `right_ne_zero_of_mul h`. Conclude with `GlobalTheory.T.local_characters_trivial_of_nonzero_average K h2 hC c M hM R hR Sv hS (GlobalTheory.T.product_character_norm_one_trivial K h2 hC DK c n t S hA M hM g h3) h1`.
-/
theorem L_ctone : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ R : Finset (Pl →₀ ℤ), IsReps M R → ∀ Sv : Finset Pl, GoodSv M Sv →
  ∀ g : G2, th0 R Sv n t M g ≠ 0 → ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1 := by
  intro K _ _ h2 hC DK c n t S hA M hM R hR Sv hS g h
  rw [thetaZero_periodLattice_eq] at h
  have h1 := left_ne_zero_of_mul h
  have h3 := right_ne_zero_of_mul h
  exact GlobalTheory.T.local_characters_trivial_of_nonzero_average K h2 hC c M hM R hR Sv hS (GlobalTheory.T.product_character_norm_one_trivial K h2 hC DK c n t S hA M hM g h3) h1
/- English proof (translation)
Take `⟨-, S0, hS0⟩` from `hM`. Use `⟨S0.filter fun v => (M v).IsSp, fun v hv => (Finset.mem_filter.1 hv).2, fun v hv hs => ?_⟩` and prove the remaining obligations. Conclude with `hS0 v fun h => hv (Finset.mem_filter.2 ⟨h, hs⟩)`.
-/
theorem exists_goodSv (M : ∀ v : Pl, LM c v) (hM : AdmM M) : ∃ Sv, GoodSv M Sv := by
  classical
  obtain ⟨-, S0, hS0⟩ := hM
  refine ⟨S0.filter fun v => (M v).IsSp, fun v hv => (Finset.mem_filter.1 hv).2, fun v hv hs => ?_⟩
  exact hS0 v fun h => hv (Finset.mem_filter.2 ⟨h, hs⟩)

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.CenTheta.u0 GlobalTheory.CompanionTheory.CenTheta.uW`. Use `congr 1`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Establish `h` using `hct v (Ad3.R.lc v z)`. Consider the cases of `hm : M v with`.

Consider the case `sp w₁ w₂ Φ`. Rewrite `h` using `[hm]`. Establish `h1 : ((cAt c v w₁ (Ad3.R.lc v z) : ℂˣ) : ℂ) = ((cAt c v w₂ (Ad3.R.lc v z) : ℂˣ) : ℂ)`. Establish `h2 : ((cAt c v w₁ (Ad3.R.lc v z) * (cAt c v w₂ (Ad3.R.lc v z))⁻¹ : ℂˣ) : ℂ) = 1` using `h`. Establish `h3 : cAt c v w₁ (Ad3.R.lc v z) * (cAt c v w₂ (Ad3.R.lc v z))⁻¹ = 1` using `Units.ext h2`.

Rewrite using `[mul_inv_eq_one.1 h3]`. Simplify using `only [GlobalTheory.CompanionTheory.CenTheta.om0, GlobalTheory.CompanionTheory.CenTheta.omW, Units.val_mul, h1]`. Consider the case `ns w σ η Φ => rfl`.
-/
theorem centralScalar_eq_of_trivial_character (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (hct : ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1) (z : Jd) :
    GlobalTheory.CompanionTheory.CenTheta.u0 n t M z = GlobalTheory.CompanionTheory.CenTheta.uW n t M z := by
  unfold GlobalTheory.CompanionTheory.CenTheta.u0 GlobalTheory.CompanionTheory.CenTheta.uW
  congr 1
  refine finprod_congr fun v => ?_
  have h := hct v (Ad3.R.lc v z)
  cases hm : M v with
  | sp w₁ w₂ Φ =>
    rw [hm] at h
    have h1 : ((cAt c v w₁ (Ad3.R.lc v z) : ℂˣ) : ℂ) = ((cAt c v w₂ (Ad3.R.lc v z) : ℂˣ) : ℂ) := by
      have h2 : ((cAt c v w₁ (Ad3.R.lc v z) * (cAt c v w₂ (Ad3.R.lc v z))⁻¹ : ℂˣ) : ℂ) = 1 := h
      have h3 : cAt c v w₁ (Ad3.R.lc v z) * (cAt c v w₂ (Ad3.R.lc v z))⁻¹ = 1 := Units.ext h2
      rw [mul_inv_eq_one.1 h3]
    simp only [GlobalTheory.CompanionTheory.CenTheta.om0, GlobalTheory.CompanionTheory.CenTheta.omW, Units.val_mul, h1]
  | ns w σ η Φ => rfl

/- English proof (translation)
Introduce `K _ _ h2 hC DK c n t S hA M hM`. Take `⟨R, hR⟩` from `L_reps K h2 hC c M hM`. Take `⟨Sv, hS⟩` from `exists_goodSv M hM`. Take `⟨hvk1, hvkT, hvkA⟩` from `L_vk K h2 c M hM`. Establish `hst` using `L_stab K h2 hC c M hM`.

Use `⟨R, Sv, (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ), ?_, fun g hg => ⟨?_, ?_, ?_⟩, fun z => ?_⟩` and prove the remaining obligations. Establish `h1 : vK M (1 : Kˣ) = 0`. Use `hvkA 1 1` as an intermediate fact. Simplify using `using this`. Use `haveI : Nonempty {κ : K1 K // vK M (κ : Kˣ) = 0} := ⟨⟨1, h1⟩⟩`.

Conclude with `(Nat.card_pos).ne'` after adjusting the coercions. Conclude with `expansion h2 hC hA M hM R hR Sv hS g hg`. Introduce `x`. Simplify using `only [thetaZero_periodLattice_eq, L_thn K h2 c n t M hM x g]`. Introduce `κ`.

Distinguish the cases in `h0 : th0 R Sv n t M g = 0 ∧ th0 R Sv n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) = 0`. Rewrite using `[h0.1, h0.2]`. Establish `hct : ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1`. Distinguish the cases in `h1 : th0 R Sv n t M g = 0`. Conclude with `L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS _ fun h => h0 ⟨h1, h⟩`.

Conclude with `L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS _ h1`. Simplify using `only [thetaZero_periodLattice_eq, L_th0diag K h2 hC DK c n t S hA M hM hct κ g]`. Use `⟨GlobalTheory.CompanionTheory.CenTheta.uW n t M z, GlobalTheory.T.norm_global_central_scalar_eq_one K h2 c n t M hM z, fun g => GlobalTheory.T.global_whittaker_central_character K h2 c n t M hM z g, fun g _ => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.CenTheta.theta_central_character h2 n t M hM R Sv z g]`. Distinguish the cases in `h0 : th0 R Sv n t M g = 0`.

Rewrite using `[h0, mul_zero, mul_zero]`. Rewrite using `[centralScalar_eq_of_trivial_character n t M (L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS g h0) z]`.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.FourierExpansionCentral K := by
  intro K _ _ h2 hC DK c n t S hA M hM
  obtain ⟨R, hR⟩ := L_reps K h2 hC c M hM
  obtain ⟨Sv, hS⟩ := exists_goodSv M hM
  obtain ⟨hvk1, hvkT, hvkA⟩ := L_vk K h2 c M hM
  have hst := L_stab K h2 hC c M hM
  refine ⟨R, Sv, (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ), ?_, fun g hg => ⟨?_, ?_, ?_⟩, fun z => ?_⟩
  · have h1 : vK M (1 : Kˣ) = 0 := by
      have := hvkA 1 1
      simpa using this
    haveI : Nonempty {κ : K1 K // vK M (κ : Kˣ) = 0} := ⟨⟨1, h1⟩⟩
    exact_mod_cast (Nat.card_pos).ne'
  · exact expansion h2 hC hA M hM R hR Sv hS g hg
  · intro x
    simp only [thetaZero_periodLattice_eq, L_thn K h2 c n t M hM x g]
  · intro κ
    by_cases h0 : th0 R Sv n t M g = 0 ∧
        th0 R Sv n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) = 0
    · rw [h0.1, h0.2]
    · have hct : ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1 := by
        by_cases h1 : th0 R Sv n t M g = 0
        · exact L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS _ fun h => h0 ⟨h1, h⟩
        · exact L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS _ h1
      simp only [thetaZero_periodLattice_eq, L_th0diag K h2 hC DK c n t S hA M hM hct κ g]
  · refine ⟨GlobalTheory.CompanionTheory.CenTheta.uW n t M z, GlobalTheory.T.norm_global_central_scalar_eq_one K h2 c n t M hM z,
      fun g => GlobalTheory.T.global_whittaker_central_character K h2 c n t M hM z g, fun g _ => ?_⟩
    rw [GlobalTheory.CompanionTheory.CenTheta.theta_central_character h2 n t M hM R Sv z g]
    by_cases h0 : th0 R Sv n t M g = 0
    · rw [h0, mul_zero, mul_zero]
    · rw [centralScalar_eq_of_trivial_character n t M (L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS g h0) z]

end GlobalTheory.CompanionTheory.FexMain
