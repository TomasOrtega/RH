import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldCoefficientNormOneTwistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionUnitRotationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaGlobalCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormEqualsComplexAbsSqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta.TermZero

/- English proof (translation)
Consider the cases of `L with`. Consider the case `ns w σ η Φ => exact hsp.elim`. Consider the case `sp w₁ w₂ Φ`. Take `⟨hne, -, -⟩` from `hok`. Take `⟨a1, a2, aN⟩` from `GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne`.

Establish `hN : Algebra.norm ℚ (κ : K) = 1`. Use `congrArg Units.val (MonoidHom.mem_ker.mp hκ)` as an intermediate fact. Simplify using `using this`. Establish `hk : dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) = 1`. Rewrite using `[aN, hN]`.

Simplify using the standard rewrite rules. Establish `h0 : dg1 v w₁ (κ : K) ≠ 0` using `left_ne_zero_of_mul_eq_one hk`. Use `set u : (Qv v)ˣ := Units.mk0 _ h0 with hu`. Establish `hk1 : k1 (LM.sp w₁ w₂ Φ : LM c v) κ = u`. Establish `: e1 (LM.sp w₁ w₂ Φ : LM c v) (κ : K) = dg1 v w₁ (κ : K)` using `rfl`.

Unfold `k1`. Rewrite using `[dif_neg (by rw [this]; exact h0)]`. Conclude with `Units.ext rfl`. Establish `hu2 : ((u⁻¹ : (Qv v)ˣ) : Qv v) = dg1 v w₂ (κ : K)`. Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises.

Conclude with `hk`. Establish `c1 : cK c w₁ κ = ((cAt c v w₁ u : ℂˣ) : ℂ)`. Establish `: atW w₁ κ = Units.map (algebraMap (Qv v) (Kv K w₁)).toMonoidHom u`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(a1 (κ : K)).symm`.

Simplify using `only [cK, cAt, MonoidHom.comp_apply, this]`. Establish `c2 : cK c w₂ κ = ((cAt c v w₂ u⁻¹ : ℂˣ) : ℂ)`. Establish `: atW w₂ κ = Units.map (algebraMap (Qv v) (Kv K w₂)).toMonoidHom u⁻¹`. Apply `Units.ext` to reduce the goal to its premises. Use `show algebraMap K (Kv K w₂) (κ : K) = algebraMap (Qv v) (Kv K w₂) ((u⁻¹ : (Qv v)ˣ) : Qv v)`.

Rewrite using `[hu2, a2]`. Simplify using `only [cK, cAt, MonoidHom.comp_apply, this]`. Rewrite using `[hk1]`. Simplify using `only [LM.ct, cW, c1, c2, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]`.
-/
theorem character_norm_one_split_datum {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (L : LM c v) (hok : L.ok) (hsp : L.IsSp) (κ : Kˣ) (hκ : κ ∈ K1 K) :
    L.ct (k1 L κ) = cW L κ := by
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | sp w₁ w₂ Φ =>
    obtain ⟨hne, -, -⟩ := hok
    obtain ⟨a1, a2, aN⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hN : Algebra.norm ℚ (κ : K) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hκ)
      simpa using this
    have hk : dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) = 1 := by
      rw [aN, hN]; simp
    have h0 : dg1 v w₁ (κ : K) ≠ 0 := left_ne_zero_of_mul_eq_one hk
    set u : (Qv v)ˣ := Units.mk0 _ h0 with hu
    have hk1 : k1 (LM.sp w₁ w₂ Φ : LM c v) κ = u := by
      have : e1 (LM.sp w₁ w₂ Φ : LM c v) (κ : K) = dg1 v w₁ (κ : K) := rfl
      unfold k1
      rw [dif_neg (by rw [this]; exact h0)]
      exact Units.ext rfl
    have hu2 : ((u⁻¹ : (Qv v)ˣ) : Qv v) = dg1 v w₂ (κ : K) := by
      apply Units.inv_eq_of_mul_eq_one_right
      exact hk
    have c1 : cK c w₁ κ = ((cAt c v w₁ u : ℂˣ) : ℂ) := by
      have : atW w₁ κ = Units.map (algebraMap (Qv v) (Kv K w₁)).toMonoidHom u := by
        apply Units.ext
        exact (a1 (κ : K)).symm
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    have c2 : cK c w₂ κ = ((cAt c v w₂ u⁻¹ : ℂˣ) : ℂ) := by
      have : atW w₂ κ = Units.map (algebraMap (Qv v) (Kv K w₂)).toMonoidHom u⁻¹ := by
        apply Units.ext
        show algebraMap K (Kv K w₂) (κ : K) = algebraMap (Qv v) (Kv K w₂) ((u⁻¹ : (Qv v)ˣ) : Qv v)
        rw [hu2, a2]
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    rw [hk1]
    simp only [LM.ct, cW, c1, c2, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]

/- English proof (translation)
Establish `h` using `GlobalTheory.T.field_coefficient_norm_one_twist K h2 c v L hok hns g 0 κ hκ 1`. Consider the cases of `L with`. Consider the case `sp w₁ w₂ Φ => exact absurd trivial hns`. Consider the case `ns w σ η Φ`. Simplify using `only [fL, LM.ct, LM.tw, one_mul, zero_mul] at h`.

Establish `h1 : cW (LM.ns w σ η Φ : LM c v) κ = 1` using `mul_left_cancel₀ h0 (by rw [h, mul_one])`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem character_norm_one_field_datum {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {c : HeckeCharacter K} {v : Pl} (L : LM c v) (hok : L.ok) (hns : ¬ L.IsSp)
    (g : GL (Fin 2) (Qv v)) (h0 : L.val g 0 ≠ 0) (κ : Kˣ) (hκ : κ ∈ K1 K) :
    L.ct (k1 L κ) = cW L κ := by
  have h := GlobalTheory.T.field_coefficient_norm_one_twist K h2 c v L hok hns g 0 κ hκ 1
  cases L with
  | sp w₁ w₂ Φ => exact absurd trivial hns
  | ns w σ η Φ =>
    simp only [fL, LM.ct, LM.tw, one_mul, zero_mul] at h
    have h1 : cW (LM.ns w σ η Φ : LM c v) κ = 1 :=
      mul_left_cancel₀ h0 (by rw [h, mul_one])
    rw [h1]
    rfl

/- English proof (translation)
Introduce `K _ _ h2 hcx DK c n t S hA M hM g hg κ hκ`. Take `⟨hok, S0, hS0⟩` from `hM`. Take `⟨S1, hS1⟩` from `GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g`. Establish `hB : (Function.mulSupport fun v => (M v).val (finAt v g) 0).Finite` using `(S0 ∪ S1).finite_toSet.subset fun v hv => by`. Assume the negation of the conclusion as `hn`.

Establish `hv' : v ∉ S0 ∧ v ∉ S1` using `by simpa using hn`. Take `⟨hU, hs⟩` from `hS0 v hv'.1`. Conclude with `hv (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) hU (hok v) hs _ (hS1 v hv'.2)).2`. Simplify using `only [thT] at hg`. Establish `hr` using `left_ne_zero_of_mul hg`.

Establish `hp` using `right_ne_zero_of_mul hg`. Establish `hfac : ∀ v, (M v).val (finAt v g) 0 ≠ 0` using `fun v hz => hp (finprod_eq_zero _ v hz hB)`. Establish `hct : ∀ v, (M v).ct (k1 (M v) κ) = cW (M v) κ`. Introduce `v`. Distinguish the cases in `hs : (M v).IsSp`.

Conclude with `character_norm_one_split_datum h2 (M v) (hok v) hs κ hκ`. Conclude with `character_norm_one_field_datum h2 (M v) (hok v) hs _ (hfac v) κ hκ`. Rewrite using `[finprod_congr hct]`. Take `⟨-, hprod⟩` from `GlobalTheory.T.product_formula_global_character K h2 hcx DK c n t S hA M hok κ`. Establish `hu : ‖((embU κ : ℂˣ) : ℂ)‖ = 1`.

Establish `h` using `(GlobalTheory.T.norm_equals_complex_abs_sq K h2 hcx κ).1`. Establish `hN : Units.map (Algebra.norm ℚ : K →* ℚ) κ = 1` using `MonoidHom.mem_ker.mp hκ`. Rewrite `h` using `[hN]`. Establish `h' : ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 = 1` using `by simpa using h.symm`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h'`.

Establish `hn : ((embU κ : ℂˣ) : ℂ) ^ (-n) = 1`. Establish `h` using `GlobalTheory.T.real_weil_action_unit_rotation n t (GL2Classical.realPart g) 0 ((embU κ : ℂˣ) : ℂ) hu`. Establish `e0 : embC K (0 : K) = 0` using `map_zero _`. Rewrite `hr` using `[e0]`. Rewrite `h` using `[zero_mul]`.

Conclude with `mul_right_cancel₀ hr (by rw [one_mul]; exact h.symm)`. Establish `hn' : ((embU κ : ℂˣ) : ℂ) ^ n = 1`. Rewrite `hn` using `[zpow_neg]`. Conclude with `inv_eq_one.mp hn`. Establish `hchi : chC n (Complex.I * t) (embU κ) = 1`.

Simplify using `only [chC]`. Rewrite using `[hu]`. Simplify using `[hn']`. Rewrite `hprod` using `[hchi, mul_one]`. Conclude with `hprod`.
-/
theorem finprod_character_norm_one_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ g : G2, thT n t M g 0 ≠ 0 → ∀ κ ∈ K1 K, ∏ᶠ v, (M v).ct (k1 (M v) κ) = 1 := by
  intro K _ _ h2 hcx DK c n t S hA M hM g hg κ hκ
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
  classical
  have hB : (Function.mulSupport fun v => (M v).val (finAt v g) 0).Finite :=
    (S0 ∪ S1).finite_toSet.subset fun v hv => by
      by_contra hn
      have hv' : v ∉ S0 ∧ v ∉ S1 := by simpa using hn
      obtain ⟨hU, hs⟩ := hS0 v hv'.1
      exact hv (GlobalTheory.T.unramified_standard_values_at_integral K h2 c v (M v) hU (hok v) hs _ (hS1 v hv'.2)).2
  simp only [thT] at hg
  have hr := left_ne_zero_of_mul hg
  have hp := right_ne_zero_of_mul hg
  have hfac : ∀ v, (M v).val (finAt v g) 0 ≠ 0 := fun v hz =>
    hp (finprod_eq_zero _ v hz hB)
  have hct : ∀ v, (M v).ct (k1 (M v) κ) = cW (M v) κ := by
    intro v
    by_cases hs : (M v).IsSp
    · exact character_norm_one_split_datum h2 (M v) (hok v) hs κ hκ
    · exact character_norm_one_field_datum h2 (M v) (hok v) hs _ (hfac v) κ hκ
  rw [finprod_congr hct]
  obtain ⟨-, hprod⟩ := GlobalTheory.T.product_formula_global_character K h2 hcx DK c n t S hA M hok κ
  have hu : ‖((embU κ : ℂˣ) : ℂ)‖ = 1 := by
    have h := (GlobalTheory.T.norm_equals_complex_abs_sq K h2 hcx κ).1
    have hN : Units.map (Algebra.norm ℚ : K →* ℚ) κ = 1 := MonoidHom.mem_ker.mp hκ
    rw [hN] at h
    have h' : ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 = 1 := by simpa using h.symm
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h'
  have hn : ((embU κ : ℂˣ) : ℂ) ^ (-n) = 1 := by
    have h := GlobalTheory.T.real_weil_action_unit_rotation n t (GL2Classical.realPart g) 0 ((embU κ : ℂˣ) : ℂ) hu
    have e0 : embC K (0 : K) = 0 := map_zero _
    rw [e0] at hr
    rw [zero_mul] at h
    exact mul_right_cancel₀ hr (by rw [one_mul]; exact h.symm)
  have hn' : ((embU κ : ℂˣ) : ℂ) ^ n = 1 := by
    rw [zpow_neg] at hn
    exact inv_eq_one.mp hn
  have hchi : chC n (Complex.I * t) (embU κ) = 1 := by
    simp only [chC]
    rw [hu]
    simp [hn']
  rw [hchi, mul_one] at hprod
  exact hprod

end GlobalTheory.CompanionTheory.FexTheta.TermZero
