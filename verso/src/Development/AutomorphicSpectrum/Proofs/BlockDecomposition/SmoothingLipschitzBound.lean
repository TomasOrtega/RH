import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

open scoped Pointwise

/- English proof (translation)
Introduce `K _ _ n _ _ ν _ β hβ R`. Take `⟨L, hL0, hL⟩` from `hβ.lip`. Use `set e : ArchMatrix K n → archGroup K n := fun Y => (isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ with he`. Establish `hec : Continuous e` using `(isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _)`. Establish `hT₀ : IsCompact (tsupport β)` using `hβ.cpt`.

Use `haveI : ProperSpace (ArchMatrix K n) := FiniteDimensional.proper ℝ _`. Establish `hB : IsCompact (e '' Metric.closedBall 0 R)` using `(isCompact_closedBall 0 R).image hec`. Use `set T : Set (archGroup K n) := tsupport β ∪ (e '' Metric.closedBall 0 R) * tsupport β with hTdef`. Establish `hT : IsCompact T` using `hT₀.union (hB.mul hT₀)`. Take `⟨S, hS0, hS⟩` from `(hT.image continuous_mat).isBounded.exists_pos_norm_le`.

Establish `hne : (tsupport β).Nonempty`. Break down `Set.eq_empty_or_nonempty (tsupport β) with h0 | h0` into its components or cases. It suffices to derive a contradiction. Establish `hz : ∀ y, β y = 0` using `fun y => image_eq_zero_of_notMem_tsupport (by simp [h0])`. Use `hβ.mass` as an intermediate fact.

Simplify using `[hz] at this`. Conclude with `h0`. Use `⟨infEmb K n '' T, L * S * ν.real T, hT.image continuous_infEmb, by positivity, ?_⟩` and prove the remaining obligations. Introduce `f hf g Y M hYY hYR hM`. Take `⟨t₀, ht₀⟩` from `hne`.

Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM _ ⟨t₀, Or.inl ht₀, rfl⟩)`. Use `set h : archGroup K n → ℂ := fun y => f (g * infEmb K n y) with hh`. Establish `hhc : Continuous h` using `hf.comp (continuous_const.mul continuous_infEmb)`. Establish `hexp : mat (e Y) = 1 + Y` using `(CuspidalSpectrum.coe_expG_top Y).trans (CuspidalSpectrum.exp_eq_one_add_of_mul_self_eq_zero hYY)`. Establish `hmul : ∀ a b : archGroup K n, mat (a * b) = mat a * mat b` using `fun _ _ => rfl`.

Establish `hinv : mat (e Y)⁻¹ = 1 - Y`. Establish `h1 : mat (e Y) * (1 - Y) = 1`. Establish `: (1 + Y) * (1 - Y) = 1 - Y * Y` using `by noncomm_ring`. Rewrite using `[hexp, this, hYY, sub_zero]`. Establish `h2 : mat (e Y)⁻¹ * mat (e Y) = 1`.

Rewrite using `[← hmul, inv_mul_cancel]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Establish `hz2 : ∀ u, u ∉ T → β u = 0` using `fun u hu => image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inl hc)`. Establish `hz1 : ∀ u, u ∉ T → β ((e Y)⁻¹ * u) = 0` using `fun u hu => image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inr ⟨e Y, ⟨Y, by simpa using hYR, rfl⟩, _, hc, by simp⟩)`.

Use `set F₁ : archGroup K n → ℂ := fun u => (β ((e Y)⁻¹ * u) : ℂ) * h u with hF₁`. Use `set F₂ : archGroup K n → ℂ := fun u => (β u : ℂ) * h u with hF₂`. Establish `hF₁c : Continuous F₁` using `(Complex.continuous_ofReal.comp (hβ.cont.comp (continuous_const.mul continuous_id))).mul hhc`. Establish `hF₂c : Continuous F₂` using `(Complex.continuous_ofReal.comp hβ.cont).mul hhc`. Establish `hF₁z : ∀ u, u ∉ T → F₁ u = 0` using `fun u hu => by simp [hF₁, hz1 u hu]`.

Establish `hF₂z : ∀ u, u ∉ T → F₂ u = 0` using `fun u hu => by simp [hF₂, hz2 u hu]`. Establish `hF₁i : Integrable F₁ ν` using `hF₁c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₁z)`. Establish `hF₂i : Integrable F₂ ν` using `hF₂c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₂z)`. Establish `hsm1 : sm ν β f (g * CuspidalSpectrum.archExp Y) = ∫ u, F₁ u ∂ν`. Rewrite using `[← integral_mul_left_eq_self (μ := ν) F₁ (e Y)]`.

Unfold `sm`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [hF₁, hh, inv_mul_cancel_left, map_mul]`. Rewrite using `[CuspidalSpectrum.archExp, mul_assoc]`. Establish `hsm2 : sm ν β f g = ∫ u, F₂ u ∂ν` using `rfl`.

Rewrite using `[hsm1, hsm2, ← integral_sub hF₁i hF₂i, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T) (fun u hu => by rw [hF₁z u hu, hF₂z u hu, sub_zero])]`. Establish `hpt : ∀ u ∈ T, ‖F₁ u - F₂ u‖ ≤ L * S * ‖Y‖ * M`. Introduce `u hu`. Establish `hd : F₁ u - F₂ u = ((β ((e Y)⁻¹ * u) - β u : ℝ) : ℂ) * h u`. Simplify using `only [hF₁, hF₂]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hm : mat ((e Y)⁻¹ * u) - mat u = -(Y * mat u)`. Rewrite using `[hmul, hinv]`. Use `noncomm_ring`.

Establish `h1 : |β ((e Y)⁻¹ * u) - β u| ≤ L * (‖Y‖ * S)`. Use `(hL _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)` and prove the remaining obligations. Rewrite using `[hm, norm_neg]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hS _ ⟨u, hu, rfl⟩) (norm_nonneg _))`. Establish `h2 : ‖h u‖ ≤ M` using `hM _ ⟨u, hu, rfl⟩`.

Rewrite using `[hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation. Use `norm_setIntegral_le_of_norm_le_const (μ := ν) (s := T) hT.measure_lt_top hpt` as an intermediate fact. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sm_lip_of_sq_zero : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  intro K _ _ n _ _ ν _ β hβ R
  obtain ⟨L, hL0, hL⟩ := hβ.lip
  set e : ArchMatrix K n → archGroup K n :=
    fun Y => (isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ with he
  have hec : Continuous e :=
    (isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _)
  have hT₀ : IsCompact (tsupport β) := hβ.cpt
  haveI : ProperSpace (ArchMatrix K n) := FiniteDimensional.proper ℝ _
  have hB : IsCompact (e '' Metric.closedBall 0 R) := (isCompact_closedBall 0 R).image hec
  set T : Set (archGroup K n) := tsupport β ∪ (e '' Metric.closedBall 0 R) * tsupport β with hTdef
  have hT : IsCompact T := hT₀.union (hB.mul hT₀)
  obtain ⟨S, hS0, hS⟩ := (hT.image continuous_mat).isBounded.exists_pos_norm_le
  have hne : (tsupport β).Nonempty := by
    rcases Set.eq_empty_or_nonempty (tsupport β) with h0 | h0
    · exfalso
      have hz : ∀ y, β y = 0 := fun y => image_eq_zero_of_notMem_tsupport (by simp [h0])
      have := hβ.mass
      simp [hz] at this
    · exact h0
  refine ⟨infEmb K n '' T, L * S * ν.real T, hT.image continuous_infEmb, by positivity, ?_⟩
  intro f hf g Y M hYY hYR hM
  obtain ⟨t₀, ht₀⟩ := hne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨t₀, Or.inl ht₀, rfl⟩)
  set h : archGroup K n → ℂ := fun y => f (g * infEmb K n y) with hh
  have hhc : Continuous h := hf.comp (continuous_const.mul continuous_infEmb)

  have hexp : mat (e Y) = 1 + Y :=
    (CuspidalSpectrum.coe_expG_top Y).trans (CuspidalSpectrum.exp_eq_one_add_of_mul_self_eq_zero hYY)
  have hmul : ∀ a b : archGroup K n, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have hinv : mat (e Y)⁻¹ = 1 - Y := by
    have h1 : mat (e Y) * (1 - Y) = 1 := by
      have : (1 + Y) * (1 - Y) = 1 - Y * Y := by noncomm_ring
      rw [hexp, this, hYY, sub_zero]
    have h2 : mat (e Y)⁻¹ * mat (e Y) = 1 := by
      rw [← hmul, inv_mul_cancel]; rfl
    calc mat (e Y)⁻¹ = mat (e Y)⁻¹ * (mat (e Y) * (1 - Y)) := by rw [h1, mul_one]
      _ = 1 - Y := by rw [← mul_assoc, h2, one_mul]

  have hz2 : ∀ u, u ∉ T → β u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inl hc)
  have hz1 : ∀ u, u ∉ T → β ((e Y)⁻¹ * u) = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inr
      ⟨e Y, ⟨Y, by simpa using hYR, rfl⟩, _, hc, by simp⟩)
  set F₁ : archGroup K n → ℂ := fun u => (β ((e Y)⁻¹ * u) : ℂ) * h u with hF₁
  set F₂ : archGroup K n → ℂ := fun u => (β u : ℂ) * h u with hF₂
  have hF₁c : Continuous F₁ :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp (continuous_const.mul continuous_id))).mul hhc
  have hF₂c : Continuous F₂ := (Complex.continuous_ofReal.comp hβ.cont).mul hhc
  have hF₁z : ∀ u, u ∉ T → F₁ u = 0 := fun u hu => by simp [hF₁, hz1 u hu]
  have hF₂z : ∀ u, u ∉ T → F₂ u = 0 := fun u hu => by simp [hF₂, hz2 u hu]
  have hF₁i : Integrable F₁ ν :=
    hF₁c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₁z)
  have hF₂i : Integrable F₂ ν :=
    hF₂c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₂z)
  have hsm1 : sm ν β f (g * CuspidalSpectrum.archExp Y) = ∫ u, F₁ u ∂ν := by
    rw [← integral_mul_left_eq_self (μ := ν) F₁ (e Y)]
    unfold sm
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF₁, hh, inv_mul_cancel_left, map_mul]
    rw [CuspidalSpectrum.archExp, mul_assoc]
  have hsm2 : sm ν β f g = ∫ u, F₂ u ∂ν := rfl
  rw [hsm1, hsm2, ← integral_sub hF₁i hF₂i,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T)
      (fun u hu => by rw [hF₁z u hu, hF₂z u hu, sub_zero])]
  have hpt : ∀ u ∈ T, ‖F₁ u - F₂ u‖ ≤ L * S * ‖Y‖ * M := by
    intro u hu
    have hd : F₁ u - F₂ u = ((β ((e Y)⁻¹ * u) - β u : ℝ) : ℂ) * h u := by
      simp only [hF₁, hF₂]; push_cast; ring
    have hm : mat ((e Y)⁻¹ * u) - mat u = -(Y * mat u) := by
      rw [hmul, hinv]; noncomm_ring
    have h1 : |β ((e Y)⁻¹ * u) - β u| ≤ L * (‖Y‖ * S) := by
      refine (hL _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      rw [hm, norm_neg]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hS _ ⟨u, hu, rfl⟩) (norm_nonneg _))
    have h2 : ‖h u‖ ≤ M := hM _ ⟨u, hu, rfl⟩
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |β ((e Y)⁻¹ * u) - β u| * ‖h u‖ ≤ (L * (‖Y‖ * S)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = L * S * ‖Y‖ * M := by ring
  have := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := T) hT.measure_lt_top hpt
  refine this.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.Conc
