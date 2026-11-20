import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

/- English proof (translation)
Use `set Z' := toMeasurable μ Z with hZ'`. Establish `hm : MeasurableSet Z'` using `measurableSet_toMeasurable μ Z`. Establish `h0 : μ Z' = 0` using `by rw [hZ', measure_toMeasurable]; exact hZ`. Use `set S : Set (G × G) := (fun p : G × G => p.2 * p.1) ⁻¹' Z' with hS`. Establish `hSm : MeasurableSet S` using `(measurable_snd.mul measurable_fst) hm`.

Establish `hS0 : (μ.prod ν) S = 0`. Rewrite using `[Measure.prod_apply_symm hSm]`. Establish `: ∀ y : G, μ ((fun x => (x, y)) ⁻¹' S) = 0` using `fun y => by`. Establish `: (fun x => (x, y)) ⁻¹' S = (fun x => y * x) ⁻¹' Z'` using `rfl`. Rewrite using `[this, measure_preimage_mul]`.

Conclude with `h0`. Simplify using `[this]`. Establish `hae : ∀ᵐ p ∂μ.prod ν, p ∉ S` using `compl_mem_ae_iff.2 (by simpa using hS0)`. Use `filter_upwards [Measure.ae_ae_of_ae_prod hae] with x hx`. Use `filter_upwards [hx] with m hmx hmem`.

Conclude with `hmx (subset_toMeasurable μ Z hmem)`.
-/
theorem rr_ae_ae_mul {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] {Z : Set G} (hZ : μ Z = 0) : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z := by
  set Z' := toMeasurable μ Z with hZ'
  have hm : MeasurableSet Z' := measurableSet_toMeasurable μ Z
  have h0 : μ Z' = 0 := by rw [hZ', measure_toMeasurable]; exact hZ
  set S : Set (G × G) := (fun p : G × G => p.2 * p.1) ⁻¹' Z' with hS
  have hSm : MeasurableSet S := (measurable_snd.mul measurable_fst) hm
  have hS0 : (μ.prod ν) S = 0 := by
    rw [Measure.prod_apply_symm hSm]
    have : ∀ y : G, μ ((fun x => (x, y)) ⁻¹' S) = 0 := fun y => by
      have : (fun x => (x, y)) ⁻¹' S = (fun x => y * x) ⁻¹' Z' := rfl
      rw [this, measure_preimage_mul]; exact h0
    simp [this]
  have hae : ∀ᵐ p ∂μ.prod ν, p ∉ S := compl_mem_ae_iff.2 (by simpa using hS0)
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with x hx
  filter_upwards [hx] with m hmx hmem
  exact hmx (subset_toMeasurable μ Z hmem)

/- English proof (translation)
Use `Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hp) y` as an intermediate fact. Rewrite `this` using `[h1]`. Simplify using `using this`.
-/
theorem rr_e_zero (X : CData) (hp : X.I.IsPosType X.e) (h1 : X.e 1 = 0) (y : X.I.Gf) : X.e y = 0 := by
  have := Formalism.HermitianLatticeCounting.Final.S7.posTypeBound X.I.Gf X.e (positive_type_notation_eq X.I hp) y
  rw [h1] at this
  simpa using this

/- English proof (translation)
Use `ContinuousLinearMap.ext fun y => ?_` and prove the remaining obligations. Establish `h : ∀ x, ⟪x, T y⟫_ℂ = 0` using `fun x => by`. Rewrite using `[hT.2 x y]`. Simplify using `[CData.φ, phe, he]`. Conclude with `inner_self_eq_zero.1 (h _)`.
-/
theorem rr_T_zero (X : CData) (he : ∀ y, X.e y = 0) (T : X.L2 →L[ℂ] X.L2) (hT : X.IsOp T) : T = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  have h : ∀ x, ⟪x, T y⟫_ℂ = 0 := fun x => by
    rw [hT.2 x y]
    simp [CData.φ, phe, he]
  exact inner_self_eq_zero.1 (h _)

/- English proof (translation)
Use `ContinuousLinearMap.ext fun y => ?_` and prove the remaining obligations. Establish `h : ∀ x, ⟪x, X.Re y⟫_ℂ = 0` using `fun x => by`. Rewrite using `[hRe.2 x y]`. Simplify using `[he]`. Conclude with `inner_self_eq_zero.1 (h _)`.
-/
theorem rr_Re_zero (X : CData) (he : ∀ y, X.e y = 0) (hRe : X.I.IsRConvF X.μf X.fund X.R X.e X.Re) : X.Re = 0 := by
  refine ContinuousLinearMap.ext fun y => ?_
  have h : ∀ x, ⟪x, X.Re y⟫_ℂ = 0 := fun x => by
    rw [hRe.2 x y]
    simp [he]
  exact inner_self_eq_zero.1 (h _)

/- English proof (translation)
Take `⟨hH, hF, -⟩` from `hd`. Use `hH` as an intermediate fact. Establish `: (X.I.muA X.μf).IsMulLeftInvariant` using `rr_muA_left X.I X.μf`. Establish `hfd` using `rr_FD_of X.I X.μf X.fund hF`. Use `set Z₀ : Set X.I.GA := {t | (Fv : X.I.GA → ℂ) t ≠ 0} with hZ₀`.

Establish `hz : (X.I.muA X.μf) (Z₀ ∩ X.fund) = 0`. Rewrite using `[← Measure.restrict_apply' hF.1]`. Conclude with `h0`. Establish `hsub : {y | X.I.ext Fv y ≠ 0} ⊆ ⋃ γ : rr_GF X.I, (fun y => (γ : X.I.GA) * y) ⁻¹' (Z₀ ∩ X.fund)`. Introduce `y hy`.

Take `⟨γ, h1, h2, h3⟩` from `rr_rep_spec hfd y`. Use `mem_iUnion.2 ⟨⟨γ, h1⟩, ?_, h3⟩` and prove the remaining obligations. Use `show (Fv : X.I.GA → ℂ) (γ * y) ≠ 0`. Rewrite using `[← h2]`. Conclude with `hy`.

Use `measure_mono_null hsub ?_` and prove the remaining obligations. Rewrite using `[measure_iUnion_null_iff]`. Introduce `γ`. Rewrite using `[measure_preimage_mul]`. Conclude with `hz`.
-/
theorem rr_ext_null (X : CData) (hd : RegData X) (Fv : X.L2) (h0 : (Fv : X.I.GA → ℂ) =ᵐ[X.μ] 0) :
    (X.I.muA X.μf) {y | X.I.ext Fv y ≠ 0} = 0 := by
  obtain ⟨hH, hF, -⟩ := hd
  have := hH
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  set Z₀ : Set X.I.GA := {t | (Fv : X.I.GA → ℂ) t ≠ 0} with hZ₀
  have hz : (X.I.muA X.μf) (Z₀ ∩ X.fund) = 0 := by
    rw [← Measure.restrict_apply' hF.1]
    exact h0
  have hsub : {y | X.I.ext Fv y ≠ 0} ⊆ ⋃ γ : rr_GF X.I, (fun y => (γ : X.I.GA) * y) ⁻¹' (Z₀ ∩ X.fund) := by
    intro y hy
    obtain ⟨γ, h1, h2, h3⟩ := rr_rep_spec hfd y
    refine mem_iUnion.2 ⟨⟨γ, h1⟩, ?_, h3⟩
    show (Fv : X.I.GA → ℂ) (γ * y) ≠ 0
    rw [← h2]
    exact hy
  refine measure_mono_null hsub ?_
  rw [measure_iUnion_null_iff]; intro γ
  rw [measure_preimage_mul]; exact hz

/- English proof (translation)
Introduce `W _ ν hν`. Establish `hz` using `rr_ext_null X hd Fv h0`. Take `⟨hH, -, -⟩` from `hd`. Use `hH` as an intermediate fact. Establish `: SecondCountableTopology X.I.Gf` using `rr_secondCountable X.I X.μf`.

Establish `: (X.I.muA X.μf).IsMulLeftInvariant` using `rr_muA_left X.I X.μf`. Establish `: SigmaFinite (X.I.muA X.μf)` using `rr_muA_sigmaFinite X.I X.μf`. Establish `: IsFiniteMeasure ν` using `hν.1`. Use `filter_upwards [rr_ae_ae_mul (X.I.muA X.μf) ν hz] with x hx`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hx] with m hm`. Assume the negation of the conclusion as `hne`. Conclude with `hm hne`.
-/
theorem rr_cusp_of_null (X : CData) (hd : RegData X) (Fv : X.L2) (h0 : (Fv : X.I.GA → ℂ) =ᵐ[X.μ] 0) :
    X.I.IsCuspFn (X.I.muA X.μf) (X.I.ext Fv) := by
  intro W _ ν hν
  have hz := rr_ext_null X hd Fv h0
  obtain ⟨hH, -, -⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : IsFiniteMeasure ν := hν.1
  filter_upwards [rr_ae_ae_mul (X.I.muA X.μf) ν hz] with x hx
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hx] with m hm
  by_contra hne
  exact hm hne

/- English proof (translation)
Establish `he` using `rr_e_zero X hX.1.2.2.2.2.2.2.1.2.2.2.1 h1`. Establish `hRe` using `rr_Re_zero X he hX.2.1.2.2.2.2.2.2`. Use `⟨fun T hT => ?_, fun T hT _ => ?_, fun T hT _ Fv hFv => ?_⟩` and prove the remaining obligations. Rewrite using `[rr_T_zero X he T hT]`. Conclude with `IsStarProjection.zero _`.

Establish `hT0` using `rr_T_zero X he T hT`. Establish `hΦ : ∀ Φ : X.I.eHom X.σs X.μf X.fund X.R X.Re, (Φ : X.Hs →L[ℂ] X.L2) = 0`. Introduce and unpack `⟨Φ, hΦ⟩`. Take `⟨S, -, rfl⟩` from `Submodule.mem_map.1 hΦ`. Simplify using `[hRe]`.

Establish `hr : ∀ v : X.rg T, (v : X.L2) = 0`. Introduce and unpack `⟨_, y, rfl⟩`. Simplify using `[hT0]`. Establish `s1 : Subsingleton (X.I.eHom X.σs X.μf X.fund X.R X.Re)` using `⟨fun a b => Subtype.ext (by rw [hΦ a, hΦ b])⟩`. Establish `s2 : Subsingleton (X.rg T)` using `⟨fun a b => Subtype.ext (by rw [hr a, hr b])⟩`.

Use `⟨0, fun Φ => ?_⟩` and prove the remaining obligations. Rewrite using `[hr, hΦ]`. Simplify using the standard rewrite rules. Establish `hT0` using `rr_T_zero X he T hT`. Take `⟨y, rfl⟩` from `hFv`.

Establish `: ((T : X.L2 →ₗ[ℂ] X.L2) y) = 0` using `by simp [hT0]`. Rewrite using `[this]`. Conclude with `rr_cusp_of_null X (RegData_of_HypB X hX) 0 (Lp.coeFn_zero _ _ _)`.
-/
theorem projection_count_cusp_of_trivial_idempotent (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.e 1 = 0) :
    X.ProjStep ∧ X.CountedStep ∧ X.CuspStep := by
  have he := rr_e_zero X hX.1.2.2.2.2.2.2.1.2.2.2.1 h1
  have hRe := rr_Re_zero X he hX.2.1.2.2.2.2.2.2
  refine ⟨fun T hT => ?_, fun T hT _ => ?_, fun T hT _ Fv hFv => ?_⟩
  · rw [rr_T_zero X he T hT]
    exact IsStarProjection.zero _
  · have hT0 := rr_T_zero X he T hT
    have hΦ : ∀ Φ : X.I.eHom X.σs X.μf X.fund X.R X.Re, (Φ : X.Hs →L[ℂ] X.L2) = 0 := by
      rintro ⟨Φ, hΦ⟩
      obtain ⟨S, -, rfl⟩ := Submodule.mem_map.1 hΦ
      simp [hRe]
    have hr : ∀ v : X.rg T, (v : X.L2) = 0 := by
      rintro ⟨_, y, rfl⟩
      simp [hT0]
    have s1 : Subsingleton (X.I.eHom X.σs X.μf X.fund X.R X.Re) :=
      ⟨fun a b => Subtype.ext (by rw [hΦ a, hΦ b])⟩
    have s2 : Subsingleton (X.rg T) := ⟨fun a b => Subtype.ext (by rw [hr a, hr b])⟩
    refine ⟨0, fun Φ => ?_⟩
    rw [hr, hΦ]
    simp
  · have hT0 := rr_T_zero X he T hT
    obtain ⟨y, rfl⟩ := hFv
    have : ((T : X.L2 →ₗ[ℂ] X.L2) y) = 0 := by simp [hT0]
    rw [this]
    exact rr_cusp_of_null X (RegData_of_HypB X hX) 0 (Lp.coeFn_zero _ _ _)

end Formalism.MainNotions.LeviCoordinates

end
