import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HaarPushforwardEqBallDensityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Orbit

variable {G X : Type} [Group G] (p : G → X)

def trivPart (Γ₀ : Subgroup G) : Set Γ₀ := {γ | ∀ a, p ((γ : G) * a) = p a}

/- English proof (translation)
Use `set H : Subgroup Γ₀ := Γ₁.subgroupOf Γ₀ with hH`. Establish `hHidx : H.index ≠ 0` using `hidx`. Use `haveI : H.FiniteIndex := ⟨hHidx⟩`. Use `haveI : Finite (Γ₀ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex`. Use `haveI : Finite (trivPart p Γ₀) := hfin`.

Use `set Z := {z : Γ₀ // z ∈ trivPart p Γ₀ ∧ (z : G) ∈ Γ₁} with hZ`. Use `haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : trivPart p Γ₀)) (fun x y h => Subtype.ext (congrArg (fun w : trivPart p Γ₀ => w.1) h))`. Establish `memH : ∀ u : Γ₀, u ∈ H ↔ (u : G) ∈ Γ₁` using `fun u => Subgroup.mem_subgroupOf`. Establish `hex : ∀ q : Γ₀ ⧸ H, ∃ g : Γ₀, (g : G) * a ∈ S ∧ (QuotientGroup.mk g⁻¹ : Γ₀ ⧸ H) = q`. Introduce `q`.

Take `⟨d, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨γ, hγ, hmem⟩` from `hcov (((d⁻¹ : Γ₀) : G) * a)`. Use `⟨⟨γ, hle hγ⟩ * d⁻¹, by simpa [mul_assoc] using hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.eq, inv_inv, inv_mul_cancel_right, memH]`. Conclude with `hγ`.

Use `choose g hgS hgq using hex`. Establish `hmaps : ∀ x : (Γ₀ ⧸ H) × Z, (((x.2.1 * g x.1 : Γ₀) : G) * a) ∈ S`. Introduce and unpack `⟨q, z⟩`. Establish `h1` using `z.2.1 ((g q : G) * a)`. Use `hsat _ _ h1.symm (hgS q) |> fun h => ?_` and prove the remaining obligations.

Simplify `h` using `[mul_assoc]`. Set `Φ : (Γ₀ ⧸ H) × Z → {γ : Γ₀ | (γ : G) * a ∈ S}` to `fun x => ⟨x.2.1 * g x.1, hmaps x⟩`. Establish `hbij : Function.Bijective Φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, z⟩ ⟨q', z'⟩ h`.

Establish `h0 : z.1 * g q = z'.1 * g q'` using `congrArg Subtype.val h`. Establish `hq : q = q'`. Rewrite using `[← hgq q, ← hgq q', QuotientGroup.eq, inv_inv, memH]`. Establish `e : g q * (g q')⁻¹ = z.1⁻¹ * z'.1`. Rewrite using `[eq_inv_mul_iff_mul_eq, ← mul_assoc, h0, mul_inv_cancel_right]`.

Rewrite using `[e]`. Conclude with `Γ₁.mul_mem (Γ₁.inv_mem z.2.2) z'.2.2`. Substitute `hq` using the available equality. Establish `hz : z.1 = z'.1` using `mul_right_cancel h0`. Conclude with `Prod.ext rfl (Subtype.ext hz)`.

Introduce and unpack `⟨γ, hγ⟩ set q : Γ₀ ⧸ H := QuotientGroup.mk γ⁻¹ with hq`. Establish `h1 : g q * γ⁻¹ ∈ H`. Use `hgq q` as an intermediate fact. Rewrite `this` using `[hq, QuotientGroup.eq, inv_inv]`. Conclude with `this`.

Establish `hu : γ * (g q)⁻¹ ∈ H`. Use `H.inv_mem h1` as an intermediate fact. Simplify using `using this`. Establish `hu' : ((γ * (g q)⁻¹ : Γ₀) : G) ∈ Γ₁` using `(memH _).1 hu`. Establish `h2` using `hsep _ (hgS q) _ hu' (by simpa [mul_assoc] using hγ)`.

Establish `h3 : p ((γ : G) * a) = p ((g q : G) * a)` using `by simpa [mul_assoc] using h2`. Establish `h4` using `hact ((g q : G)⁻¹) _ _ h3`. Establish `h5 : p ((((g q)⁻¹ * γ : Γ₀) : G) * a) = p a`. Simplify `h4` using `[mul_assoc]`. Establish `hw` using `hgood _ h5`.

Establish `htriv : (γ * (g q)⁻¹ : Γ₀) ∈ trivPart p Γ₀`. Introduce `x`. Establish `h6` using `hact (g q : G) _ _ (hw (((g q)⁻¹ : Γ₀) * x))`. Simplify `h6` using `[mul_assoc]`. Use `⟨(q, ⟨γ * (g q)⁻¹, htriv, hu'⟩), Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify using `[Φ]`. Use `haveI : Finite {γ : Γ₀ | (γ : G) * a ∈ S} := Finite.of_surjective Φ hbij.2`. Establish `hc` using `Nat.card_eq_of_bijective Φ hbij`. Rewrite `hc` using `[Nat.card_prod]`. Establish `hfinT : {γ : Γ₀ | (γ : G) * a ∈ S}.Finite` using `Set.toFinite _`.

Rewrite using `[← hfinT.cast_ncard_eq, ← Nat.card_coe_set_eq, ← hc]`. Both sides reduce to the same expression.
-/
theorem encard_translates (Γ₀ Γ₁ : Subgroup G) (hle : Γ₁ ≤ Γ₀) (hidx : Γ₁.relIndex Γ₀ ≠ 0)
    (hact : ∀ u a b, p a = p b → p (u * a) = p (u * b)) (S : Set G)
    (hsat : ∀ a b, p a = p b → a ∈ S → b ∈ S)
    (hcov : ∀ a, ∃ γ ∈ Γ₁, γ * a ∈ S)
    (hsep : ∀ a ∈ S, ∀ γ ∈ Γ₁, γ * a ∈ S → p (γ * a) = p a)
    (hfin : (trivPart p Γ₀).Finite) (a : G)
    (hgood : ∀ γ : Γ₀, p ((γ : G) * a) = p a → γ ∈ trivPart p Γ₀) :
    {γ : Γ₀ | (γ : G) * a ∈ S}.encard =
      ((Γ₁.relIndex Γ₀ * Nat.card {z : Γ₀ // z ∈ trivPart p Γ₀ ∧ (z : G) ∈ Γ₁} : ℕ) : ℕ∞) := by
  classical
  set H : Subgroup Γ₀ := Γ₁.subgroupOf Γ₀ with hH
  have hHidx : H.index ≠ 0 := hidx
  haveI : H.FiniteIndex := ⟨hHidx⟩
  haveI : Finite (Γ₀ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (trivPart p Γ₀) := hfin
  set Z := {z : Γ₀ // z ∈ trivPart p Γ₀ ∧ (z : G) ∈ Γ₁} with hZ
  haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : trivPart p Γ₀))
    (fun x y h => Subtype.ext (congrArg (fun w : trivPart p Γ₀ => w.1) h))
  have memH : ∀ u : Γ₀, u ∈ H ↔ (u : G) ∈ Γ₁ := fun u => Subgroup.mem_subgroupOf

  have hex : ∀ q : Γ₀ ⧸ H, ∃ g : Γ₀, (g : G) * a ∈ S ∧ (QuotientGroup.mk g⁻¹ : Γ₀ ⧸ H) = q := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨γ, hγ, hmem⟩ := hcov (((d⁻¹ : Γ₀) : G) * a)
    refine ⟨⟨γ, hle hγ⟩ * d⁻¹, by simpa [mul_assoc] using hmem, ?_⟩
    rw [QuotientGroup.eq, inv_inv, inv_mul_cancel_right, memH]
    exact hγ
  choose g hgS hgq using hex
  have hmaps : ∀ x : (Γ₀ ⧸ H) × Z, (((x.2.1 * g x.1 : Γ₀) : G) * a) ∈ S := by
    rintro ⟨q, z⟩
    have h1 := z.2.1 ((g q : G) * a)
    refine hsat _ _ h1.symm (hgS q) |> fun h => ?_
    simpa [mul_assoc] using h
  let Φ : (Γ₀ ⧸ H) × Z → {γ : Γ₀ | (γ : G) * a ∈ S} := fun x => ⟨x.2.1 * g x.1, hmaps x⟩
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨q, z⟩ ⟨q', z'⟩ h
      have h0 : z.1 * g q = z'.1 * g q' := congrArg Subtype.val h
      have hq : q = q' := by
        rw [← hgq q, ← hgq q', QuotientGroup.eq, inv_inv, memH]
        have e : g q * (g q')⁻¹ = z.1⁻¹ * z'.1 := by
          rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h0, mul_inv_cancel_right]
        rw [e]
        exact Γ₁.mul_mem (Γ₁.inv_mem z.2.2) z'.2.2
      subst hq
      have hz : z.1 = z'.1 := mul_right_cancel h0
      exact Prod.ext rfl (Subtype.ext hz)
    · rintro ⟨γ, hγ⟩
      set q : Γ₀ ⧸ H := QuotientGroup.mk γ⁻¹ with hq
      have h1 : g q * γ⁻¹ ∈ H := by
        have := hgq q
        rw [hq, QuotientGroup.eq, inv_inv] at this
        exact this
      have hu : γ * (g q)⁻¹ ∈ H := by
        have := H.inv_mem h1
        simpa using this
      have hu' : ((γ * (g q)⁻¹ : Γ₀) : G) ∈ Γ₁ := (memH _).1 hu
      have h2 := hsep _ (hgS q) _ hu' (by simpa [mul_assoc] using hγ)
      have h3 : p ((γ : G) * a) = p ((g q : G) * a) := by simpa [mul_assoc] using h2
      have h4 := hact ((g q : G)⁻¹) _ _ h3
      have h5 : p ((((g q)⁻¹ * γ : Γ₀) : G) * a) = p a := by
        simpa [mul_assoc] using h4
      have hw := hgood _ h5
      have htriv : (γ * (g q)⁻¹ : Γ₀) ∈ trivPart p Γ₀ := by
        intro x
        have h6 := hact (g q : G) _ _ (hw (((g q)⁻¹ : Γ₀) * x))
        simpa [mul_assoc] using h6
      refine ⟨(q, ⟨γ * (g q)⁻¹, htriv, hu'⟩), Subtype.ext ?_⟩
      simp [Φ]
  haveI : Finite {γ : Γ₀ | (γ : G) * a ∈ S} := Finite.of_surjective Φ hbij.2
  have hc := Nat.card_eq_of_bijective Φ hbij
  rw [Nat.card_prod] at hc
  have hfinT : {γ : Γ₀ | (γ : G) * a ∈ S}.Finite := Set.toFinite _
  rw [← hfinT.cast_ncard_eq, ← Nat.card_coe_set_eq, ← hc]
  rfl

/- English proof (translation)
Establish `hm : ∀ γ : Γ₀, AEMeasurable (fun x => S.indicator f (γ • x)) (μ.restrict FD)` using `fun γ => ((hf.indicator hS).comp (measurable_const_smul γ)).aemeasurable`. Rewrite using `[← lintegral_indicator hS, hFD.lintegral_eq_tsum'', ← lintegral_tsum hm, ← lintegral_const_mul _ hf]`. Use `lintegral_congr_ae ((ae_restrict_of_ae hN).mono fun a ha => ?_)` and prove the remaining obligations. Establish `e : ∀ γ : Γ₀, S.indicator f (γ • a) = ({γ : Γ₀ | (γ : G) * a ∈ S}).indicator (1 : Γ₀ → ℝ≥0∞) γ * f a`. Introduce `γ`.

Establish `hs : γ • a = (γ : G) * a` using `rfl`. Distinguish the cases in `h : (γ : G) * a ∈ S`. Rewrite using `[hs, Set.indicator_of_mem h, Set.indicator_of_mem (by exact h), hinv γ γ.2 a]`. Simplify using the standard rewrite rules. Rewrite using `[hs, Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]`.

Simplify using the standard rewrite rules. Simplify using `only [e]`. Establish `e2 : ∑' i : Γ₀, ({γ : Γ₀ | (γ : G) * a ∈ S}).indicator (1 : Γ₀ → ℝ≥0∞) i = (({γ : Γ₀ | (γ : G) * a ∈ S}.encard : ℕ∞) : ℝ≥0∞)`. Rewrite using `[← ENNReal.tsum_set_one]`. Conclude with `(tsum_subtype _ (fun _ => (1 : ℝ≥0∞))).symm`.

Rewrite using `[ENNReal.tsum_mul_right, e2, ha]`.
-/
theorem setLIntegral_eq_mul_of_count [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ₀ : Subgroup G) [Countable Γ₀] (FD : Set G) (hFD : IsFundamentalDomain Γ₀ FD μ) (S : Set G)
    (hS : MeasurableSet S) (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ₀, ∀ a, f (γ * a) = f a) (N : ℕ∞)
    (hN : ∀ᵐ a ∂μ, {γ : Γ₀ | (γ : G) * a ∈ S}.encard = N) :
    ∫⁻ a in S, f a ∂μ = (N : ℝ≥0∞) * ∫⁻ a in FD, f a ∂μ := by
  classical
  have hm : ∀ γ : Γ₀, AEMeasurable (fun x => S.indicator f (γ • x)) (μ.restrict FD) := fun γ =>
    ((hf.indicator hS).comp (measurable_const_smul γ)).aemeasurable
  rw [← lintegral_indicator hS, hFD.lintegral_eq_tsum'', ← lintegral_tsum hm, ← lintegral_const_mul _ hf]
  refine lintegral_congr_ae ((ae_restrict_of_ae hN).mono fun a ha => ?_)
  have e : ∀ γ : Γ₀, S.indicator f (γ • a) = ({γ : Γ₀ | (γ : G) * a ∈ S}).indicator (1 : Γ₀ → ℝ≥0∞) γ * f a := by
    intro γ
    have hs : γ • a = (γ : G) * a := rfl
    by_cases h : (γ : G) * a ∈ S
    · rw [hs, Set.indicator_of_mem h, Set.indicator_of_mem (by exact h), hinv γ γ.2 a]
      simp
    · rw [hs, Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]
      simp
  simp only [e]
  have e2 : ∑' i : Γ₀, ({γ : Γ₀ | (γ : G) * a ∈ S}).indicator (1 : Γ₀ → ℝ≥0∞) i =
      (({γ : Γ₀ | (γ : G) * a ∈ S}.encard : ℕ∞) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_set_one]
    exact (tsum_subtype _ (fun _ => (1 : ℝ≥0∞))).symm
  rw [ENNReal.tsum_mul_right, e2, ha]

end Orbit

section Ball

open scoped ComplexOrder in

/- English proof (translation)
Establish `h0 : (0 : Fin n → ℂ) ∈ ballDom q`. Introduce `τ`. Establish `: ballMat q (0 : Fin n → ℂ) τ = 0` using `by ext a b; simp [ballMat]`. Simplify using `[this, Matrix.PosDef.one]`. Establish `hs : StarConvex ℝ (0 : Fin n → ℂ) (ballDom q)`.

Introduce `t ht a b ha hb hab`. Rewrite using `[smul_zero, zero_add]`. Introduce `τ`. Establish `hZ : ballMat q (b • t) τ = (b : ℂ) • ballMat q t τ`. Use extensionality with `x y`.

Simplify using `[ballMat]`. Establish `hb1 : b ≤ 1` using `by linarith`. Establish `hP` using `ht τ`. Use `set Z := ballMat q t τ`. Establish `e : 1 - (ballMat q (b • t) τ)ᴴ * ballMat q (b • t) τ = ((1 - b ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) + ((b ^ 2 : ℝ) : ℂ) • (1 - Zᴴ * Z)`.

Rewrite using `[hZ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Rewrite using `[sub_smul, one_smul, pow_two]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Break down `eq_or_lt_of_le hb1 with h1 | h1` into its components or cases. Substitute `h1` using the available equality. Simplify using `using hP`. Establish `hc : (0 : ℂ) < ((1 - b ^ 2 : ℝ) : ℂ)`.

Establish `: (0 : ℝ) < 1 - b ^ 2` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Establish `hd : (0 : ℂ) ≤ ((b ^ 2 : ℝ) : ℂ)`. Establish `: (0 : ℝ) ≤ b ^ 2` using `by positivity`. Conclude with `this` after adjusting the coercions.

Conclude with `(Matrix.PosDef.one.smul hc).add_posSemidef (hP.posSemidef.smul hd)`. Conclude with `(hs.isPathConnected h0).isConnected.isPreconnected`.
-/
theorem isPreconnected_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsPreconnected (ballDom q) := by
  have h0 : (0 : Fin n → ℂ) ∈ ballDom q := by
    intro τ
    have : ballMat q (0 : Fin n → ℂ) τ = 0 := by ext a b; simp [ballMat]
    simp [this, Matrix.PosDef.one]
  have hs : StarConvex ℝ (0 : Fin n → ℂ) (ballDom q) := by
    intro t ht a b ha hb hab
    rw [smul_zero, zero_add]
    intro τ
    have hZ : ballMat q (b • t) τ = (b : ℂ) • ballMat q t τ := by
      ext x y
      simp [ballMat]
    have hb1 : b ≤ 1 := by linarith
    have hP := ht τ
    set Z := ballMat q t τ
    have e : 1 - (ballMat q (b • t) τ)ᴴ * ballMat q (b • t) τ =
        ((1 - b ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) + ((b ^ 2 : ℝ) : ℂ) • (1 - Zᴴ * Z) := by
      rw [hZ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      rw [sub_smul, one_smul, pow_two]
      abel
    rw [e]
    rcases eq_or_lt_of_le hb1 with h1 | h1
    · subst h1
      simpa using hP
    · have hc : (0 : ℂ) < ((1 - b ^ 2 : ℝ) : ℂ) := by
        have : (0 : ℝ) < 1 - b ^ 2 := by nlinarith
        exact_mod_cast this
      have hd : (0 : ℂ) ≤ ((b ^ 2 : ℝ) : ℂ) := by
        have : (0 : ℝ) ≤ b ^ 2 := by positivity
        exact_mod_cast this
      exact (Matrix.PosDef.one.smul hc).add_posSemidef (hP.posSemidef.smul hd)
  exact (hs.isPathConnected h0).isConnected.isPreconnected

/- English proof (translation)
Establish `hm : ∀ τ, Continuous fun t : Fin n → ℂ => ballMat q t τ` using `fun τ => continuous_matrix fun a b => continuous_apply _`. Establish `hd : ∀ τ, Measurable fun t : Fin n → ℂ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re` using `fun τ => Real.measurable_log.comp (Complex.continuous_re.comp (continuous_const.sub ((hm τ).matrix_conjTranspose.matrix_mul (hm τ))).matrix_det).measurable`. Unfold `ballDens ballPot`. Conclude with `Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun τ _ => hd τ).neg)`.
-/
theorem measurable_ballDens {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    Measurable (ballDens q) := by
  have hm : ∀ τ, Continuous fun t : Fin n → ℂ => ballMat q t τ := fun τ =>
    continuous_matrix fun a b => continuous_apply _
  have hd : ∀ τ, Measurable fun t : Fin n → ℂ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re := fun τ =>
    Real.measurable_log.comp (Complex.continuous_re.comp
      (continuous_const.sub ((hm τ).matrix_conjTranspose.matrix_mul (hm τ))).matrix_det).measurable
  unfold ballDens ballPot
  exact Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun τ _ => hd τ).neg)

end Ball

section Index

/- English proof (translation)
Establish `e : (H.map φ).subgroupOf φ.range = H.map φ.rangeRestrict`. Use extensionality with `⟨x, hx⟩`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨y, hy, Subtype.ext rfl⟩`. Introduce and unpack `⟨y, hy, h⟩`. Conclude with `⟨y, hy, congrArg Subtype.val h⟩`. Rewrite using `[Subgroup.relIndex, e]`. Introduce `h0`.

Use `Subgroup.index_map_dvd H φ.rangeRestrict_surjective` as an intermediate fact. Rewrite `this` using `[h0, zero_dvd_iff]`. Conclude with `hH this`.
-/
theorem relIndex_map_range_ne_zero {L G : Type} [Group L] [Group G] (φ : L →* G) (H : Subgroup L) (hH : H.index ≠ 0) :
    (H.map φ).relIndex φ.range ≠ 0 := by
  have e : (H.map φ).subgroupOf φ.range = H.map φ.rangeRestrict := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, Subtype.ext rfl⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, congrArg Subtype.val h⟩
  rw [Subgroup.relIndex, e]
  intro h0
  have := Subgroup.index_map_dvd H φ.rangeRestrict_surjective
  rw [h0, zero_dvd_iff] at this
  exact hH this

end Index

section Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {F : UnivFam E Ψ j j' n g Λ}

local notation "𝐯" => Pi.basisFun E (Fin (j + j'))

/- English proof (translation)
Rewrite using `[← Δ.π_range]`. Conclude with `⟨a, rfl⟩`.
-/
theorem pi_mem_ball (Δ : GroupDict F) (a) : Δ.π a ∈ ballDom F.q := by
  rw [← Δ.π_range]
  exact ⟨a, rfl⟩

/- English proof (translation)
Rewrite `h`, the goal using `[Δ.π_fibre]`. Simplify `h` using `[mul_assoc]`.
-/
theorem pi_mul_congr (Δ : GroupDict F) (u a b) (h : Δ.π a = Δ.π b) : Δ.π (u * a) = Δ.π (u * b) := by
  rw [Δ.π_fibre] at h ⊢
  simpa [mul_assoc] using h

/- English proof (translation)
Take `⟨h₁, hh₁⟩` from `h`. Take `⟨h₂, hh₂⟩` from `Δ.α_act γ a`. Take `⟨t₀, -, huniq⟩` from `F.univ (F.R t') (F.form_eq t') (F.sig t' ht')`. Establish `A : t' = t₀` using `huniq t' ⟨ht', LinearEquiv.refl ℂ _, fun x => rfl⟩`. Establish `B : Δ.π (archEmbed Δ.h 𝐯 γ * a) = t₀`.

Use `huniq _ ⟨pi_mem_ball Δ _, h₂.symm.trans h₁, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(Δ.α γ).1.surjective x`. Establish `e1` using `hh₁ y`. Establish `e2` using `hh₂ y`. Simplify using `only [LinearEquiv.trans_apply]`.

Rewrite using `[e2, LinearEquiv.symm_apply_apply, ← e1]`. Both sides reduce to the same expression. Rewrite using `[A, B]`.
-/
theorem pi_eq_of_eqvBy (Δ : GroupDict F) (γ : latticeStab Δ.h Δ.e.range) (a) (t' : Fin n → ℂ)
    (ht' : t' ∈ ballDom F.q) (h : (F.R (Δ.π a)).EqvBy (F.R t') (Δ.α γ).1) :
    Δ.π (archEmbed Δ.h 𝐯 γ * a) = t' := by
  obtain ⟨h₁, hh₁⟩ := h
  obtain ⟨h₂, hh₂⟩ := Δ.α_act γ a
  obtain ⟨t₀, -, huniq⟩ := F.univ (F.R t') (F.form_eq t') (F.sig t' ht')
  have A : t' = t₀ := huniq t' ⟨ht', LinearEquiv.refl ℂ _, fun x => rfl⟩
  have B : Δ.π (archEmbed Δ.h 𝐯 γ * a) = t₀ := by
    refine huniq _ ⟨pi_mem_ball Δ _, h₂.symm.trans h₁, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (Δ.α γ).1.surjective x
    have e1 := hh₁ y
    have e2 := hh₂ y
    simp only [LinearEquiv.trans_apply]
    rw [e2, LinearEquiv.symm_apply_apply, ← e1]
    rfl
  rw [A, B]

/- English proof (translation)
Take `⟨c, -, -, hc⟩` from `GlobalTheory.T.haar_pushforward_eq_ball_density E Ψ j j' n g Λ F Δ μ`. Take `⟨A, G, hA, -, hAπ, -⟩` from `Δ.act u`. Take `⟨a₀, ha₀⟩` from `hu`. Rewrite `ha₀` using `[hAπ]`. Take `⟨i, hi⟩` from `Function.ne_iff.1 ha₀`.

Establish `hfd : DifferentiableOn ℂ (fun t => A t i - t i) (ballDom F.q)` using `(differentiableOn_pi.1 hA i).sub (differentiable_apply i).differentiableOn`. Establish `hfa` using `GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (BallInverse.isOpen_ballDom F.q) hfd`. Establish `hz` using `ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd (BallInverse.isOpen_ballDom F.q) (isPreconnected_ballDom F.q) hfa ⟨Δ.π a₀, pi_mem_ball Δ a₀, sub_ne_zero.2 hi⟩`. Use `set Zr := {z | z ∈ ballDom F.q ∧ A z i - z i = 0} with hZr`. Establish `hν : (μ.map Δ.π) Zr = 0`.

Rewrite using `[hc, Measure.smul_apply, smul_eq_mul]`. Establish `h1 : (volume.restrict (ballDom F.q)) Zr = 0` using `Measure.restrict_le_self.absolutelyContinuous hz`. Establish `h2` using `withDensity_absolutelyContinuous (volume.restrict (ballDom F.q)) (fun t => ENNReal.ofReal (ballDens F.q t)) h1`. Rewrite using `[h2, mul_zero]`. Use `measure_mono_null ?_ (le_antisymm ((Measure.le_map_apply Δ.π_cont.aemeasurable Zr).trans hν.le) bot_le)` and prove the remaining obligations.

Introduce `a ha`. Use `⟨pi_mem_ball Δ a, ?_⟩` and prove the remaining obligations. Establish `ha' : Δ.π (u * a) = Δ.π a` using `ha`. Rewrite `ha'` using `[hAπ]`. Simplify using `[ha']`.
-/
theorem null_fixed (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h 𝐯)) [μ.IsHaarMeasure] (u : archUnitary Δ.h 𝐯)
    (hu : ∃ a, Δ.π (u * a) ≠ Δ.π a) : μ {a | Δ.π (u * a) = Δ.π a} = 0 := by
  obtain ⟨c, -, -, hc⟩ := GlobalTheory.T.haar_pushforward_eq_ball_density E Ψ j j' n g Λ F Δ μ
  obtain ⟨A, G, hA, -, hAπ, -⟩ := Δ.act u
  obtain ⟨a₀, ha₀⟩ := hu
  rw [hAπ] at ha₀
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha₀
  have hfd : DifferentiableOn ℂ (fun t => A t i - t i) (ballDom F.q) :=
    (differentiableOn_pi.1 hA i).sub (differentiable_apply i).differentiableOn
  have hfa := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (BallInverse.isOpen_ballDom F.q) hfd
  have hz := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd (BallInverse.isOpen_ballDom F.q)
    (isPreconnected_ballDom F.q) hfa ⟨Δ.π a₀, pi_mem_ball Δ a₀, sub_ne_zero.2 hi⟩
  set Zr := {z | z ∈ ballDom F.q ∧ A z i - z i = 0} with hZr
  have hν : (μ.map Δ.π) Zr = 0 := by
    rw [hc, Measure.smul_apply, smul_eq_mul]
    have h1 : (volume.restrict (ballDom F.q)) Zr = 0 := Measure.restrict_le_self.absolutelyContinuous hz
    have h2 := withDensity_absolutelyContinuous (volume.restrict (ballDom F.q))
      (fun t => ENNReal.ofReal (ballDens F.q t)) h1
    rw [h2, mul_zero]
  refine measure_mono_null ?_ (le_antisymm ((Measure.le_map_apply Δ.π_cont.aemeasurable Zr).trans hν.le) bot_le)
  intro a ha
  refine ⟨pi_mem_ball Δ a, ?_⟩
  have ha' : Δ.π (u * a) = Δ.π a := ha
  rw [hAπ] at ha'
  simp [ha']

/- English proof (translation)
Use `haveI : DiscreteTopology (archLatticeGroup Δ.h 𝐯 Δ.e.range) := ArchLatticeDiscrete.proof Δ.h 𝐯 Δ.e.range Δ.integral.isLattice`. Establish `hK : IsCompact (Δ.M.stab : Set (archUnitary Δ.h 𝐯))` using `MajorantStabCompact.proof Δ.h 𝐯 Δ.M`. Establish `hcl : IsClosed ((archLatticeGroup Δ.h 𝐯 Δ.e.range : Subgroup _) : Set (archUnitary Δ.h 𝐯))` using `Subgroup.isClosed_of_discrete`. Establish `hf : (((archLatticeGroup Δ.h 𝐯 Δ.e.range : Subgroup _) : Set (archUnitary Δ.h 𝐯)) ∩ Δ.M.stab).Finite` using `(hK.inter_left hcl).finite ((isDiscrete_iff_discreteTopology.2 (inferInstanceAs (DiscreteTopology (archLatticeGroup Δ.h 𝐯 Δ.e.range)))).mono Set.inter_subset_left)`. Use `(hf.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, ?_⟩` and prove the remaining obligations.

Establish `h1 : Δ.π ((γ : archUnitary Δ.h 𝐯) * 1) = Δ.π 1` using `hγ 1`. Establish `h2` using `(Δ.π_fibre 1 (γ : archUnitary Δ.h 𝐯)).1 (by simpa using h1.symm)`. Simplify using `using h2`.
-/
theorem finite_trivPart (Δ : GroupDict F) :
    (trivPart Δ.π (archLatticeGroup Δ.h 𝐯 Δ.e.range)).Finite := by
  haveI : DiscreteTopology (archLatticeGroup Δ.h 𝐯 Δ.e.range) :=
    ArchLatticeDiscrete.proof Δ.h 𝐯 Δ.e.range Δ.integral.isLattice
  have hK : IsCompact (Δ.M.stab : Set (archUnitary Δ.h 𝐯)) := MajorantStabCompact.proof Δ.h 𝐯 Δ.M
  have hcl : IsClosed ((archLatticeGroup Δ.h 𝐯 Δ.e.range : Subgroup _) : Set (archUnitary Δ.h 𝐯)) :=
    Subgroup.isClosed_of_discrete
  have hf : (((archLatticeGroup Δ.h 𝐯 Δ.e.range : Subgroup _) : Set (archUnitary Δ.h 𝐯)) ∩ Δ.M.stab).Finite :=
    (hK.inter_left hcl).finite
      ((isDiscrete_iff_discreteTopology.2 (inferInstanceAs (DiscreteTopology (archLatticeGroup Δ.h 𝐯 Δ.e.range)))).mono
        Set.inter_subset_left)
  refine (hf.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, ?_⟩
  have h1 : Δ.π ((γ : archUnitary Δ.h 𝐯) * 1) = Δ.π 1 := hγ 1
  have h2 := (Δ.π_fibre 1 (γ : archUnitary Δ.h 𝐯)).1 (by simpa using h1.symm)
  simpa using h2

end Dict

section Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {F : UnivFam E Ψ j j' n g Λ}

local notation "𝐯" => Pi.basisFun E (Fin (j + j'))

/- English proof (translation)
Take `⟨c, hc0, hcT, hc⟩` from `GlobalTheory.T.haar_pushforward_eq_ball_density E Ψ j j' n g Λ F Δ μ`. Use `set Γ₀ := archLatticeGroup Δ.h 𝐯 Δ.e.range with hΓ₀`. Set `φ : latticeStab Δ.h Δ.e.range →* archUnitary Δ.h 𝐯` to `(archEmbed Δ.h 𝐯).comp (latticeStab Δ.h Δ.e.range).subtype`. Set `ψ : latticeStab Δ.h Δ.e.range →* (Λ ≃ₗ[𝓞 E] Λ)` to `(autGrp F.form).subtype.comp Δ.α.toMonoidHom`. Establish `hrange : φ.range = Γ₀`.

Rewrite using `[hΓ₀, archLatticeGroup, MonoidHom.range_comp, Subgroup.range_subtype]`. Establish `hψ : ψ.range = autGrp F.form`. Rewrite using `[MonoidHom.range_comp, MonoidHom.range_eq_top.2 Δ.α.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]`. Use `set Γ₁ : Subgroup (archUnitary Δ.h 𝐯) := (Γ.comap ψ).map φ with hΓ₁`. Establish `hle : Γ₁ ≤ Γ₀`.

Rewrite using `[← hrange, hΓ₁]`. Conclude with `Subgroup.map_le_range _ _`. Establish `hidx : Γ₁.relIndex Γ₀ ≠ 0`. Rewrite using `[← hrange]`. Use `relIndex_map_range_ne_zero φ _ ?_` and prove the remaining obligations.

Rewrite using `[Subgroup.index_comap, hψ]`. Conclude with `hΓ.2`. Use `haveI : Countable Γ₀ := by`. Establish `: Countable Δ.h.unitaryGroup` using `countable_unitaryGroup Δ.h 𝐯`. Establish `h1 : ((Γ₀ : Subgroup _) : Set (archUnitary Δ.h 𝐯)).Countable`.

Rewrite using `[hΓ₀, archLatticeGroup, Subgroup.coe_map]`. Conclude with `(Set.to_countable _).image _`. Conclude with `h1.to_subtype`. Use `set S : Set (archUnitary Δ.h 𝐯) := Δ.π ⁻¹' FF with hS`. Establish `hSm : MeasurableSet S` using `Δ.π_cont.measurable hFF.1`.

Establish `hact` using `pi_mul_congr Δ`. Establish `hsat : ∀ a b, Δ.π a = Δ.π b → a ∈ S → b ∈ S` using `fun a b h ha => by`. Simplify `ha` using `[hS, ← h]`. Establish `hcov : ∀ a, ∃ γ ∈ Γ₁, γ * a ∈ S`. Introduce `a`.

Take `⟨t', ht', γ, hγ, hE⟩` from `hFF.2.2.1 (Δ.π a) (pi_mem_ball Δ a)`. Use `set s := Δ.α.symm ⟨γ, hΓ.1 hγ⟩ with hs`. Establish `hαs : (Δ.α s).1 = γ` using `by simp [hs]`. Use `⟨φ s, ⟨s, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show ψ s ∈ Γ show (Δ.α s).1 ∈ Γ`.

Rewrite using `[hαs]`. Conclude with `hγ`. Use `pi_eq_of_eqvBy Δ s a t' (hFF.2.1 ht') (by rw [hαs]; exact hE) show Δ.π (φ s * a) ∈ FF` as an intermediate fact. Establish `e : φ s = archEmbed Δ.h 𝐯 s` using `rfl`. Rewrite using `[e, this]`.

Conclude with `ht'`. Establish `hsep : ∀ a ∈ S, ∀ γ ∈ Γ₁, γ * a ∈ S → Δ.π (γ * a) = Δ.π a`. Introduce and unpack `a ha _ ⟨s, hs, rfl⟩ hγ`. Use `(hFF.2.2.2 _ ha _ hγ ⟨(Δ.α s).1, hs, Δ.α_act s a⟩).symm` and prove the remaining obligations. Establish `hfin` using `finite_trivPart Δ`.

Use `set N : ℕ := Γ₁.relIndex Γ₀ * Nat.card {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} with hN`. Establish `hN0 : N ≠ 0`. Use `Nat.mul_ne_zero hidx ?_` and prove the remaining obligations. Use `haveI : Finite (trivPart Δ.π Γ₀) := hfin`. Use `haveI : Finite {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} := Finite.of_injective (fun z => (⟨z.1, z.2.1⟩ : trivPart Δ.π Γ₀)) (fun x y h => Subtype.ext (congrArg (fun w : trivPart Δ.π Γ₀ => w.1) h))`.

Use `haveI : Nonempty {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} := ⟨⟨1, fun a => by simp, Γ₁.one_mem⟩⟩`. Conclude with `Nat.card_pos.ne'`. Establish `hgood : ∀ᵐ a ∂μ, ∀ γ : Γ₀, Δ.π ((γ : archUnitary Δ.h 𝐯) * a) = Δ.π a → γ ∈ trivPart Δ.π Γ₀`. Rewrite using `[ae_all_iff]`. Introduce `γ`.

Distinguish the cases in `hγ : γ ∈ trivPart Δ.π Γ₀`. Conclude with `ae_of_all _ fun _ _ => hγ`. Establish `hne : ∃ a, Δ.π ((γ : archUnitary Δ.h 𝐯) * a) ≠ Δ.π a`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `hγ hcon`. Establish `h0` using `null_fixed Δ μ (γ : archUnitary Δ.h 𝐯) hne`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with a ha h1`. Conclude with `absurd h1 ha`. Establish `hcount : ∀ᵐ a ∂μ, {γ : Γ₀ | (γ : archUnitary Δ.h 𝐯) * a ∈ S}.encard = ((N : ℕ) : ℕ∞)` using `hgood.mono fun a ha => encard_translates Δ.π Γ₀ Γ₁ hle hidx hact S hsat hcov hsep hfin a ha`.

Use `⟨c⁻¹ * (N : ℝ≥0∞), ?_, ?_, fun Φ hΦ hinv => ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (ENNReal.inv_ne_zero.2 hcT) (by exact_mod_cast hN0)`. Conclude with `ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.natCast_ne_top N)`. Establish `hπm : Measurable Δ.π` using `Δ.π_cont.measurable`. Establish `hdens : Measurable fun t => ENNReal.ofReal (ballDens F.q t)` using `ENNReal.measurable_ofReal.comp (measurable_ballDens F.q)`.

Establish `hfinv : ∀ γ ∈ Γ₀, ∀ a, Φ (Δ.π (γ * a)) = Φ (Δ.π a)`. Introduce and unpack `_ ⟨s, hs, rfl⟩ a`. Conclude with `(hinv _ (pi_mem_ball Δ a) _ (pi_mem_ball Δ _) ⟨(Δ.α ⟨s, hs⟩).1, (Δ.α ⟨s, hs⟩).2, Δ.α_act ⟨s, hs⟩ a⟩).symm`. Establish `h1` using `setLIntegral_eq_mul_of_count μ Γ₀ FD hFD S hSm (fun a => Φ (Δ.π a)) (hΦ.comp hπm) hfinv ((N : ℕ) : ℕ∞) hcount`. Establish `h2 : ∫⁻ a in S, Φ (Δ.π a) ∂μ = c * ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t)`.

Rewrite using `[hS, ← setLIntegral_map hFF.1 hΦ hπm, hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, restrict_withDensity hFF.1, lintegral_withDensity_eq_lintegral_mul _ hdens hΦ, Measure.restrict_restrict hFF.1, Set.inter_eq_left.2 hFF.2.1]`. Use `congr 1`. Use `lintegral_congr fun t => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`. Rewrite `h1` using `[h2]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]`. Use `_ = c⁻¹ * (N : ℝ≥0∞) * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by`. Rewrite using `[h1, mul_assoc]`. Simplify using the standard rewrite rules.
-/
theorem exists_const_lintegral (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h 𝐯)) [μ.IsHaarMeasure]
    (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h 𝐯)) (hΓ : F.IsArith Γ)
    (hFF : F.IsFundSet Γ FF) (hFD : IsFundamentalDomain (archLatticeGroup Δ.h 𝐯 Δ.e.range) FD μ) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ →
      (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') →
      ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  classical
  obtain ⟨c, hc0, hcT, hc⟩ := GlobalTheory.T.haar_pushforward_eq_ball_density E Ψ j j' n g Λ F Δ μ
  set Γ₀ := archLatticeGroup Δ.h 𝐯 Δ.e.range with hΓ₀
  let φ : latticeStab Δ.h Δ.e.range →* archUnitary Δ.h 𝐯 := (archEmbed Δ.h 𝐯).comp (latticeStab Δ.h Δ.e.range).subtype
  let ψ : latticeStab Δ.h Δ.e.range →* (Λ ≃ₗ[𝓞 E] Λ) := (autGrp F.form).subtype.comp Δ.α.toMonoidHom
  have hrange : φ.range = Γ₀ := by
    rw [hΓ₀, archLatticeGroup, MonoidHom.range_comp, Subgroup.range_subtype]
  have hψ : ψ.range = autGrp F.form := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 Δ.α.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set Γ₁ : Subgroup (archUnitary Δ.h 𝐯) := (Γ.comap ψ).map φ with hΓ₁
  have hle : Γ₁ ≤ Γ₀ := by
    rw [← hrange, hΓ₁]
    exact Subgroup.map_le_range _ _
  have hidx : Γ₁.relIndex Γ₀ ≠ 0 := by
    rw [← hrange]
    refine relIndex_map_range_ne_zero φ _ ?_
    rw [Subgroup.index_comap, hψ]
    exact hΓ.2
  haveI : Countable Γ₀ := by
    have : Countable Δ.h.unitaryGroup := countable_unitaryGroup Δ.h 𝐯
    have h1 : ((Γ₀ : Subgroup _) : Set (archUnitary Δ.h 𝐯)).Countable := by
      rw [hΓ₀, archLatticeGroup, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    exact h1.to_subtype
  set S : Set (archUnitary Δ.h 𝐯) := Δ.π ⁻¹' FF with hS
  have hSm : MeasurableSet S := Δ.π_cont.measurable hFF.1
  have hact := pi_mul_congr Δ
  have hsat : ∀ a b, Δ.π a = Δ.π b → a ∈ S → b ∈ S := fun a b h ha => by
    simpa [hS, ← h] using ha
  have hcov : ∀ a, ∃ γ ∈ Γ₁, γ * a ∈ S := by
    intro a
    obtain ⟨t', ht', γ, hγ, hE⟩ := hFF.2.2.1 (Δ.π a) (pi_mem_ball Δ a)
    set s := Δ.α.symm ⟨γ, hΓ.1 hγ⟩ with hs
    have hαs : (Δ.α s).1 = γ := by simp [hs]
    refine ⟨φ s, ⟨s, ?_, rfl⟩, ?_⟩
    · show ψ s ∈ Γ
      show (Δ.α s).1 ∈ Γ
      rw [hαs]
      exact hγ
    · have := pi_eq_of_eqvBy Δ s a t' (hFF.2.1 ht') (by rw [hαs]; exact hE)
      show Δ.π (φ s * a) ∈ FF
      have e : φ s = archEmbed Δ.h 𝐯 s := rfl
      rw [e, this]
      exact ht'
  have hsep : ∀ a ∈ S, ∀ γ ∈ Γ₁, γ * a ∈ S → Δ.π (γ * a) = Δ.π a := by
    rintro a ha _ ⟨s, hs, rfl⟩ hγ
    refine (hFF.2.2.2 _ ha _ hγ ⟨(Δ.α s).1, hs, Δ.α_act s a⟩).symm
  have hfin := finite_trivPart Δ
  set N : ℕ := Γ₁.relIndex Γ₀ * Nat.card {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} with hN
  have hN0 : N ≠ 0 := by
    refine Nat.mul_ne_zero hidx ?_
    haveI : Finite (trivPart Δ.π Γ₀) := hfin
    haveI : Finite {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} :=
      Finite.of_injective (fun z => (⟨z.1, z.2.1⟩ : trivPart Δ.π Γ₀))
        (fun x y h => Subtype.ext (congrArg (fun w : trivPart Δ.π Γ₀ => w.1) h))
    haveI : Nonempty {z : Γ₀ // z ∈ trivPart Δ.π Γ₀ ∧ (z : archUnitary Δ.h 𝐯) ∈ Γ₁} :=
      ⟨⟨1, fun a => by simp, Γ₁.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hgood : ∀ᵐ a ∂μ, ∀ γ : Γ₀, Δ.π ((γ : archUnitary Δ.h 𝐯) * a) = Δ.π a → γ ∈ trivPart Δ.π Γ₀ := by
    rw [ae_all_iff]
    intro γ
    by_cases hγ : γ ∈ trivPart Δ.π Γ₀
    · exact ae_of_all _ fun _ _ => hγ
    · have hne : ∃ a, Δ.π ((γ : archUnitary Δ.h 𝐯) * a) ≠ Δ.π a := by
        by_contra hcon
        push Not at hcon
        exact hγ hcon
      have h0 := null_fixed Δ μ (γ : archUnitary Δ.h 𝐯) hne
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with a ha h1
      exact absurd h1 ha
  have hcount : ∀ᵐ a ∂μ, {γ : Γ₀ | (γ : archUnitary Δ.h 𝐯) * a ∈ S}.encard = ((N : ℕ) : ℕ∞) :=
    hgood.mono fun a ha =>
      encard_translates Δ.π Γ₀ Γ₁ hle hidx hact S hsat hcov hsep hfin a ha
  refine ⟨c⁻¹ * (N : ℝ≥0∞), ?_, ?_, fun Φ hΦ hinv => ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.2 hcT) (by exact_mod_cast hN0)
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) (ENNReal.natCast_ne_top N)
  have hπm : Measurable Δ.π := Δ.π_cont.measurable
  have hdens : Measurable fun t => ENNReal.ofReal (ballDens F.q t) :=
    ENNReal.measurable_ofReal.comp (measurable_ballDens F.q)
  have hfinv : ∀ γ ∈ Γ₀, ∀ a, Φ (Δ.π (γ * a)) = Φ (Δ.π a) := by
    rintro _ ⟨s, hs, rfl⟩ a
    exact (hinv _ (pi_mem_ball Δ a) _ (pi_mem_ball Δ _)
      ⟨(Δ.α ⟨s, hs⟩).1, (Δ.α ⟨s, hs⟩).2, Δ.α_act ⟨s, hs⟩ a⟩).symm
  have h1 := setLIntegral_eq_mul_of_count μ Γ₀ FD hFD S hSm (fun a => Φ (Δ.π a)) (hΦ.comp hπm) hfinv
    ((N : ℕ) : ℕ∞) hcount
  have h2 : ∫⁻ a in S, Φ (Δ.π a) ∂μ = c * ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) := by
    rw [hS, ← setLIntegral_map hFF.1 hΦ hπm, hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      restrict_withDensity hFF.1, lintegral_withDensity_eq_lintegral_mul _ hdens hΦ,
      Measure.restrict_restrict hFF.1, Set.inter_eq_left.2 hFF.2.1]
    congr 1
    refine lintegral_congr fun t => ?_
    simp [mul_comm]
  rw [h2] at h1
  calc ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t)
      = c⁻¹ * (c * ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
    _ = c⁻¹ * (N : ℝ≥0∞) * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
        rw [h1, mul_assoc]
        simp

end Dict

/- English proof (translation)
Introduce `E _ _ _ Ψ _ j j' n g Λ _ _ F Δ μ _ Γ FF FD hΓ hFF hFD`. Conclude with `exists_const_lintegral Δ μ Γ FF FD hΓ hFF hFD`.
-/
theorem lintegral_fundSet_eq_const_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))), F.IsArith Γ → F.IsFundSet Γ FF → IsFundamentalDomain (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) FD μ → ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ → (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') → ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F Δ μ _ Γ FF FD hΓ hFF hFD
  exact exists_const_lintegral Δ μ Γ FF FD hΓ hFF hFD

end GlobalTheory.CompanionTheory.Ar.Cusp
