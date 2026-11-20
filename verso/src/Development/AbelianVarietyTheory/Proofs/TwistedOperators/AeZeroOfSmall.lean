import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDescendPeriodicTrig
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffMulCharConvAndHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanPeriodicIndepOfCovolumeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPosOfPeriodicNonneg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped TensorProduct ContDiff Topology NNReal ENNReal

namespace GlobalTheory.ThetaAllChar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilVacMove GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨ψ₀, hstd, a, ha, hψa⟩` from `exists_std hψ`. Establish `hlaws` using `GlobalTheory.OrientedFormLaws.symplOH_laws D S T`. Use `set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) a with hc`.

Establish `hmap : (c • x : WO S T) = x.map fun z => algebraMap (AF D.host.F) (AE D) c * z`. Use extensionality with `i j`. Simplify using `[Matrix.smul_apply, Algebra.smul_def]`. Establish `key : ∀ y : WO S T, symplO S T (c • x) y = c * symplO S T x y`. Introduce `y`.

Rewrite using `[hmap]`. Unfold `symplO`. Rewrite using `[GlobalTheory.OrientedFormLaws.hO_mul_left, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`. Establish `hx' : (c • x : WO S T) ∈ ratL T S`. Use `(GlobalTheory.RatAnnih.ratL_annihilator D ψ₀ hstd S T _).1 ?_` and prove the remaining obligations.

Introduce `γ hγ`. Rewrite using `[key, hc, ← hψa, ← hlaws.2.2.2.1]`. Conclude with `h ⟨γ, hγ⟩`. Establish `hback` using `smul_mem_ratL a⁻¹ hx'`. Rewrite `hback` using `[hc, smul_smul, ← map_mul, inv_mul_cancel₀ ha, map_one, one_smul]`.

Conclude with `hback`. Introduce `hx γ`. Conclude with `chi_rat hψ γ.2 hx`.
-/
theorem chi_ker (hψ : IsCharAF D.host.F ψ) (x : WO S T) :
    (∀ γ : ratL T S, chi ψ S T γ x = 1) ↔ x ∈ ratL T S := by
  constructor
  · intro h
    obtain ⟨ψ₀, hstd, a, ha, hψa⟩ := exists_std hψ
    have hlaws := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
    set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) a with hc
    have hmap : (c • x : WO S T) = x.map fun z => algebraMap (AF D.host.F) (AE D) c * z := by
      ext i j
      simp [Matrix.smul_apply, Algebra.smul_def]

    have key : ∀ y : WO S T, symplO S T (c • x) y = c * symplO S T x y := by
      intro y
      rw [hmap]
      unfold symplO
      rw [GlobalTheory.OrientedFormLaws.hO_mul_left, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
    have hx' : (c • x : WO S T) ∈ ratL T S := by
      refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ₀ hstd S T _).1 ?_
      intro γ hγ
      rw [key, hc, ← hψa, ← hlaws.2.2.2.1]
      exact h ⟨γ, hγ⟩
    have hback := smul_mem_ratL a⁻¹ hx'
    rw [hc, smul_smul, ← map_mul, inv_mul_cancel₀ ha, map_one, one_smul] at hback
    exact hback
  · intro hx γ
    exact chi_rat hψ γ.2 hx

/- English proof (translation)
Unfold `chi`. Conclude with `hn _`.
-/
theorem norm_chi (hn : ∀ x, ‖ψ x‖ = 1) (γ x : WO S T) : ‖chi ψ S T γ x‖ = 1 := by
  unfold chi
  exact hn _

def chiR (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (γ : ratL T S) : WO S T → ℂ := chi ψ S T γ.1

/- English proof (translation)
Use `⟨fun a => continuous_chi hψ.1 _, fun a x y => chi_add _ _ _, fun a b x => ?_, fun x => ?_, fun a x => norm_chi hψ.2.1 _ _, fun x => chi_ker hψ x⟩` and prove the remaining obligations. Use `show chi ψ S T ((a + b : ratL T S) : WO S T) x = chi ψ S T a x * chi ψ S T b x`. Rewrite using `[AddSubgroup.coe_add]`. Conclude with `chi_add_left _ _ _`. Use `show chi ψ S T ((0 : ratL T S) : WO S T) x = 1`.

Rewrite using `[ZeroMemClass.coe_zero]`. Conclude with `chi_zero_left x`.
-/
theorem chiR_laws (hψ : IsCharAF D.host.F ψ) : (∀ a, Continuous (chiR ψ S T a)) ∧
    (∀ a x y, chiR ψ S T a (x + y) = chiR ψ S T a x * chiR ψ S T a y) ∧
    (∀ a b x, chiR ψ S T (a + b) x = chiR ψ S T a x * chiR ψ S T b x) ∧ (∀ x, chiR ψ S T 0 x = 1) ∧
    (∀ a x, ‖chiR ψ S T a x‖ = 1) ∧ ∀ x, (∀ a, chiR ψ S T a x = 1) ↔ x ∈ ratL T S := by
  refine ⟨fun a => continuous_chi hψ.1 _, fun a x y => chi_add _ _ _, fun a b x => ?_, fun x => ?_,
    fun a x => norm_chi hψ.2.1 _ _, fun x => chi_ker hψ x⟩
  · show chi ψ S T ((a + b : ratL T S) : WO S T) x = chi ψ S T a x * chi ψ S T b x
    rw [AddSubgroup.coe_add]
    exact chi_add_left _ _ _
  · show chi ψ S T ((0 : ratL T S) : WO S T) x = 1
    rw [ZeroMemClass.coe_zero]
    exact chi_zero_left x

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (isTheta_zero : IsThetaFunO ψ S T 0)`. Consider the case `@insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `isTheta_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem isTheta_sum {ι : Type} (s : Finset ι) (F : ι → WO S T → ℂ) (h : ∀ i ∈ s, IsThetaFunO ψ S T (F i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isTheta_zero : IsThetaFunO ψ S T 0)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isTheta_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def trig (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (s : Finset (ratL T S)) (c : ratL T S → ℂ) : WO S T → ℂ :=
  ∑ γ ∈ s, c γ • chi ψ S T γ

/- English proof (translation)
Establish `hpt : ∀ w, ‖u w‖ₑ ^ 2 ≤ ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (B ^ 2)`. Introduce `w`. Establish `h0 : 0 ≤ ‖u w‖` using `norm_nonneg _`. Rewrite using `[← ENNReal.ofReal_mul (sq_nonneg ε), ← mul_pow, ← ofReal_norm, ← ENNReal.ofReal_pow h0]`. Conclude with `ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 (h w) 2)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_sq_le {G : Type} [MeasurableSpace G] (ν : Measure G) {u : G → ℂ} {ε B : ℝ}
    (h : ∀ w, ‖u w‖ ≤ ε * B) : ∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (B ^ 2) * ν Set.univ) := by
  have hpt : ∀ w, ‖u w‖ₑ ^ 2 ≤ ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (B ^ 2) := by
    intro w
    have h0 : 0 ≤ ‖u w‖ := norm_nonneg _
    rw [← ENNReal.ofReal_mul (sq_nonneg ε), ← mul_pow, ← ofReal_norm, ← ENNReal.ofReal_pow h0]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 (h w) 2)
  calc ∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν ≤ ∫⁻ _w, ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (B ^ 2) ∂ν := lintegral_mono hpt
    _ = _ := by rw [lintegral_const, mul_assoc]

/- English proof (translation)
Establish `hpt : ∀ a b : ℂ, ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2)`. Introduce `a b`. Establish `ha` using `norm_nonneg a`. Establish `hb` using `norm_nonneg b`. Establish `hab : ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)`.

Establish `t` using `norm_sub_le a b`. Establish `t0` using `norm_nonneg (a - b)`. Use polynomial arithmetic with `[sq_nonneg (‖a‖ - ‖b‖)]`. Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]`. Conclude with `ENNReal.ofReal_le_ofReal hab`.

Use `set I := ∫⁻ w, ‖h w‖ₑ ^ 2 ∂ν with hI`. Establish `hK : 2 * (M + N) ≠ ⊤` using `ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hM, hN⟩)`. Establish `hle : ∀ ε : ℝ, 0 < ε → I ≤ ENNReal.ofReal (ε ^ 2) * (2 * (M + N))`. Introduce `ε hε`. Take `⟨u, v, hu, huv, hu2, hv2⟩` from `hs ε hε`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun w => ?_` and prove the remaining obligations. Rewrite using `[huv]`. Conclude with `hpt (u w) (v w)`. Use `_ = 2 * (∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν + ∫⁻ w, ‖v w‖ₑ ^ 2 ∂ν) := by`.

Rewrite using `[lintegral_const_mul' _ _ (by simp), lintegral_add_left (hu.enorm.pow_const 2)]`. Use `_ ≤ 2 * (ENNReal.ofReal (ε ^ 2) * M + ENNReal.ofReal (ε ^ 2) * N) := by gcongr`. Use `_ = ENNReal.ofReal (ε ^ 2) * (2 * (M + N)) := by ring`. Establish `hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2) * (2 * (M + N))) (𝓝[>] 0) (𝓝 0)`. Establish `h1 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2)) (𝓝[>] 0) (𝓝 0)`.

Establish `: Filter.Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 0)`. Simplify using `using ((continuous_pow 2).tendsto (0 : ℝ))`. Simplify using `using (ENNReal.tendsto_ofReal (this.mono_left nhdsWithin_le_nhds))`. Simplify using `using ENNReal.Tendsto.mul_const h1 (Or.inr hK)`. Establish `hI0 : I = 0`.

Use `le_antisymm (ge_of_tendsto hlim ?_) bot_le` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε using hle ε hε`. Establish `hae` using `(lintegral_eq_zero_iff (hm.enorm.pow_const 2)).1 hI0`. Use `filter_upwards [hae] with w hw`. Simplify using `using hw`.
-/
theorem ae_zero_of_small {G : Type} [MeasurableSpace G] (ν : Measure G) {h : G → ℂ} (hm : Measurable h) {M N : ℝ≥0∞}
    (hM : M ≠ ⊤) (hN : N ≠ ⊤) (hs : ∀ ε : ℝ, 0 < ε → ∃ u v : G → ℂ, Measurable u ∧ h = u - v ∧
      ∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (ε ^ 2) * M ∧ ∫⁻ w, ‖v w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (ε ^ 2) * N) :
    ∀ᵐ w ∂ν, h w = 0 := by

  have hpt : ∀ a b : ℂ, ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
    intro a b
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    have hab : ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
      have t := norm_sub_le a b
      have t0 := norm_nonneg (a - b)
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hab
  set I := ∫⁻ w, ‖h w‖ₑ ^ 2 ∂ν with hI
  have hK : 2 * (M + N) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hM, hN⟩)
  have hle : ∀ ε : ℝ, 0 < ε → I ≤ ENNReal.ofReal (ε ^ 2) * (2 * (M + N)) := by
    intro ε hε
    obtain ⟨u, v, hu, huv, hu2, hv2⟩ := hs ε hε
    calc I ≤ ∫⁻ w, 2 * (‖u w‖ₑ ^ 2 + ‖v w‖ₑ ^ 2) ∂ν := by
          refine lintegral_mono fun w => ?_
          rw [huv]
          exact hpt (u w) (v w)
      _ = 2 * (∫⁻ w, ‖u w‖ₑ ^ 2 ∂ν + ∫⁻ w, ‖v w‖ₑ ^ 2 ∂ν) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (hu.enorm.pow_const 2)]
      _ ≤ 2 * (ENNReal.ofReal (ε ^ 2) * M + ENNReal.ofReal (ε ^ 2) * N) := by gcongr
      _ = ENNReal.ofReal (ε ^ 2) * (2 * (M + N)) := by ring
  have hlim : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2) * (2 * (M + N))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_pow 2).tendsto (0 : ℝ))
      simpa using (ENNReal.tendsto_ofReal (this.mono_left nhdsWithin_le_nhds))
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hK)
  have hI0 : I = 0 := by
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [self_mem_nhdsWithin] with ε hε using hle ε hε
  have hae := (lintegral_eq_zero_iff (hm.enorm.pow_const 2)).1 hI0
  filter_upwards [hae] with w hw
  simpa using hw

/- English proof (translation)
Introduce `μ 𝓕 hμ h𝓕 A hAθ hAc hAb`. Take `⟨C, hC⟩` from `hAb`. Establish `hE` using `isExpChar_of_isCharAF hψ`. Establish `hn` using `hE.2.1`. Establish `: μ.IsAddHaarMeasure` using `hμ`.

Take `⟨h1, h2, h3, h4, h5, K, hK, hcov⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `h1` as an intermediate fact. Use `h2` as an intermediate fact. Use `h3` as an intermediate fact. Use `h4` as an intermediate fact.

Use `h5` as an intermediate fact. Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Take `⟨hχc, hχadd, hχadd', hχ0, hχn, hχker⟩` from `chiR_laws (S := S) (T := T) hψ`. Establish `hfin : μ 𝓕 ≠ ⊤`. Take `⟨N, hN⟩` from `(GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov).2 (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)`.

Conclude with `(hN μ 𝓕 hμ h𝓕).2.1`. Establish `hmulχ : ∀ γ ∈ ratL T S, ∀ g, IsThetaFunO ψ S T g → A (chi ψ S T γ * g) = chi ψ S T γ * A g`. Introduce `γ hγ g hg`. Rewrite using `[← heisO_rat hγ hg, ← heisO_rat hγ (hAθ g hg)]`. Conclude with `hAc _ g hg`.

Establish `htp : ∀ (s : Finset (ratL T S)) (c : ratL T S → ℂ) g, IsThetaFunO ψ S T g → A ((∑ a ∈ s, c a • chiR ψ S T a) * g) = (∑ a ∈ s, c a • chiR ψ S T a) * A g`. Introduce `s c g hg`. Rewrite using `[Finset.sum_mul, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, smul_mul_assoc, map_smul]`.

Use `congr 1`. Conclude with `hmulχ a a.2 g hg`. Establish `hcomm : ∀ Φ, IsThetaFunO 1 S T Φ → ∀ g, IsThetaFunO ψ S T g → A (Φ * g) = Φ * A g`. Introduce `Φ hΦ g hg`. Establish `hAg` using `hAθ g hg`.

Take `⟨Bg, hBg0, hBg⟩` from `exists_bound hn hg`. Take `⟨Ba, hBa0, hBa⟩` from `exists_bound hn hAg`. Establish `hh : IsThetaFunO ψ S T (A (Φ * g) - Φ * A g)` using `isTheta_sub (hAθ _ (isTheta_one_mul hΦ hg)) (isTheta_one_mul hΦ hAg)`. Establish `hae : ∀ᵐ w ∂μ.restrict 𝓕, (A (Φ * g) - Φ * A g) w = 0`. Use `ae_zero_of_small (μ.restrict 𝓕) (M := (C : ℝ≥0∞) * (ENNReal.ofReal (Bg ^ 2) * μ 𝓕)) (N := ENNReal.ofReal (Ba ^ 2) * μ 𝓕) hh.cont.measurable ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)`. Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin`. Introduce `ε hε`. Take `⟨s, c, happ⟩` from `GlobalTheory.trigPoly_dense_periodic (WO S T) (ratL T S) K hK hcov (ratL T S) (chiR ψ S T) hχc hχadd hχadd' hχ0 hχn hχker Φ hΦ.cont (periodic_of_one hΦ) ε hε`. Take `⟨P, hPdef⟩ : ∃ P : WO S T → ℂ, P = ∑ a ∈ s, c a • chiR ψ S T a` from `⟨_, rfl⟩`.

Establish `hPθ : IsThetaFunO 1 S T P`. Rewrite using `[hPdef]`. Conclude with `isTheta_sum s _ fun a _ => isTheta_smul _ (isTheta_chi hψ a.2)`. Establish `hPA : A (P * g) = P * A g`. Rewrite using `[hPdef]`.

Conclude with `htp s c g hg`. Establish `hPapp : ∀ x, ‖(Φ - P) x‖ ≤ ε`. Introduce `x`. Rewrite using `[hPdef]`. Simplify `happ x` using `[Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Establish `hDθ : IsThetaFunO 1 S T (Φ - P)` using `isTheta_sub hΦ hPθ`. Use `⟨A ((Φ - P) * g), (Φ - P) * A g, (hAθ _ (isTheta_one_mul hDθ hg)).cont.measurable, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_mul, sub_mul, map_sub, hPA]`. Normalize the expressions using the abelian group laws. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_sq_le _ fun w => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, norm_mul]`. Conclude with `mul_le_mul (hPapp w) (hBg w) (norm_nonneg _) hε.le`. Use `_ = ENNReal.ofReal (ε ^ 2) * ((C : ℝ≥0∞) * (ENNReal.ofReal (Bg ^ 2) * μ 𝓕)) := by`. Rewrite using `[Measure.restrict_apply_univ]`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_sq_le _ fun w => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, norm_mul]`. Conclude with `mul_le_mul (hPapp w) (hBa w) (norm_nonneg _) hε.le`.

Use `_ = ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Ba ^ 2) * μ 𝓕) := by`. Rewrite using `[Measure.restrict_apply_univ]`. Establish `hz` using `GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hh.cont (norm_periodic' hn hh) hae`. Conclude with `sub_eq_zero.1 hz`. Take `⟨g, hg, hg0⟩` from `exists_theta_zero_ne hψ S T`.

Establish `hpt : ∀ f, IsThetaFunO ψ S T f → A f 0 = A g 0 / g 0 * f 0`. Introduce `f hf`. Establish `e1` using `hcomm (f * star g) (isTheta_mul_star hn hf hg) g hg`. Establish `e2` using `hcomm (g * star g) (isTheta_mul_star hn hg hg) f hf`. Establish `e3 : f * star g * g = g * star g * f` using `by ring`.

Rewrite `e1` using `[e3, e2]`. Establish `e0` using `congrFun e1 0`. Simplify using `only [Pi.mul_apply, Pi.star_apply] at e0`. Establish `hs : star (g 0) ≠ 0` using `star_ne_zero.2 hg0`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hg0]`.

Apply `mul_right_cancel₀ hs` to reduce the goal to its premises. Take the linear combination `e0`. Use `⟨A g 0 / g 0, fun f hf => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `h1` using `hpt (heisO ψ S T x f) (isTheta_heis hE hf x)`.

Rewrite `h1` using `[hAc x f hf, heisO_apply_zero, heisO_apply_zero]`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Conclude with `h1`.
-/
theorem schur (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : Schur ψ S T := by
  intro μ 𝓕 hμ h𝓕 A hAθ hAc hAb
  obtain ⟨C, hC⟩ := hAb
  have hE := isExpChar_of_isCharAF hψ
  have hn := hE.2.1
  have : μ.IsAddHaarMeasure := hμ
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hχc, hχadd, hχadd', hχ0, hχn, hχker⟩ := chiR_laws (S := S) (T := T) hψ
  have hfin : μ 𝓕 ≠ ⊤ := by
    obtain ⟨N, hN⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov).2
      (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    exact (hN μ 𝓕 hμ h𝓕).2.1

  have hmulχ : ∀ γ ∈ ratL T S, ∀ g, IsThetaFunO ψ S T g → A (chi ψ S T γ * g) = chi ψ S T γ * A g := by
    intro γ hγ g hg
    rw [← heisO_rat hγ hg, ← heisO_rat hγ (hAθ g hg)]
    exact hAc _ g hg
  have htp : ∀ (s : Finset (ratL T S)) (c : ratL T S → ℂ) g, IsThetaFunO ψ S T g →
      A ((∑ a ∈ s, c a • chiR ψ S T a) * g) = (∑ a ∈ s, c a • chiR ψ S T a) * A g := by
    intro s c g hg
    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul]
    congr 1
    exact hmulχ a a.2 g hg

  have hcomm : ∀ Φ, IsThetaFunO 1 S T Φ → ∀ g, IsThetaFunO ψ S T g → A (Φ * g) = Φ * A g := by
    intro Φ hΦ g hg
    have hAg := hAθ g hg
    obtain ⟨Bg, hBg0, hBg⟩ := exists_bound hn hg
    obtain ⟨Ba, hBa0, hBa⟩ := exists_bound hn hAg
    have hh : IsThetaFunO ψ S T (A (Φ * g) - Φ * A g) :=
      isTheta_sub (hAθ _ (isTheta_one_mul hΦ hg)) (isTheta_one_mul hΦ hAg)
    have hae : ∀ᵐ w ∂μ.restrict 𝓕, (A (Φ * g) - Φ * A g) w = 0 := by
      refine ae_zero_of_small (μ.restrict 𝓕) (M := (C : ℝ≥0∞) * (ENNReal.ofReal (Bg ^ 2) * μ 𝓕))
        (N := ENNReal.ofReal (Ba ^ 2) * μ 𝓕) hh.cont.measurable ?_ ?_ ?_
      · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
      intro ε hε
      obtain ⟨s, c, happ⟩ := GlobalTheory.trigPoly_dense_periodic (WO S T) (ratL T S) K hK hcov (ratL T S) (chiR ψ S T)
        hχc hχadd hχadd' hχ0 hχn hχker Φ hΦ.cont (periodic_of_one hΦ) ε hε
      obtain ⟨P, hPdef⟩ : ∃ P : WO S T → ℂ, P = ∑ a ∈ s, c a • chiR ψ S T a := ⟨_, rfl⟩
      have hPθ : IsThetaFunO 1 S T P := by
        rw [hPdef]
        exact isTheta_sum s _ fun a _ => isTheta_smul _ (isTheta_chi hψ a.2)
      have hPA : A (P * g) = P * A g := by
        rw [hPdef]
        exact htp s c g hg
      have hPapp : ∀ x, ‖(Φ - P) x‖ ≤ ε := by
        intro x
        rw [hPdef]
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using happ x
      have hDθ : IsThetaFunO 1 S T (Φ - P) := isTheta_sub hΦ hPθ
      refine ⟨A ((Φ - P) * g), (Φ - P) * A g, (hAθ _ (isTheta_one_mul hDθ hg)).cont.measurable, ?_, ?_, ?_⟩
      · rw [sub_mul, sub_mul, map_sub, hPA]
        abel
      · calc ∫⁻ w, ‖A ((Φ - P) * g) w‖ₑ ^ 2 ∂μ.restrict 𝓕
            ≤ (C : ℝ≥0∞) * ∫⁻ w, ‖((Φ - P) * g) w‖ₑ ^ 2 ∂μ.restrict 𝓕 := hC _ (isTheta_one_mul hDθ hg)
          _ ≤ (C : ℝ≥0∞) * (ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Bg ^ 2) * (μ.restrict 𝓕) Set.univ)) := by
              gcongr
              refine lintegral_sq_le _ fun w => ?_
              rw [Pi.mul_apply, norm_mul]
              exact mul_le_mul (hPapp w) (hBg w) (norm_nonneg _) hε.le
          _ = ENNReal.ofReal (ε ^ 2) * ((C : ℝ≥0∞) * (ENNReal.ofReal (Bg ^ 2) * μ 𝓕)) := by
              rw [Measure.restrict_apply_univ]
              ring
      · calc ∫⁻ w, ‖((Φ - P) * A g) w‖ₑ ^ 2 ∂μ.restrict 𝓕
            ≤ ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Ba ^ 2) * (μ.restrict 𝓕) Set.univ) := by
              refine lintegral_sq_le _ fun w => ?_
              rw [Pi.mul_apply, norm_mul]
              exact mul_le_mul (hPapp w) (hBa w) (norm_nonneg _) hε.le
          _ = ENNReal.ofReal (ε ^ 2) * (ENNReal.ofReal (Ba ^ 2) * μ 𝓕) := by
              rw [Measure.restrict_apply_univ]
    have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hh.cont
      (norm_periodic' hn hh) hae
    exact sub_eq_zero.1 hz

  obtain ⟨g, hg, hg0⟩ := exists_theta_zero_ne hψ S T
  have hpt : ∀ f, IsThetaFunO ψ S T f → A f 0 = A g 0 / g 0 * f 0 := by
    intro f hf
    have e1 := hcomm (f * star g) (isTheta_mul_star hn hf hg) g hg
    have e2 := hcomm (g * star g) (isTheta_mul_star hn hg hg) f hf
    have e3 : f * star g * g = g * star g * f := by ring
    rw [e3, e2] at e1
    have e0 := congrFun e1 0
    simp only [Pi.mul_apply, Pi.star_apply] at e0
    have hs : star (g 0) ≠ 0 := star_ne_zero.2 hg0
    rw [div_mul_eq_mul_div, eq_div_iff hg0]
    apply mul_right_cancel₀ hs
    linear_combination e0

  refine ⟨A g 0 / g 0, fun f hf => ?_⟩
  funext x
  have h1 := hpt (heisO ψ S T x f) (isTheta_heis hE hf x)
  rw [hAc x f hf, heisO_apply_zero, heisO_apply_zero] at h1
  rw [Pi.smul_apply, smul_eq_mul]
  exact h1

/- English proof (translation)
Proceed by induction on `Ls using List.reverseRecOn with`. Consider the case `nil`. Introduce `g hg`. Take `⟨Bg, hBg0, hBg⟩` from `exists_bound hψ.2.1 hg`. Use `⟨[[]], Bg, hBg0, by simp, ?_⟩` and prove the remaining obligations.

Introduce `Φ _ B hB hΦB w`. Establish `h1 : ‖Φ w‖ ≤ B` using `hΦB [] (by simp) w`. Use `show ‖Φ w * g w‖ ≤ Bg * B`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `append_singleton Ls L ih`. Introduce `g hg`. Establish `hL' : IsRealDir L` using `hL L (by simp)`. Establish `hLs : ∀ L ∈ Ls, IsRealDir L` using `fun L' h' => hL L' (by simp [h'])`. Take `⟨Ms1, C1, hC1, hM1, h1⟩` from `ih hLs g hg`.

Establish `hg'` using `(hasDerivAt_and_isTheta hψ hL' hg).2`. Take `⟨Ms2, C2, hC2, hM2, h2⟩` from `ih hLs _ hg'`. Use `⟨Ms1.map (· ++ [L]) ++ Ms2, C1 + C2, add_nonneg hC1 hC2, ?_, ?_⟩` and prove the remaining obligations. Introduce `M hM L'' hL''`. Break down `List.mem_append.1 hM with hM | hM` into its components or cases.

Take `⟨M', hM', rfl⟩` from `List.mem_map.1 hM`. Break down `List.mem_append.1 hL'' with h | h` into its components or cases. Conclude with `hM1 M' hM' L'' h`. Rewrite using `[List.mem_singleton.1 h]`. Conclude with `hL'`.

Conclude with `hM2 M hM L'' hL''`. Introduce `Φ hΦ B hB hΦB w`. Establish `hΦ'` using `(hasDerivAt_and_isTheta isExpChar_one hL' hΦ).2`. Establish `e : dHeisWord ψ S T (Ls ++ [L]) (Φ * g) = dHeisWord ψ S T Ls (dHeis 1 S T L Φ * g) + dHeisWord ψ S T Ls (Φ * dHeis ψ S T L g)`. Rewrite using `[dHeisWord_concat, dHeis_one_mul hψ hL' hΦ hg, dHeisWord_add hψ hLs (isTheta_one_mul hΦ' hg) (isTheta_one_mul hΦ hg')]`.

Establish `b1` using `h1 (dHeis 1 S T L Φ) hΦ' B hB (fun M hM w => by`. Rewrite using `[← dHeisWord_concat]`. Conclude with `hΦB _ (List.mem_append_left _ (List.mem_map.2 ⟨M, hM, rfl⟩)) w) w`. Establish `b2` using `h2 Φ hΦ B hB (fun M hM w => hΦB M (List.mem_append_right _ hM) w) w`. Rewrite using `[e, Pi.add_apply]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem word_bound (hψ : IsExpChar ψ) (Ls : List (ℝ →+ WO S T)) (hL : ∀ L ∈ Ls, IsRealDir L) :
    ∀ g, IsThetaFunO ψ S T g → ∃ (Ms : List (List (ℝ →+ WO S T))) (C : ℝ), 0 ≤ C ∧ (∀ M ∈ Ms, ∀ L ∈ M, IsRealDir L) ∧
      ∀ Φ, IsThetaFunO 1 S T Φ → ∀ B : ℝ, 0 ≤ B → (∀ M ∈ Ms, ∀ w, ‖dHeisWord 1 S T M Φ w‖ ≤ B) →
        ∀ w, ‖dHeisWord ψ S T Ls (Φ * g) w‖ ≤ C * B := by
  induction Ls using List.reverseRecOn with
  | nil =>
    intro g hg
    obtain ⟨Bg, hBg0, hBg⟩ := exists_bound hψ.2.1 hg
    refine ⟨[[]], Bg, hBg0, by simp, ?_⟩
    intro Φ _ B hB hΦB w
    have h1 : ‖Φ w‖ ≤ B := hΦB [] (by simp) w
    show ‖Φ w * g w‖ ≤ Bg * B
    rw [norm_mul]
    calc ‖Φ w‖ * ‖g w‖ ≤ B * Bg := mul_le_mul h1 (hBg w) (norm_nonneg _) hB
      _ = Bg * B := mul_comm _ _
  | append_singleton Ls L ih =>
    intro g hg
    have hL' : IsRealDir L := hL L (by simp)
    have hLs : ∀ L ∈ Ls, IsRealDir L := fun L' h' => hL L' (by simp [h'])
    obtain ⟨Ms1, C1, hC1, hM1, h1⟩ := ih hLs g hg
    have hg' := (hasDerivAt_and_isTheta hψ hL' hg).2
    obtain ⟨Ms2, C2, hC2, hM2, h2⟩ := ih hLs _ hg'
    refine ⟨Ms1.map (· ++ [L]) ++ Ms2, C1 + C2, add_nonneg hC1 hC2, ?_, ?_⟩
    · intro M hM L'' hL''
      rcases List.mem_append.1 hM with hM | hM
      · obtain ⟨M', hM', rfl⟩ := List.mem_map.1 hM
        rcases List.mem_append.1 hL'' with h | h
        · exact hM1 M' hM' L'' h
        · rw [List.mem_singleton.1 h]
          exact hL'
      · exact hM2 M hM L'' hL''
    · intro Φ hΦ B hB hΦB w
      have hΦ' := (hasDerivAt_and_isTheta isExpChar_one hL' hΦ).2
      have e : dHeisWord ψ S T (Ls ++ [L]) (Φ * g) =
          dHeisWord ψ S T Ls (dHeis 1 S T L Φ * g) + dHeisWord ψ S T Ls (Φ * dHeis ψ S T L g) := by
        rw [dHeisWord_concat, dHeis_one_mul hψ hL' hΦ hg,
          dHeisWord_add hψ hLs (isTheta_one_mul hΦ' hg) (isTheta_one_mul hΦ hg')]
      have b1 := h1 (dHeis 1 S T L Φ) hΦ' B hB (fun M hM w => by
        rw [← dHeisWord_concat]
        exact hΦB _ (List.mem_append_left _ (List.mem_map.2 ⟨M, hM, rfl⟩)) w) w
      have b2 := h2 Φ hΦ B hB (fun M hM w => hΦB M (List.mem_append_right _ hM) w) w
      rw [e, Pi.add_apply]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ C1 * B + C2 * B := add_le_add b1 b2
        _ = (C1 + C2) * B := by ring

/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => exact ⟨[], 0, le_rfl, by simp, fun _ _ _ _ _ _ hLs _ => by simp at hLs⟩`. Consider the case `cons Ls W ih`. Take `⟨Ms1, C1, hC1, hM1, h1⟩` from `word_bound hψ Ls (hW Ls (by simp)) g hg`. Take `⟨Ms2, C2, hC2, hM2, h2⟩` from `ih (fun Ls' h' => hW Ls' (by simp [h']))`.

Use `⟨Ms1 ++ Ms2, C1 + C2, add_nonneg hC1 hC2, ?_, ?_⟩` and prove the remaining obligations. Introduce `M hM`. Break down `List.mem_append.1 hM with h | h` into its components or cases. Use `exacts [hM1 M h, hM2 M h]`. Introduce `Φ hΦ B hB hΦB Ls' hLs' w`.

Break down `List.mem_cons.1 hLs' with rfl | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem words_bound (hψ : IsExpChar ψ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (W : List (List (ℝ →+ WO S T)))
    (hW : ∀ Ls ∈ W, ∀ L ∈ Ls, IsRealDir L) :
    ∃ (Ms : List (List (ℝ →+ WO S T))) (C : ℝ), 0 ≤ C ∧ (∀ M ∈ Ms, ∀ L ∈ M, IsRealDir L) ∧
      ∀ Φ, IsThetaFunO 1 S T Φ → ∀ B : ℝ, 0 ≤ B → (∀ M ∈ Ms, ∀ w, ‖dHeisWord 1 S T M Φ w‖ ≤ B) →
        ∀ Ls ∈ W, ∀ w, ‖dHeisWord ψ S T Ls (Φ * g) w‖ ≤ C * B := by
  induction W with
  | nil => exact ⟨[], 0, le_rfl, by simp, fun _ _ _ _ _ _ hLs _ => by simp at hLs⟩
  | cons Ls W ih =>
    obtain ⟨Ms1, C1, hC1, hM1, h1⟩ := word_bound hψ Ls (hW Ls (by simp)) g hg
    obtain ⟨Ms2, C2, hC2, hM2, h2⟩ := ih (fun Ls' h' => hW Ls' (by simp [h']))
    refine ⟨Ms1 ++ Ms2, C1 + C2, add_nonneg hC1 hC2, ?_, ?_⟩
    · intro M hM
      rcases List.mem_append.1 hM with h | h
      exacts [hM1 M h, hM2 M h]
    · intro Φ hΦ B hB hΦB Ls' hLs' w
      rcases List.mem_cons.1 hLs' with rfl | h
      · calc _ ≤ C1 * B := h1 Φ hΦ B hB (fun M hM => hΦB M (List.mem_append_left _ hM)) w
          _ ≤ (C1 + C2) * B := by nlinarith
      · calc _ ≤ C2 * B := h2 Φ hΦ B hB (fun M hM => hΦB M (List.mem_append_right _ hM)) Ls' h w
          _ ≤ (C1 + C2) * B := by nlinarith

/- English proof (translation)
Introduce `U hU`. Take `⟨V, hV, hVg⟩` from `hg.level`. Establish `hUV : IsOpen ((U ⊓ V : AddSubgroup (WO S T)) : Set (WO S T))`. Rewrite using `[AddSubgroup.coe_inf]`. Conclude with `hU.inter hV`.

Take `⟨words, C, hw, hC⟩` from `hℓ (U ⊓ V) hUV`. Take `⟨Ms, C', hC', hMs, hb⟩` from `words_bound hψ hg words hw`. Use `⟨Ms, C * C', hMs, ?_⟩` and prove the remaining obligations. Introduce `Φ hΦ hΦU B hB hΦB`. Establish `hlev : HasLevel ψ S T (U ⊓ V) (Φ * g)`.

Introduce `u hu hu0`. Rewrite using `[heisO_one_mul, hΦU u (AddSubgroup.mem_inf.1 hu).1 hu0, hVg u (AddSubgroup.mem_inf.1 hu).2 hu0]`. Use `hC (Φ * g) (isTheta_one_mul hΦ hg) hlev (C' * B) (mul_nonneg hC' hB) (hb Φ hΦ B hB hΦB)` as an intermediate fact. Simplify `this` using `[LinearMap.comp_apply, LinearMap.mulRight_apply, mul_assoc]`.
-/
theorem isThetaCont_mul (hψ : IsExpChar ψ) {ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hℓ : IsThetaCont ψ S T ℓ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : IsThetaCont 1 S T (ℓ ∘ₗ LinearMap.mulRight ℂ g) := by
  intro U hU
  obtain ⟨V, hV, hVg⟩ := hg.level
  have hUV : IsOpen ((U ⊓ V : AddSubgroup (WO S T)) : Set (WO S T)) := by
    rw [AddSubgroup.coe_inf]
    exact hU.inter hV
  obtain ⟨words, C, hw, hC⟩ := hℓ (U ⊓ V) hUV
  obtain ⟨Ms, C', hC', hMs, hb⟩ := words_bound hψ hg words hw
  refine ⟨Ms, C * C', hMs, ?_⟩
  intro Φ hΦ hΦU B hB hΦB
  have hlev : HasLevel ψ S T (U ⊓ V) (Φ * g) := by
    intro u hu hu0
    rw [heisO_one_mul, hΦU u (AddSubgroup.mem_inf.1 hu).1 hu0, hVg u (AddSubgroup.mem_inf.1 hu).2 hu0]
  have := hC (Φ * g) (isTheta_one_mul hΦ hg) hlev (C' * B) (mul_nonneg hC' hB) (hb Φ hΦ B hB hΦB)
  simpa [LinearMap.comp_apply, LinearMap.mulRight_apply, mul_assoc] using this

def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (Φ : WO S T → ℂ)
    (γ : WO S T) : ℂ :=
  ∫ y in 𝓕, Φ y * starRingEnd ℂ (chi ψ S T γ y) ∂μ

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, K, hK, hcov⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `h1` as an intermediate fact. Use `h2` as an intermediate fact. Use `h3` as an intermediate fact. Use `h4` as an intermediate fact.

Use `h5` as an intermediate fact. Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Take `⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, -⟩` from `GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov`. Take `⟨hχc, hχadd, hχadd', hχ0, hχn, hχker⟩` from `chiR_laws (S := S) (T := T) hψ`. Establish `hE1 : IsExpChar (1 : AddChar (AF D.host.F) ℂ)` using `isExpChar_one`.

Set `cf : (WO S T → ℂ) → ratL T S → ℂ` to `fun Ψ a => ∫ y in 𝓕, Ψ y * starRingEnd ℂ (chiR ψ S T a y) ∂μ`. Set `tr : Finset (ratL T S) → (ratL T S → ℂ) → (WO S T → ℂ) → WO S T → ℂ` to `fun s c Ψ => ∑ a ∈ s, (c a * cf Ψ a) • chiR ψ S T a`. Establish `tr_apply : ∀ s c Ψ x, tr s c Ψ x = ∑ a ∈ s, c a * (cf Ψ a * chiR ψ S T a x)`. Introduce `s c Ψ x`. Simplify using `only [tr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]`.

Establish `tr_theta : ∀ s c Ψ, IsThetaFunO 1 S T (tr s c Ψ)` using `fun s c Ψ => isTheta_sum s _ fun a _ => isTheta_smul _ (isTheta_chi hψ a.2)`. Establish `hper : ∀ Ψ, IsThetaFunO 1 S T Ψ → Continuous Ψ ∧ ∀ γ ∈ ratL T S, ∀ x, Ψ (γ + x) = Ψ x` using `fun Ψ hΨ => ⟨hΨ.cont, periodic_of_one hΨ⟩`. Establish `claws` using `fun (a : ratL T S) (Ψ : WO S T → ℂ) (hΨ : IsThetaFunO 1 S T Ψ) => GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt (WO S T) (ratL T S) K hK hcov μ 𝓕 hμ h𝓕 (chiR ψ S T a) (hχc a) (hχadd a) (hχn a) (fun γ hγ => chi_rat hψ a.2 hγ) Ψ (hper Ψ hΨ).1 (hper Ψ hΨ).2`. Establish `tr_dHeis : ∀ s c (L : ℝ →+ WO S T), IsRealDir L → ∀ Ψ, IsThetaFunO 1 S T Ψ → dHeis 1 S T L (tr s c Ψ) = tr s c (dHeis 1 S T L Ψ)`. Introduce `s c L hL Ψ hΨ`.

Establish `hd` using `hasDerivAt_and_isTheta hE1 hL hΨ`. Use function extensionality and compare the values at `x`. Establish `hline : ∀ w, HasDerivAt (fun t : ℝ => Ψ (w + L t)) (dHeis 1 S T L Ψ w) 0`. Introduce `w`. Establish `hw` using `hd.1 w`.

Simplify using `only [heisO_one_apply] at hw`. Conclude with `hw`. Establish `hsum : HasDerivAt (fun t : ℝ => tr s c Ψ (x + L t)) (tr s c (dHeis 1 S T L Ψ) x) 0`. Establish `hterm : ∀ a ∈ s, HasDerivAt (fun t : ℝ => c a * (cf Ψ a * chiR ψ S T a (x + L t))) (c a * (cf (dHeis 1 S T L Ψ) a * chiR ψ S T a x)) 0` using `fun a _ => ((claws a Ψ hΨ).2 L _ (hper _ hd.2).1 (hper _ hd.2).2 hline x).const_mul (c a)`. Simplify using `only [tr_apply]`.

Establish `hs'` using `HasDerivAt.sum hterm`. Rewrite `hs'` using `[Finset.sum_fn]`. Conclude with `hs'`. Establish `e : (fun t : ℝ => heisO 1 S T (L t) (tr s c Ψ) x) = fun t => tr s c Ψ (x + L t)`. Use function extensionality and compare the values at `t`.

Rewrite using `[heisO_one_apply]`. Use `show deriv (fun t : ℝ => heisO 1 S T (L t) (tr s c Ψ) x) 0 = _`. Rewrite using `[e]`. Conclude with `hsum.deriv`. Take `⟨V, hV, hVΦ⟩` from `hΦ.level`.

Establish `hfix : ∀ u ∈ V, u.map (infPart D) = 0 → ∀ y, Φ (u + y) = Φ y`. Introduce `u hu hu0 y`. Establish `hy` using `congrFun (hVΦ u hu hu0) y`. Rewrite `hy` using `[heisO_one_apply, add_comm]`. Conclude with `hy`.

Establish `tr_level : ∀ s c, HasLevel 1 S T V (tr s c Φ)`. Introduce `s c u hu hu0`. Use function extensionality and compare the values at `w`. Rewrite using `[heisO_one_apply, tr_apply, tr_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Establish `hconv` using `(claws a Φ hΦ).1 u`. Simplify using `only [hfix u hu hu0] at hconv`. Establish `hconv' : cf Φ a * chiR ψ S T a u = cf Φ a` using `hconv`. Rewrite using `[hχadd a w u]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨words, C, hw, hC⟩` from `hm V hV`. Establish `hbound : ∀ ε : ℝ, 0 < ε → ‖m Φ - κ * Φ 0‖ ≤ (C + ‖κ‖) * ε`. Introduce `ε hε`. Establish `hl : ∀ Ψ ∈ (Φ :: words.map fun M => dHeisWord 1 S T M Φ), Continuous Ψ ∧ ∀ γ ∈ ratL T S, ∀ x, Ψ (γ + x) = Ψ x`.

Introduce `Ψ hΨ`. Break down `List.mem_cons.1 hΨ with rfl | hΨ` into its components or cases. Conclude with `hper _ hΦ`. Take `⟨M, hM, rfl⟩` from `List.mem_map.1 hΨ`. Conclude with `hper _ (isTheta_dHeisWord hE1 (hw M hM) hΦ)`.

Take `⟨s, c, happ⟩` from `GlobalTheory.exists_summation_kernel_periodic (WO S T) (ratL T S) K hK hcov (ratL T S) (chiR ψ S T) hχc hχadd hχadd' hχ0 hχn hχker μ 𝓕 hμ h𝓕 _ hl ε hε`. Establish `tr_word : ∀ M : List (ℝ →+ WO S T), (∀ L ∈ M, IsRealDir L) → ∀ Ψ, IsThetaFunO 1 S T Ψ → dHeisWord 1 S T M (tr s c Ψ) = tr s c (dHeisWord 1 S T M Ψ)`. Introduce `M`. Proceed by induction on `M using List.reverseRecOn with`. Consider the case `nil => intro _ Ψ _`.

Both sides reduce to the same expression. Consider the case `append_singleton M L ih`. Introduce `hML Ψ hΨ`. Establish `hL : IsRealDir L` using `hML L (by simp)`. Rewrite using `[dHeisWord_concat, dHeisWord_concat, tr_dHeis s c L hL Ψ hΨ, ih (fun L' h' => hML L' (by simp [h'])) _ (hasDerivAt_and_isTheta hE1 hL hΨ).2]`.

Establish `hRθ : IsThetaFunO 1 S T (Φ - tr s c Φ)` using `isTheta_sub hΦ (tr_theta s c Φ)`. Establish `hRlev : HasLevel 1 S T V (Φ - tr s c Φ)`. Introduce `u hu hu0`. Use function extensionality and compare the values at `w`. Establish `a2` using `congrFun (tr_level s c u hu hu0) w`.

Rewrite `a2` using `[heisO_one_apply]`. Rewrite using `[heisO_one_apply, Pi.sub_apply, Pi.sub_apply, a2, add_comm, hfix u hu hu0]`. Establish `eR : Φ - tr s c Φ = Φ + (-1 : ℂ) • tr s c Φ`. Rewrite using `[neg_one_smul, sub_eq_add_neg]`. Establish `hRder : ∀ M ∈ words, ∀ w, ‖dHeisWord 1 S T M (Φ - tr s c Φ) w‖ ≤ ε`.

Introduce `M hM w`. Establish `e : dHeisWord 1 S T M (Φ - tr s c Φ) = dHeisWord 1 S T M Φ - tr s c (dHeisWord 1 S T M Φ)`. Rewrite using `[eR, dHeisWord_add hE1 (hw M hM) hΦ (isTheta_smul _ (tr_theta s c Φ)), dHeisWord_smul, tr_word M (hw M hM) Φ hΦ, neg_one_smul, ← sub_eq_add_neg]`. Rewrite using `[e, Pi.sub_apply, tr_apply]`. Conclude with `happ _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨M, hM, rfl⟩)) w`.

Establish `hmR` using `hC _ hRθ hRlev ε hε.le hRder`. Establish `h0 : ‖Φ 0 - tr s c Φ 0‖ ≤ ε`. Rewrite using `[tr_apply]`. Conclude with `happ Φ List.mem_cons_self 0`. Establish `hmT : m (tr s c Φ) = κ * tr s c Φ 0`.

Rewrite using `[tr_apply]`. Simplify using `only [tr, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[show chiR ψ S T a = chi ψ S T a from rfl, hκ _ a.2, chi_zero]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : m Φ - κ * Φ 0 = m (Φ - tr s c Φ) - κ * (Φ 0 - tr s c Φ 0)`. Rewrite using `[map_sub, hmT]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `_ ≤ C * ε + ‖κ‖ * ε := by gcongr`. Use `_ = (C + ‖κ‖) * ε := by ring`. Establish `hz : ‖m Φ - κ * Φ 0‖ = 0`.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖m Φ - κ * Φ 0‖` using `lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)`. Establish `hKpos : 0 < |C| + ‖κ‖ + 1` using `by positivity`. Establish `hb` using `hbound (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) (by positivity)`. Establish `hCle : C + ‖κ‖ ≤ |C| + ‖κ‖ + 1` using `by linarith [le_abs_self C]`.

Establish `hmono : (C + ‖κ‖) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) ≤ (|C| + ‖κ‖ + 1) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1)))` using `by gcongr`. Establish `e : (|C| + ‖κ‖ + 1) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) = ‖m Φ - κ * Φ 0‖ / 2`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `sub_eq_zero.1 (norm_eq_zero.1 hz)`.
-/
theorem eq_mul_of_chi (hψ : IsCharAF D.host.F ψ) {m : (WO S T → ℂ) →ₗ[ℂ] ℂ} (hm : IsThetaCont 1 S T m) {κ : ℂ}
    (hκ : ∀ γ ∈ ratL T S, m (chi ψ S T γ) = κ) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO 1 S T Φ) : m Φ = κ * Φ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov
  obtain ⟨hχc, hχadd, hχadd', hχ0, hχn, hχker⟩ := chiR_laws (S := S) (T := T) hψ
  have hE1 : IsExpChar (1 : AddChar (AF D.host.F) ℂ) := isExpChar_one

  let cf : (WO S T → ℂ) → ratL T S → ℂ := fun Ψ a => ∫ y in 𝓕, Ψ y * starRingEnd ℂ (chiR ψ S T a y) ∂μ
  let tr : Finset (ratL T S) → (ratL T S → ℂ) → (WO S T → ℂ) → WO S T → ℂ :=
    fun s c Ψ => ∑ a ∈ s, (c a * cf Ψ a) • chiR ψ S T a
  have tr_apply : ∀ s c Ψ x, tr s c Ψ x = ∑ a ∈ s, c a * (cf Ψ a * chiR ψ S T a x) := by
    intro s c Ψ x
    simp only [tr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have tr_theta : ∀ s c Ψ, IsThetaFunO 1 S T (tr s c Ψ) := fun s c Ψ =>
    isTheta_sum s _ fun a _ => isTheta_smul _ (isTheta_chi hψ a.2)
  have hper : ∀ Ψ, IsThetaFunO 1 S T Ψ → Continuous Ψ ∧ ∀ γ ∈ ratL T S, ∀ x, Ψ (γ + x) = Ψ x :=
    fun Ψ hΨ => ⟨hΨ.cont, periodic_of_one hΨ⟩

  have claws := fun (a : ratL T S) (Ψ : WO S T → ℂ) (hΨ : IsThetaFunO 1 S T Ψ) =>
    GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt (WO S T) (ratL T S) K hK hcov μ 𝓕 hμ h𝓕
      (chiR ψ S T a) (hχc a) (hχadd a) (hχn a) (fun γ hγ => chi_rat hψ a.2 hγ) Ψ (hper Ψ hΨ).1 (hper Ψ hΨ).2

  have tr_dHeis : ∀ s c (L : ℝ →+ WO S T), IsRealDir L → ∀ Ψ, IsThetaFunO 1 S T Ψ →
      dHeis 1 S T L (tr s c Ψ) = tr s c (dHeis 1 S T L Ψ) := by
    intro s c L hL Ψ hΨ
    have hd := hasDerivAt_and_isTheta hE1 hL hΨ
    funext x
    have hline : ∀ w, HasDerivAt (fun t : ℝ => Ψ (w + L t)) (dHeis 1 S T L Ψ w) 0 := by
      intro w
      have hw := hd.1 w
      simp only [heisO_one_apply] at hw
      exact hw
    have hsum : HasDerivAt (fun t : ℝ => tr s c Ψ (x + L t)) (tr s c (dHeis 1 S T L Ψ) x) 0 := by
      have hterm : ∀ a ∈ s, HasDerivAt (fun t : ℝ => c a * (cf Ψ a * chiR ψ S T a (x + L t)))
          (c a * (cf (dHeis 1 S T L Ψ) a * chiR ψ S T a x)) 0 := fun a _ =>
        ((claws a Ψ hΨ).2 L _ (hper _ hd.2).1 (hper _ hd.2).2 hline x).const_mul (c a)
      simp only [tr_apply]
      have hs' := HasDerivAt.sum hterm
      rw [Finset.sum_fn] at hs'
      exact hs'
    have e : (fun t : ℝ => heisO 1 S T (L t) (tr s c Ψ) x) = fun t => tr s c Ψ (x + L t) := by
      funext t
      rw [heisO_one_apply]
    show deriv (fun t : ℝ => heisO 1 S T (L t) (tr s c Ψ) x) 0 = _
    rw [e]
    exact hsum.deriv
  obtain ⟨V, hV, hVΦ⟩ := hΦ.level
  have hfix : ∀ u ∈ V, u.map (infPart D) = 0 → ∀ y, Φ (u + y) = Φ y := by
    intro u hu hu0 y
    have hy := congrFun (hVΦ u hu hu0) y
    rw [heisO_one_apply, add_comm] at hy
    exact hy

  have tr_level : ∀ s c, HasLevel 1 S T V (tr s c Φ) := by
    intro s c u hu hu0
    funext w
    rw [heisO_one_apply, tr_apply, tr_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hconv := (claws a Φ hΦ).1 u
    simp only [hfix u hu hu0] at hconv
    have hconv' : cf Φ a * chiR ψ S T a u = cf Φ a := hconv
    rw [hχadd a w u]
    congr 1
    calc cf Φ a * (chiR ψ S T a w * chiR ψ S T a u) = chiR ψ S T a w * (cf Φ a * chiR ψ S T a u) := by ring
      _ = cf Φ a * chiR ψ S T a w := by rw [hconv']; ring
  obtain ⟨words, C, hw, hC⟩ := hm V hV
  have hbound : ∀ ε : ℝ, 0 < ε → ‖m Φ - κ * Φ 0‖ ≤ (C + ‖κ‖) * ε := by
    intro ε hε
    have hl : ∀ Ψ ∈ (Φ :: words.map fun M => dHeisWord 1 S T M Φ),
        Continuous Ψ ∧ ∀ γ ∈ ratL T S, ∀ x, Ψ (γ + x) = Ψ x := by
      intro Ψ hΨ
      rcases List.mem_cons.1 hΨ with rfl | hΨ
      · exact hper _ hΦ
      · obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hΨ
        exact hper _ (isTheta_dHeisWord hE1 (hw M hM) hΦ)
    obtain ⟨s, c, happ⟩ := GlobalTheory.exists_summation_kernel_periodic (WO S T) (ratL T S) K hK hcov (ratL T S)
      (chiR ψ S T) hχc hχadd hχadd' hχ0 hχn hχker μ 𝓕 hμ h𝓕 _ hl ε hε
    have tr_word : ∀ M : List (ℝ →+ WO S T), (∀ L ∈ M, IsRealDir L) → ∀ Ψ, IsThetaFunO 1 S T Ψ →
        dHeisWord 1 S T M (tr s c Ψ) = tr s c (dHeisWord 1 S T M Ψ) := by
      intro M
      induction M using List.reverseRecOn with
      | nil => intro _ Ψ _; rfl
      | append_singleton M L ih =>
        intro hML Ψ hΨ
        have hL : IsRealDir L := hML L (by simp)
        rw [dHeisWord_concat, dHeisWord_concat, tr_dHeis s c L hL Ψ hΨ,
          ih (fun L' h' => hML L' (by simp [h'])) _ (hasDerivAt_and_isTheta hE1 hL hΨ).2]
    have hRθ : IsThetaFunO 1 S T (Φ - tr s c Φ) := isTheta_sub hΦ (tr_theta s c Φ)
    have hRlev : HasLevel 1 S T V (Φ - tr s c Φ) := by
      intro u hu hu0
      funext w
      have a2 := congrFun (tr_level s c u hu hu0) w
      rw [heisO_one_apply] at a2
      rw [heisO_one_apply, Pi.sub_apply, Pi.sub_apply, a2, add_comm, hfix u hu hu0]
    have eR : Φ - tr s c Φ = Φ + (-1 : ℂ) • tr s c Φ := by
      rw [neg_one_smul, sub_eq_add_neg]
    have hRder : ∀ M ∈ words, ∀ w, ‖dHeisWord 1 S T M (Φ - tr s c Φ) w‖ ≤ ε := by
      intro M hM w
      have e : dHeisWord 1 S T M (Φ - tr s c Φ) = dHeisWord 1 S T M Φ - tr s c (dHeisWord 1 S T M Φ) := by
        rw [eR, dHeisWord_add hE1 (hw M hM) hΦ (isTheta_smul _ (tr_theta s c Φ)), dHeisWord_smul,
          tr_word M (hw M hM) Φ hΦ, neg_one_smul, ← sub_eq_add_neg]
      rw [e, Pi.sub_apply, tr_apply]
      exact happ _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨M, hM, rfl⟩)) w
    have hmR := hC _ hRθ hRlev ε hε.le hRder
    have h0 : ‖Φ 0 - tr s c Φ 0‖ ≤ ε := by
      rw [tr_apply]
      exact happ Φ List.mem_cons_self 0
    have hmT : m (tr s c Φ) = κ * tr s c Φ 0 := by
      rw [tr_apply]
      simp only [tr, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show chiR ψ S T a = chi ψ S T a from rfl, hκ _ a.2, chi_zero]
      ring
    have e2 : m Φ - κ * Φ 0 = m (Φ - tr s c Φ) - κ * (Φ 0 - tr s c Φ 0) := by
      rw [map_sub, hmT]
      ring
    rw [e2]
    calc ‖m (Φ - tr s c Φ) - κ * (Φ 0 - tr s c Φ 0)‖ ≤ ‖m (Φ - tr s c Φ)‖ + ‖κ‖ * ‖Φ 0 - tr s c Φ 0‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ C * ε + ‖κ‖ * ε := by gcongr
      _ = (C + ‖κ‖) * ε := by ring

  have hz : ‖m Φ - κ * Φ 0‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖m Φ - κ * Φ 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hKpos : 0 < |C| + ‖κ‖ + 1 := by positivity
    have hb := hbound (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) (by positivity)
    have hCle : C + ‖κ‖ ≤ |C| + ‖κ‖ + 1 := by linarith [le_abs_self C]
    have hmono : (C + ‖κ‖) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) ≤
        (|C| + ‖κ‖ + 1) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) := by
      gcongr
    have e : (|C| + ‖κ‖ + 1) * (‖m Φ - κ * Φ 0‖ / (2 * (|C| + ‖κ‖ + 1))) = ‖m Φ - κ * Φ 0‖ / 2 := by
      field_simp
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

/- English proof (translation)
Introduce `ℓ hinv hℓ`. Establish `hE` using `isExpChar_of_isCharAF hψ`. Take `⟨g, hg, hg0⟩` from `exists_theta_zero_ne hψ S T`. Establish `hmul : ∀ h, IsThetaFunO ψ S T h → ∀ Φ, IsThetaFunO 1 S T Φ → ℓ (Φ * h) = ℓ h * Φ 0`. Introduce `h hh Φ hΦ`.

Establish `key` using `eq_mul_of_chi (m := ℓ ∘ₗ LinearMap.mulRight ℂ h) (κ := ℓ h) hψ (isThetaCont_mul hE hℓ hh) ?_ hΦ`. Simplify using `using key`. Introduce `γ hγ`. Take `⟨γ', rfl⟩` from `hγ`. Express the relevant statement in the definitionally equal form `ℓ (chi ψ S T _ * h) = ℓ h`.

Rewrite using `[← heisO_rat ⟨γ', rfl⟩ hh]`. Conclude with `hinv γ' h hh`. Use `⟨ℓ g / g 0, fun f hf => ?_⟩` and prove the remaining obligations. Establish `e1` using `hmul g hg (f * star g) (isTheta_mul_star hE.2.1 hf hg)`. Establish `e2` using `hmul f hf (g * star g) (isTheta_mul_star hE.2.1 hg hg)`.

Establish `e3 : f * star g * g = g * star g * f` using `by ring`. Rewrite `e1` using `[e3, e2]`. Simplify using `only [Pi.mul_apply, Pi.star_apply] at e1`. Establish `hs : star (g 0) ≠ 0` using `star_ne_zero.2 hg0`. Establish `e4 : ℓ f * g 0 = ℓ g * f 0`.

Apply `mul_right_cancel₀ hs` to reduce the goal to its premises. Take the linear combination `e1`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hg0]`. Conclude with `e4`.
-/
theorem thetaUnique (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : ThetaUnique ψ S T := by
  intro ℓ hinv hℓ
  have hE := isExpChar_of_isCharAF hψ
  obtain ⟨g, hg, hg0⟩ := exists_theta_zero_ne hψ S T

  have hmul : ∀ h, IsThetaFunO ψ S T h → ∀ Φ, IsThetaFunO 1 S T Φ → ℓ (Φ * h) = ℓ h * Φ 0 := by
    intro h hh Φ hΦ
    have key := eq_mul_of_chi (m := ℓ ∘ₗ LinearMap.mulRight ℂ h) (κ := ℓ h) hψ (isThetaCont_mul hE hℓ hh) ?_ hΦ
    · simpa using key
    intro γ hγ
    obtain ⟨γ', rfl⟩ := hγ
    change ℓ (chi ψ S T _ * h) = ℓ h
    rw [← heisO_rat ⟨γ', rfl⟩ hh]
    exact hinv γ' h hh
  refine ⟨ℓ g / g 0, fun f hf => ?_⟩

  have e1 := hmul g hg (f * star g) (isTheta_mul_star hE.2.1 hf hg)
  have e2 := hmul f hf (g * star g) (isTheta_mul_star hE.2.1 hg hg)
  have e3 : f * star g * g = g * star g * f := by ring
  rw [e3, e2] at e1
  simp only [Pi.mul_apply, Pi.star_apply] at e1
  have hs : star (g 0) ≠ 0 := star_ne_zero.2 hg0
  have e4 : ℓ f * g 0 = ℓ g * f 0 := by
    apply mul_right_cancel₀ hs
    linear_combination e1
  rw [div_mul_eq_mul_div, eq_div_iff hg0]
  exact e4

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, K, hK, hcov⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `h1` as an intermediate fact. Use `h2` as an intermediate fact. Use `h3` as an intermediate fact. Use `h4` as an intermediate fact.

Use `h5` as an intermediate fact. Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Take `⟨⟨μ, 𝓕, hμ, h𝓕, hvol⟩, -⟩` from `GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov`. Conclude with `⟨μ, 𝓕, hμ, h𝓕, hvol⟩`.
-/
theorem covolOneExists (S T : HSp D) : CovolOneExists S T := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, hvol⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hcov
  exact ⟨μ, 𝓕, hμ, h𝓕, hvol⟩

/- English proof (translation)
Introduce `μ μ' 𝓕 𝓕' hc hc' f f' hf hf'`. Take `⟨h1, h2, h3, h4, h5, K, hK, hcov⟩` from `GlobalTheory.AdelicMatrixLattice.lattice D T S`. Use `h1` as an intermediate fact. Use `h2` as an intermediate fact. Use `h3` as an intermediate fact.

Use `h4` as an intermediate fact. Use `h5` as an intermediate fact. Establish `: BorelSpace (WO S T)` using `⟨rfl⟩`. Establish `hn` using `(isExpChar_of_isCharAF hψ).2.1`. Establish `hΦ` using `isTheta_mul_star hn hf hf'`.

Take `⟨hμ, h𝓕, hv⟩` from `hc`. Take `⟨hμ', h𝓕', hv'⟩` from `hc'`. Establish `key` using `GlobalTheory.mean_periodic_indep_of_covolume_one (WO S T) (ratL T S) K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 hv hμ' h𝓕' hv' (f * star f') hΦ.cont (periodic_of_one hΦ)`. Establish `key'` using `GlobalTheory.mean_periodic_indep_of_covolume_one (WO S T) (ratL T S) K hK hcov μ' μ 𝓕' 𝓕 hμ' h𝓕' hv' hμ h𝓕 hv (f * star f') hΦ.cont (periodic_of_one hΦ)`. Simplify using `only [heisO_apply_zero]`.

Conclude with `⟨key.1, key'.1, key.2⟩`.
-/
theorem heisenbergLemma (hψ : IsCharAF D.host.F ψ) (S T : HSp D) : HeisenbergLemma ψ S T := by
  intro μ μ' 𝓕 𝓕' hc hc' f f' hf hf'
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have := h1
  have := h2
  have := h3
  have := h4
  have := h5
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have hn := (isExpChar_of_isCharAF hψ).2.1
  have hΦ := isTheta_mul_star hn hf hf'
  obtain ⟨hμ, h𝓕, hv⟩ := hc
  obtain ⟨hμ', h𝓕', hv'⟩ := hc'

  have key := GlobalTheory.mean_periodic_indep_of_covolume_one (WO S T) (ratL T S) K hK hcov μ μ' 𝓕 𝓕' hμ h𝓕 hv hμ' h𝓕'
    hv' (f * star f') hΦ.cont (periodic_of_one hΦ)
  have key' := GlobalTheory.mean_periodic_indep_of_covolume_one (WO S T) (ratL T S) K hK hcov μ' μ 𝓕' 𝓕 hμ' h𝓕' hv' hμ h𝓕
    hv (f * star f') hΦ.cont (periodic_of_one hΦ)
  simp only [heisO_apply_zero]
  exact ⟨key.1, key'.1, key.2⟩

/- English proof (translation)
Introduce `ψ hψ S T`. Use `⟨schur hψ S T, thetaUnique hψ S T, ⟨covolOneExists S T, heisenbergLemma hψ S T⟩, ?_⟩` and prove the remaining obligations. Take `⟨g, hg, h0⟩` from `exists_theta_zero_ne hψ S T`. Conclude with `⟨g, hg, fun h => h0 (by simp [h])⟩`.
-/
theorem thetaFacts (D : D7) : ThetaFacts D := by
  intro ψ hψ S T
  refine ⟨schur hψ S T, thetaUnique hψ S T, ⟨covolOneExists S T, heisenbergLemma hψ S T⟩, ?_⟩
  obtain ⟨g, hg, h0⟩ := exists_theta_zero_ne hψ S T
  exact ⟨g, hg, fun h => h0 (by simp [h])⟩

end GlobalTheory.ThetaAllChar

end
