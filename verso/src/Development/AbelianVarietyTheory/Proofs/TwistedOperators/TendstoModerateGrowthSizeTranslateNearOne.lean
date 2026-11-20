import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.NearOne

variable {D : D7} {θ : InfFam D} {V : HSp D}

/- English proof (translation)
Take `⟨L, hL, hexp, hlog⟩` from `GlobalTheory.ConjMult.hasLogAt (V := V) τ`. Establish `hJ` using `GlobalTheory.SmoothAutCheck.gramAt_unit V τ`. Establish `h0 : L 1 = 0`. Establish `h` using `hlog.self_of_nhds`. Simplify using `using h`.

Use `⟨fun u => (L u).1, fun u => (L u).2, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Filter.Tendsto L (𝓝 1) (𝓝 0)` using `h0 ▸ hL.continuousAt.tendsto`. Conclude with `(continuous_subtype_val.tendsto _).comp hc`. Use `filter_upwards [nhdsWithin_le_nhds hexp, self_mem_nhdsWithin] with u hu hmem`. Conclude with `hu ((GlobalTheory.ConjMult.unit_iffM hJ u).2 hmem)`.
-/
theorem exists_log (V : HSp D) (τ : D.what₂.Tau) :
    ∃ Λ : Matrix (Fin V.rank) (Fin V.rank) ℂ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ u, Λ u ∈ lieAt V τ) ∧
      Tendsto Λ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ u in 𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1, NormedSpace.exp (Λ u) = u := by
  obtain ⟨L, hL, hexp, hlog⟩ := GlobalTheory.ConjMult.hasLogAt (V := V) τ
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have h0 : L 1 = 0 := by
    have h := hlog.self_of_nhds
    simpa using h
  refine ⟨fun u => (L u).1, fun u => (L u).2, ?_, ?_⟩
  · have hc : Filter.Tendsto L (𝓝 1) (𝓝 0) := h0 ▸ hL.continuousAt.tendsto
    exact (continuous_subtype_val.tendsto _).comp hc
  · filter_upwards [nhdsWithin_le_nhds hexp, self_mem_nhdsWithin] with u hu hmem
    exact hu ((GlobalTheory.ConjMult.unit_iffM hJ u).2 hmem)

/- English proof (translation)
Set `_ : NormedRing (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedRing`. Set `_ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Set `_ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ)` to `.restrictScalars ℚ ℂ _`. Establish `_ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ)` using `FiniteDimensional.complete ℂ _`. Conclude with `NormedSpace.exp_continuous`.
-/
private theorem continuous_matrix_exp' (n : ℕ) : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp M) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := .restrictScalars ℚ ℂ _
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact NormedSpace.exp_continuous

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

/- English proof (translation)
Establish `hl` using `height_laws (V := V)`. Establish `hexp : Continuous (fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => NormedSpace.exp M)` using `continuous_matrix_exp' V.rank`. Set `F : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ → ℝ` to `fun p => height V (atTau θ V τ (NormedSpace.exp (p.2 • p.1.1)))`. Establish `hF : Continuous F`. Establish `hin : Continuous fun p : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ => NormedSpace.exp (p.2 • p.1.1)` using `hexp.comp (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))`.

Conclude with `hl.2.2.2.2.comp ((GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hin fun p => GlobalTheory.Mem.Lift.exp_mem p.1.2 p.2)`. Establish `h0mem : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ` using `by show (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ + gramAt D V τ * 0 = 0`. Simplify using the standard rewrite rules. Establish `hF0 : ∀ t : ℝ, F (⟨0, h0mem⟩, t) = 1`. Introduce `t`.

Use `show height V (atTau θ V τ (NormedSpace.exp (t • (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) = 1`. Rewrite using `[smul_zero, NormedSpace.exp_zero, (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.1, hl.2.1]`. Establish `hev : ∀ᶠ x in 𝓝 (⟨0, h0mem⟩ : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ}), ∀ t ∈ Set.Icc (0 : ℝ) 1, F (x, t) ≤ 2`. Use `isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_` and prove the remaining obligations. Establish `hlt : F (⟨0, h0mem⟩, t) < 2` using `by rw [hF0]; norm_num`.

Conclude with `(hF.continuousAt.eventually (gt_mem_nhds hlt)).mono fun z hz => hz.le`. Rewrite `hev` using `[nhds_subtype, Filter.eventually_comap]`. Use `filter_upwards [hev] with X hX hXl t ht`. Conclude with `hX ⟨X, hXl⟩ rfl t ht`.
-/
theorem exists_height_le (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2 := by
  have hl := height_laws (V := V)
  have hexp : Continuous (fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => NormedSpace.exp M) := continuous_matrix_exp' V.rank
  let F : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ → ℝ :=
    fun p => height V (atTau θ V τ (NormedSpace.exp (p.2 • p.1.1)))
  have hF : Continuous F := by
    have hin : Continuous fun p : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ =>
        NormedSpace.exp (p.2 • p.1.1) :=
      hexp.comp (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))
    exact hl.2.2.2.2.comp ((GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hin
      fun p => GlobalTheory.Mem.Lift.exp_mem p.1.2 p.2)
  have h0mem : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ := by
    show (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ + gramAt D V τ * 0 = 0
    simp
  have hF0 : ∀ t : ℝ, F (⟨0, h0mem⟩, t) = 1 := by
    intro t
    show height V (atTau θ V τ (NormedSpace.exp (t • (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) = 1
    rw [smul_zero, NormedSpace.exp_zero, (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.1, hl.2.1]
  have hev : ∀ᶠ x in 𝓝 (⟨0, h0mem⟩ : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ}),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, F (x, t) ≤ 2 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hlt : F (⟨0, h0mem⟩, t) < 2 := by rw [hF0]; norm_num
    exact (hF.continuousAt.eventually (gt_mem_nhds hlt)).mono fun z hz => hz.le
  rw [nhds_subtype, Filter.eventually_comap] at hev
  filter_upwards [hev] with X hX hXl t ht
  exact hX ⟨X, hXl⟩ rfl t ht

/- English proof (translation)
Use `set S := (growthSob θ V 1 N φ).toReal with hS`. Establish `hS0 : 0 ≤ S` using `ENNReal.toReal_nonneg`. Use `set s := ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ with hs_def`. Establish `hs0 : 0 ≤ s` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hglob : ∀ a : Fin V.rank × Fin V.rank, ∀ h, ‖glDer θ V (τ, a) φ h‖ ≤ S * height V h ^ N`.

Introduce `a`. Establish `h1 : growthSize V N (glDer θ V (τ, a) φ) ≤ growthSob θ V 1 N φ`. Establish `h0` using `le_wordSum (A := glDer θ V) (p := growthSize V N) (d := 1) (l := [(τ, a)]) (by simp) φ`. Simplify `h0` using `[wordAct, growthSob]`. Establish `h2 : growthSize V N (glDer θ V (τ, a) φ) ≤ ENNReal.ofReal S`.

Rewrite using `[hS, ENNReal.ofReal_toReal hf]`. Conclude with `h1`. Conclude with `(growthSize_le_iff hS0).1 h2`. Establish `hder : ∀ h, ‖Rder θ V τ X φ h‖ ≤ s * S * height V h ^ N`. Introduce `h`.

Rewrite using `[Rder_eq_sum_glDer hθ hs hX, Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, norm_smul]`. Conclude with `mul_le_mul_of_nonneg_left (hglob a h) (norm_nonneg _)`.

Use `_ = s * S * height V h ^ N := by rw [← Finset.sum_mul, mul_assoc]`. Establish `hC : 0 ≤ s * S * 2 ^ N` using `by positivity`. Rewrite using `[growthSize_le_iff hC]`. Introduce `g`. Establish `hl` using `height_laws (V := V)`.

Establish `hφd : ∀ t, HasDerivAt (fun r : ℝ => φ (g * oneP θ V τ X r)) (Rder θ V τ X φ (g * oneP θ V τ X t)) t` using `fun t => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX g') g t`. Establish `hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * 2 ^ N * height V g ^ N`. Introduce `t ht`. Establish `hk : height V (oneP θ V τ X t) ≤ 2` using `hh t (Set.Ico_subset_Icc_self ht)`. Establish `hgk : height V (g * oneP θ V τ X t) ≤ height V g * 2` using `(hl.2.2.2.1 g _).trans (mul_le_mul_of_nonneg_left hk (zero_le_one.trans (hl.1 g)))`.

Establish `hpow : height V (g * oneP θ V τ X t) ^ N ≤ (height V g * 2) ^ N` using `pow_le_pow_left₀ (zero_le_one.trans (hl.1 _)) hgk N`. Combine the equalities or inequalities in the displayed calculation. Establish `key` using `norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => φ (g * oneP θ V τ X r)) (a := 0) (b := 1) (fun t _ => (hφd t).hasDerivWithinAt) hb 1 (by simp)`. Simplify using `only [sub_zero, mul_one] at key`. Rewrite `key` using `[GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one]`.

Conclude with `key`.
-/
theorem growthSize_sub_le (hθ : IsInfFam θ) {τ : D.what₂.Tau} {N : ℕ} {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (hf : growthSob θ V 1 N φ ≠ ⊤) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hh : ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2) :
    growthSize V N (rTr V (oneP θ V τ X 1) φ - φ) ≤
      ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖) * (growthSob θ V 1 N φ).toReal * 2 ^ N) := by
  set S := (growthSob θ V 1 N φ).toReal with hS
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  set s := ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ with hs_def
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hglob : ∀ a : Fin V.rank × Fin V.rank, ∀ h, ‖glDer θ V (τ, a) φ h‖ ≤ S * height V h ^ N := by
    intro a
    have h1 : growthSize V N (glDer θ V (τ, a) φ) ≤ growthSob θ V 1 N φ := by
      have h0 := le_wordSum (A := glDer θ V) (p := growthSize V N) (d := 1) (l := [(τ, a)]) (by simp) φ
      simpa [wordAct, growthSob] using h0
    have h2 : growthSize V N (glDer θ V (τ, a) φ) ≤ ENNReal.ofReal S := by
      rw [hS, ENNReal.ofReal_toReal hf]
      exact h1
    exact (growthSize_le_iff hS0).1 h2
  have hder : ∀ h, ‖Rder θ V τ X φ h‖ ≤ s * S * height V h ^ N := by
    intro h
    rw [Rder_eq_sum_glDer hθ hs hX, Finset.sum_apply]
    calc ‖∑ a : Fin V.rank × Fin V.rank, (X a.1 a.2 • glDer θ V (τ, a) φ) h‖
        ≤ ∑ a : Fin V.rank × Fin V.rank, ‖(X a.1 a.2 • glDer θ V (τ, a) φ) h‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ * (S * height V h ^ N) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hglob a h) (norm_nonneg _)
      _ = s * S * height V h ^ N := by rw [← Finset.sum_mul, mul_assoc]
  have hC : 0 ≤ s * S * 2 ^ N := by positivity
  rw [growthSize_le_iff hC]
  intro g
  have hl := height_laws (V := V)
  have hφd : ∀ t, HasDerivAt (fun r : ℝ => φ (g * oneP θ V τ X r)) (Rder θ V τ X φ (g * oneP θ V τ X t)) t :=
    fun t => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX g') g t
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * 2 ^ N * height V g ^ N := by
    intro t ht
    have hk : height V (oneP θ V τ X t) ≤ 2 := hh t (Set.Ico_subset_Icc_self ht)
    have hgk : height V (g * oneP θ V τ X t) ≤ height V g * 2 :=
      (hl.2.2.2.1 g _).trans (mul_le_mul_of_nonneg_left hk (zero_le_one.trans (hl.1 g)))
    have hpow : height V (g * oneP θ V τ X t) ^ N ≤ (height V g * 2) ^ N :=
      pow_le_pow_left₀ (zero_le_one.trans (hl.1 _)) hgk N
    calc ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * height V (g * oneP θ V τ X t) ^ N := hder _
      _ ≤ s * S * (height V g * 2) ^ N := mul_le_mul_of_nonneg_left hpow (mul_nonneg hs0 hS0)
      _ = s * S * 2 ^ N * height V g ^ N := by rw [mul_pow]; ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => φ (g * oneP θ V τ X r))
    (a := 0) (b := 1) (fun t _ => (hφd t).hasDerivWithinAt) hb 1 (by simp)
  simp only [sub_zero, mul_one] at key
  rw [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
  exact key

/- English proof (translation)
Introduce `D θ hθ V τ N φ hs hf`. Take `⟨Λ, hΛmem, hΛ0, hΛexp⟩` from `exists_log V τ`. Establish `hH` using `exists_height_le hθ V τ`. Establish `h1 : Filter.Tendsto Λ (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0)` using `hΛ0.mono_left nhdsWithin_le_nhds`. Establish `h2 : Filter.Tendsto (fun u => ∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0)`.

Establish `h3 : ∀ a : Fin V.rank × Fin V.rank, Filter.Tendsto (fun u => ‖Λ u a.1 a.2‖) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0)`. Introduce `a`. Establish `hce : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => M a.1 a.2` using `by fun_prop`. Establish `h5 : Filter.Tendsto (fun u => Λ u a.1 a.2) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 ((0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) a.1 a.2))` using `(hce.tendsto _).comp h1`. Simplify using `using h5.norm`.

Establish `h4` using `tendsto_finsetSum (Finset.univ : Finset (Fin V.rank × Fin V.rank)) fun a _ => h3 a`. Simplify using `using h4`. Establish `hc : Filter.Tendsto (fun u => ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖) * (growthSob θ V 1 N φ).toReal * 2 ^ N)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0)`. Establish `h4` using `ENNReal.tendsto_ofReal ((h2.mul_const ((growthSob θ V 1 N φ).toReal)).mul_const ((2 : ℝ) ^ N))`. Simplify using `using h4`.

Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc (Filter.Eventually.of_forall fun _ => zero_le) ?_` and prove the remaining obligations. Use `filter_upwards [hΛexp, h1.eventually hH] with u hu hhu`. Establish `hk : atTau θ V τ u = oneP θ V τ (Λ u) 1` using `by show atTau θ V τ u = atTau θ V τ (NormedSpace.exp ((1 : ℝ) • Λ u))`. Rewrite using `[one_smul, hu]`. Rewrite using `[hk]`.

Conclude with `growthSize_sub_le hθ hs hf (hΛmem u) (hhu (hΛmem u))`.
-/
theorem tendsto_growthSize_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 1 N φ ≠ ⊤ → Filter.Tendsto (fun u : Matrix (Fin V.rank) (Fin V.rank) ℂ => GlobalTheory.Size.growthSize V N (rTr V (atTau θ V τ u) φ - φ)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (nhds 0) := by
  intro D θ hθ V τ N φ hs hf
  obtain ⟨Λ, hΛmem, hΛ0, hΛexp⟩ := exists_log V τ
  have hH := exists_height_le hθ V τ
  have h1 : Filter.Tendsto Λ (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := hΛ0.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun u => ∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖)
      (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h3 : ∀ a : Fin V.rank × Fin V.rank, Filter.Tendsto (fun u => ‖Λ u a.1 a.2‖)
        (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
      intro a
      have hce : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => M a.1 a.2 := by
        fun_prop
      have h5 : Filter.Tendsto (fun u => Λ u a.1 a.2) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ)))
          (𝓝 ((0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) a.1 a.2)) :=
        (hce.tendsto _).comp h1
      simpa using h5.norm
    have h4 := tendsto_finsetSum (Finset.univ : Finset (Fin V.rank × Fin V.rank)) fun a _ => h3 a
    simpa using h4
  have hc : Filter.Tendsto (fun u => ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖) *
      (growthSob θ V 1 N φ).toReal * 2 ^ N)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h4 := ENNReal.tendsto_ofReal ((h2.mul_const ((growthSob θ V 1 N φ).toReal)).mul_const ((2 : ℝ) ^ N))
    simpa using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hΛexp, h1.eventually hH] with u hu hhu
  have hk : atTau θ V τ u = oneP θ V τ (Λ u) 1 := by
    show atTau θ V τ u = atTau θ V τ (NormedSpace.exp ((1 : ℝ) • Λ u))
    rw [one_smul, hu]
  rw [hk]
  exact growthSize_sub_le hθ hs hf (hΛmem u) (hhu (hΛmem u))

end GlobalTheory.Size.NearOne

end
