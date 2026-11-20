import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtSubConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiPolynomialBoundInDirection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeAndArithmeticCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnObjectsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulCardPsi
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

open Formalism.BasicNotions.DV

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link

/- English proof (translation)
Take `⟨hg, hdec, hgap, -⟩` from `hW`. Establish `hr : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0)`. Simplify using `using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds`. Use `set M := WeightThresholdDefs.supAbs Y A.dir with hMdef`. Use `set S := WeightThresholdDefs.supAbs Y u with hSdef`.

Establish `hM : ∀ τ i, |A.dir τ i| ≤ M` using `fun τ i => le_ciSup (f := fun x : D.what₂.Tau × Fin Y.N => |A.dir x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)`. Establish `hS : ∀ τ i, |u τ i| ≤ S` using `fun τ i => le_ciSup (f := fun x : D.what₂.Tau × Fin Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)`. Establish `hM0 : 0 ≤ M` using `Real.iSup_nonneg fun _ => abs_nonneg _`. Establish `hS0 : 0 ≤ S` using `Real.iSup_nonneg fun _ => abs_nonneg _`. Use `set B₀ := WeightThresholdDefs.bigB0 Y u g with hB`.

Use `set P : ℝ := 4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 with hP`. Establish `hN2 : (4 : ℝ) ≤ (Y.N : ℝ) ^ 2` using `by nlinarith`. Establish `hP16 : 16 ≤ P` using `by rw [hP]; nlinarith`. Establish `hPf : 4 * (D.R.f : ℝ) ≤ P` using `by rw [hP]; nlinarith`. Establish `hBg : B₀ * g = P * (g + S)`.

Rewrite using `[hB, WeightThresholdDefs.bigB0, ← hSdef, hP]`. Clear the denominators using the available nonvanishing facts. Establish `hB16 : 16 ≤ B₀`. Rewrite using `[hB, WeightThresholdDefs.bigB0, ← hSdef]`. Establish `: 1 ≤ 1 + S / g` using `by have := div_nonneg hS0 hg.le; linarith`.

Use the polynomial consequences of the given equalities and inequalities. Use `set δ := (B₀ - 2) * g - 4 * (D.R.f : ℝ) * S with hδ`. Establish `hδ0 : 0 < δ`. Establish `e : δ = P * g + P * S - 2 * g - 4 * (D.R.f : ℝ) * S` using `by rw [hδ]; nlinarith [hBg]`. Rewrite using `[e]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hPf hS0]`. Use `set K := 4 * (D.R.f : ℝ) * M + 2 * (B₀ - 2) * M with hK`. Establish `hK0 : 0 ≤ K` using `by rw [hK]; have := mul_nonneg (by linarith : (0 : ℝ) ≤ B₀ - 2) hM0; nlinarith`. Establish `e1 : ∀ᶠ r : ℚ in 𝓝[>] 0, (r : ℝ) * K < δ`. Establish `: Tendsto (fun r : ℚ => (r : ℝ) * K) (𝓝[>] 0) (𝓝 0)` using `by simpa using hr.mul_const K`.

Conclude with `this.eventually (gt_mem_nhds hδ0)`. Establish `e2 : ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ τ (a b : Fin Y.N), a < b → (r : ℝ) * (A.dir τ a - A.dir τ b) < u τ a - u τ b`. Use `eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hab : a < b`. Establish `: Tendsto (fun r : ℚ => (r : ℝ) * (A.dir τ a - A.dir τ b)) (𝓝[>] 0) (𝓝 0)`.

Simplify using `using hr.mul_const (A.dir τ a - A.dir τ b)`. Conclude with `(this.eventually (gt_mem_nhds (sub_pos.2 (hdec τ a b hab)))).mono fun _ h _ => h`. Conclude with `Eventually.of_forall fun _ h => absurd h hab`. Use `filter_upwards [e1, e2, eventually_mem_nhdsWithin] with r h1 h2 (h0 : (0 : ℚ) < r)`. Establish `hr0 : (0 : ℝ) ≤ r` using `by exact_mod_cast h0.le`.

Use `⟨fun τ a b hab => ?_, fun τ => ?_⟩` and prove the remaining obligations. Break down `hab.lt_or_eq with hab | rfl` into its components or cases. Use `h2 τ a b hab` as an intermediate fact. Simplify using `only [SlopeTestRemainingChoices.sh]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `le_rfl`. Establish `hsup : WeightThresholdDefs.supAbs Y (A.sh u r) ≤ S + r * M`. Use `Real.iSup_le (fun x => ?_) (by positivity)` and prove the remaining obligations. Establish `h3` using `abs_sub (u x.1 x.2) ((r : ℝ) * A.dir x.1 x.2)`. Rewrite `h3` using `[abs_mul, abs_of_nonneg hr0]`.

Use `mul_le_mul_of_nonneg_left (hM x.1 x.2) hr0` as an intermediate fact. Simplify using `only [SlopeTestRemainingChoices.sh]`. Combine the linear relations using `[hS x.1 x.2]`. Establish `hgp : g - 2 * (r * M) ≤ WeightThresholdDefs.gap Y (A.sh u r) τ`. Establish `key : WeightThresholdDefs.gap Y (A.sh u r) τ = WeightThresholdDefs.gap Y u τ - r * WeightThresholdDefs.gap Y A.dir τ`.

Simplify using `only [WeightThresholdDefs.gap, SlopeTestRemainingChoices.sh]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd2 : |WeightThresholdDefs.gap Y A.dir τ| ≤ 2 * M`. Use `fun a b : Fin Y.N => (abs_sub (A.dir τ a) (A.dir τ b)).trans (by linarith [hM τ a, hM τ b] : |A.dir τ a| + |A.dir τ b| ≤ 2 * M)` as an intermediate fact. Conclude with `this _ _`.

Use `mul_le_mul_of_nonneg_left (abs_le.1 hd2).2 hr0` as an intermediate fact. Rewrite using `[key]`. Combine the linear relations using `[hgap τ]`. Establish `hB2 : (0 : ℝ) ≤ B₀ - 2` using `by linarith`. Establish `q1` using `mul_le_mul_of_nonneg_left hsup (by positivity : (0 : ℝ) ≤ 4 * (D.R.f : ℝ))`.

Establish `q2` using `mul_le_mul_of_nonneg_left hgp hB2`. Use `show 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs Y (A.sh u r) ≤ (B₀ - 2) * WeightThresholdDefs.gap Y (A.sh u r) τ`. Establish `: 4 * (D.R.f : ℝ) * (S + r * M) ≤ (B₀ - 2) * (g - 2 * (r * M))`. Rewrite `*` using `[hδ, hK]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eventually_dominant_nefCond {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y) (u : Wt Y) (g : ℝ)
    (hW : WeightThresholdDefs.WeightHyp Y u g) (hf : 1 ≤ (D.R.f : ℝ)) (hN : 2 ≤ (Y.N : ℝ)) :
    ∀ᶠ r : ℚ in 𝓝[>] 0, WeightThresholdDefs.Dominant Y (A.sh u r) ∧ NefCond Y (WeightThresholdDefs.bigB0 Y u g) (A.sh u r) := by
  obtain ⟨hg, hdec, hgap, -⟩ := hW
  have hr : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds
  set M := WeightThresholdDefs.supAbs Y A.dir with hMdef
  set S := WeightThresholdDefs.supAbs Y u with hSdef
  have hM : ∀ τ i, |A.dir τ i| ≤ M := fun τ i =>
    le_ciSup (f := fun x : D.what₂.Tau × Fin Y.N => |A.dir x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)
  have hS : ∀ τ i, |u τ i| ≤ S := fun τ i =>
    le_ciSup (f := fun x : D.what₂.Tau × Fin Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ => abs_nonneg _
  have hS0 : 0 ≤ S := Real.iSup_nonneg fun _ => abs_nonneg _
  set B₀ := WeightThresholdDefs.bigB0 Y u g with hB
  set P : ℝ := 4 * (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 with hP
  have hN2 : (4 : ℝ) ≤ (Y.N : ℝ) ^ 2 := by nlinarith
  have hP16 : 16 ≤ P := by rw [hP]; nlinarith
  have hPf : 4 * (D.R.f : ℝ) ≤ P := by rw [hP]; nlinarith
  have hBg : B₀ * g = P * (g + S) := by
    rw [hB, WeightThresholdDefs.bigB0, ← hSdef, hP]; field_simp
  have hB16 : 16 ≤ B₀ := by
    rw [hB, WeightThresholdDefs.bigB0, ← hSdef]
    have : 1 ≤ 1 + S / g := by have := div_nonneg hS0 hg.le; linarith
    nlinarith
  set δ := (B₀ - 2) * g - 4 * (D.R.f : ℝ) * S with hδ
  have hδ0 : 0 < δ := by
    have e : δ = P * g + P * S - 2 * g - 4 * (D.R.f : ℝ) * S := by rw [hδ]; nlinarith [hBg]
    rw [e]; nlinarith [mul_le_mul_of_nonneg_right hPf hS0]
  set K := 4 * (D.R.f : ℝ) * M + 2 * (B₀ - 2) * M with hK
  have hK0 : 0 ≤ K := by rw [hK]; have := mul_nonneg (by linarith : (0 : ℝ) ≤ B₀ - 2) hM0; nlinarith
  have e1 : ∀ᶠ r : ℚ in 𝓝[>] 0, (r : ℝ) * K < δ := by
    have : Tendsto (fun r : ℚ => (r : ℝ) * K) (𝓝[>] 0) (𝓝 0) := by simpa using hr.mul_const K
    exact this.eventually (gt_mem_nhds hδ0)
  have e2 : ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ τ (a b : Fin Y.N), a < b → (r : ℝ) * (A.dir τ a - A.dir τ b) < u τ a - u τ b := by
    refine eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => ?_
    by_cases hab : a < b
    · have : Tendsto (fun r : ℚ => (r : ℝ) * (A.dir τ a - A.dir τ b)) (𝓝[>] 0) (𝓝 0) := by
        simpa using hr.mul_const (A.dir τ a - A.dir τ b)
      exact (this.eventually (gt_mem_nhds (sub_pos.2 (hdec τ a b hab)))).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h hab
  filter_upwards [e1, e2, eventually_mem_nhdsWithin] with r h1 h2 (h0 : (0 : ℚ) < r)
  have hr0 : (0 : ℝ) ≤ r := by exact_mod_cast h0.le
  refine ⟨fun τ a b hab => ?_, fun τ => ?_⟩
  · rcases hab.lt_or_eq with hab | rfl
    · have := h2 τ a b hab
      simp only [SlopeTestRemainingChoices.sh]; linarith
    · exact le_rfl
  · have hsup : WeightThresholdDefs.supAbs Y (A.sh u r) ≤ S + r * M := by
      refine Real.iSup_le (fun x => ?_) (by positivity)
      have h3 := abs_sub (u x.1 x.2) ((r : ℝ) * A.dir x.1 x.2)
      rw [abs_mul, abs_of_nonneg hr0] at h3
      have := mul_le_mul_of_nonneg_left (hM x.1 x.2) hr0
      simp only [SlopeTestRemainingChoices.sh]
      linarith [hS x.1 x.2]
    have hgp : g - 2 * (r * M) ≤ WeightThresholdDefs.gap Y (A.sh u r) τ := by
      have key : WeightThresholdDefs.gap Y (A.sh u r) τ = WeightThresholdDefs.gap Y u τ - r * WeightThresholdDefs.gap Y A.dir τ := by
        simp only [WeightThresholdDefs.gap, SlopeTestRemainingChoices.sh]; ring
      have hd2 : |WeightThresholdDefs.gap Y A.dir τ| ≤ 2 * M := by
        have := fun a b : Fin Y.N =>
          (abs_sub (A.dir τ a) (A.dir τ b)).trans (by linarith [hM τ a, hM τ b] : |A.dir τ a| + |A.dir τ b| ≤ 2 * M)
        exact this _ _
      have := mul_le_mul_of_nonneg_left (abs_le.1 hd2).2 hr0
      rw [key]; linarith [hgap τ]
    have hB2 : (0 : ℝ) ≤ B₀ - 2 := by linarith
    have q1 := mul_le_mul_of_nonneg_left hsup (by positivity : (0 : ℝ) ≤ 4 * (D.R.f : ℝ))
    have q2 := mul_le_mul_of_nonneg_left hgp hB2
    show 4 * (D.R.f : ℝ) * WeightThresholdDefs.supAbs Y (A.sh u r) ≤ (B₀ - 2) * WeightThresholdDefs.gap Y (A.sh u r) τ
    have : 4 * (D.R.f : ℝ) * (S + r * M) ≤ (B₀ - 2) * (g - 2 * (r * M)) := by
      rw [hδ, hK] at *; nlinarith
    linarith

/- English proof (translation)
Introduce `hX h1 h2 h3 D O hC hfN u g hR hW`. Take `⟨A, T, H, ⟨R⟩, -⟩` from `ReadsEx.main h1.p4 D O hC`. Establish `hIns` using `h3 D O hC hfN A T H R`. Establish `hQ` using `GlobalTheory.CovHt.qPolBd_onObj h1 h2 D O hC hfN A T H R`. Establish `hSz` using `GlobalTheory.T.fibre_size_and_range_bound h1 h2 D O hC hfN A T H R`.

Establish `hTie` using `GlobalTheory.T.degree_and_arithmetic_compatibility h1 h2 D O hC hfN A T H R`. Establish `hNef` using `GlobalTheory.T.nef_on_objects hX h1 h2 D O hC hfN A T H R`. Establish `hF : ∀ c, (T.F c).FamS` using `fun c => (RegFam.nefAn_and_famS D O.Y T c (hIns c)).2 A.dir (hQ c) (hSz c).1`. Establish `hPos : Positive A` using `hNef.positive (semiposAt_of_famS hF hTie.2.1)`. Take `⟨s₀, hs₀, hP⟩` from `hPos (WeightThresholdDefs.supAbs O.Y u)`.

Establish `hf : 1 ≤ D.R.f`. Break down `Nat.eq_zero_or_pos D.R.f with h | h` into its components or cases. Simplify using `[h] at hfN`. Conclude with `h`. Establish `hN : 2 ≤ O.N`.

Assume the negation of the conclusion as `h`. Establish `: O.N - 1 = 0` using `by omega`. Simplify using `[this] at hfN`. Establish `hf' : (1 : ℝ) ≤ (D.R.f : ℝ)` using `by exact_mod_cast hf`. Establish `hN' : (2 : ℝ) ≤ (O.Y.N : ℝ)` using `by exact_mod_cast hN`.

Establish `hr : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0)`. Simplify using `using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds`. Establish `hB2 : 2 ≤ WeightThresholdDefs.bigB0 O.Y u g`. Take `⟨hg, -⟩` from `hW`. Establish `hS0 : 0 ≤ WeightThresholdDefs.supAbs O.Y u` using `Real.iSup_nonneg fun _ => abs_nonneg _`.

Establish `: 1 ≤ 1 + WeightThresholdDefs.supAbs O.Y u / g` using `by have := div_nonneg hS0 hg.le; linarith`. Simplify using `only [WeightThresholdDefs.bigB0]`. Establish `hN2 : (4 : ℝ) ≤ (O.Y.N : ℝ) ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_le_mul hf' hN2 (by norm_num) (by linarith)]`. Use `filter_upwards [eventually_dominant_nefCond A u g hW hf' hN', eventually_mem_nhdsWithin, hr.eventually (eventually_le_nhds hs₀)] with r ⟨hd, hn⟩ (h0 : (0 : ℚ) < r) hrs`.

Establish `h` using `hP _ hB2 u r hR le_rfl h0 hrs hd hn`. Conclude with `fun k => ⟨h.1 k, h.2 k⟩`.
-/
theorem approx_semipos_nefFib : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegSt → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) → ∀ (u : D.what₂.Tau → Fin O.N → ℝ) (g : ℝ), IsRat O.Y u → WeightThresholdDefs.WeightHyp O.Y u g → ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ k : O.s.Comp, (O.Mb (WeightThresholdDefs.bigB0 O.Y u g) u r k).SemiPos ∧ (O.Mb (WeightThresholdDefs.bigB0 O.Y u g) u r k).NefFib := by
  intro hX h1 h2 h3 D O hC hfN u g hR hW
  obtain ⟨A, T, H, ⟨R⟩, -⟩ := ReadsEx.main h1.p4 D O hC
  have hIns := h3 D O hC hfN A T H R
  have hQ := GlobalTheory.CovHt.qPolBd_onObj h1 h2 D O hC hfN A T H R
  have hSz := GlobalTheory.T.fibre_size_and_range_bound h1 h2 D O hC hfN A T H R
  have hTie := GlobalTheory.T.degree_and_arithmetic_compatibility h1 h2 D O hC hfN A T H R
  have hNef := GlobalTheory.T.nef_on_objects hX h1 h2 D O hC hfN A T H R
  have hF : ∀ c, (T.F c).FamS := fun c => (RegFam.nefAn_and_famS D O.Y T c (hIns c)).2 A.dir (hQ c) (hSz c).1
  have hPos : Positive A := hNef.positive (semiposAt_of_famS hF hTie.2.1)
  obtain ⟨s₀, hs₀, hP⟩ := hPos (WeightThresholdDefs.supAbs O.Y u)
  have hf : 1 ≤ D.R.f := by
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · simp [h] at hfN
    · exact h
  have hN : 2 ≤ O.N := by
    by_contra h
    have : O.N - 1 = 0 := by omega
    simp [this] at hfN
  have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf
  have hN' : (2 : ℝ) ≤ (O.Y.N : ℝ) := by exact_mod_cast hN
  have hr : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Rat.continuous_coe_real.tendsto 0).mono_left nhdsWithin_le_nhds
  have hB2 : 2 ≤ WeightThresholdDefs.bigB0 O.Y u g := by
    obtain ⟨hg, -⟩ := hW
    have hS0 : 0 ≤ WeightThresholdDefs.supAbs O.Y u := Real.iSup_nonneg fun _ => abs_nonneg _
    have : 1 ≤ 1 + WeightThresholdDefs.supAbs O.Y u / g := by have := div_nonneg hS0 hg.le; linarith
    simp only [WeightThresholdDefs.bigB0]
    have hN2 : (4 : ℝ) ≤ (O.Y.N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul hf' hN2 (by norm_num) (by linarith)]
  filter_upwards [eventually_dominant_nefCond A u g hW hf' hN', eventually_mem_nhdsWithin,
    hr.eventually (eventually_le_nhds hs₀)] with r ⟨hd, hn⟩ (h0 : (0 : ℚ) < r) hrs
  have h := hP _ hB2 u r hR le_rfl h0 hrs hd hn
  exact fun k => ⟨h.1 k, h.2 k⟩

end GlobalTheory.CovHt.Link
