import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCountStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimensionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsLogResolutionStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

/- English proof (translation)
Introduce `hin K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har`. Establish `hdim` using `GlobalTheory.T.flag_analytic_dimension_count K ι Φ y Ψ N j M n d BM FA`. Take `⟨RW, pr, hpr, hbase, hch⟩` from `GlobalTheory.T.flag_adjacent_rows_resolution K ι Φ y Ψ N j M n d BM.Rb τ a b k₀ ca cb hb hs hk hca hcb har hdim`. Take `⟨q, hq, hpq, hl0, hl1, hinj, hbp⟩` from `GlobalTheory.T.flag_adjacent_rows_analytic K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr hbase`. Establish `hch' : ∀ x, ∃ (ψ : OpenPartialHomeomorph RW.X (Fin (d + 2) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 2)), IsCompatChart RW.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧ ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i))` using `fun x => by`.

Take `⟨ψ, kb, σ, i₀, F, H, hx, h1, -, -, h4, -⟩` from `hch x`. Conclude with `⟨ψ, kb, σ, h1, hx, h4⟩`. Take `⟨pL, sL, nL, -⟩` from `GlobalTheory.T.snc_adapted_atlas_projection (d + 2) n RW.X BM.Rb.X RW.A BM.Rb.A BM.Bat pr hpr BM.L BM.s BM.nb BM.m BM.W BM.potL BM.sec BM.snc BM.norm_le hch'`. Take `⟨hA, hfs, hΘ⟩` from `GlobalTheory.T.log_resolution_fubini_study_positive (Option K) (fun o => ι (o.getD k₀)) _ (d + 2) RW`. Establish `hL : ∀ i, (FA.S.comap some).L.pullback (q i) (hq i).1 = BM.L.pullback pr hpr.1` using `fun i => by show FA.S.L.pullback (q i) (hq i).1 = _`.

Establish `e` using `FA.L_eq`. Use `revert e`. Generalize the expression as in `FA.S.L = LL`. Introduce `e`. Substitute `e` using the available equality.

Conclude with `pullback_pullback _ _ _ _ _ _ _ (hpq i)`. Establish `hs' : ∀ i, (fun x y => (FA.S.comap some).s (q i x) (q i y)) = fun x y => BM.s (pr x) (pr y)` using `fun i => by`. Use function extensionality and compare the values at `x y`. Use `show FA.S.s (q i x) (q i y) = _`. Rewrite using `[FA.s_eq]`.

Use `show BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) y) = _`. Rewrite using `[hpq i]`. Take `⟨C₅, C, t₀, ht₀, hmem⟩` from `GlobalTheory.T.two_map_pullback_energy (d + 1) (d + 2) (Ψ × Fin N) (FA.S.comap some) RW.X RW.A (potOf RW (fsHerm _ fun _ => 1)) (BM.L.pullback pr hpr.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m (fun k => pr ⁻¹' BM.W k) q hq hin.pullback (hA _ hfs) hΘ pL sL nL (fun x => BM.norm_ …`. Take `⟨L', v, Dg, cst, potL', secv, sncv, sncsv, normv, hN⟩` from `GlobalTheory.T.flag_adjacent_rows_base_metric K ι Φ y Ψ N j M n d BM τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr.1 ⟨hpr, hbase, hch⟩`. Take `⟨U, B, G, ΦY, ΦW, U_open, B_meas, coverY, coverW, ΦY_open, hfc⟩` from `GlobalTheory.T.flag_adjacent_rows_dimension K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq hl0 hl1 hinj`.

Take `⟨α, G_pos, G_smooth, α_smooth, xi_pot, base_pot, norm_hom⟩` from `GlobalTheory.T.flag_adjacent_rows_log_resolution K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq hl0 hl1 L' v cst hN U G ΦY ΦW U_open hfc`. Set `SW : AnSys (d + 2) (Option (Ψ × Fin N))` to `{ X := RW.X A := RW.A Θ := potOf RW (fsHerm _ fun _ => 1) L := BM.L.pullback pr hpr.1 s := fun x y => BM.s (pr x) (pr y) nb := BM.nb m := BM.m W := fun k => pr ⁻¹' BM.W k potΘ := hA _ hfs posΘ := hΘ potL := pL sec := sL snc := nL norm_le := fun x => BM.norm_le (pr x) th := fun o …`. Consider the cases of `o with`. Consider the case `none => exact (hmem 1 (τ, a)).1`. Consider the case `some p => exact (hmem 0 p).1`.

Use `reg := fun o => by`. Consider the cases of `o with`. Consider the case `none => exact (hmem 1 (τ, a)).2.1`. Consider the case `some p => exact (hmem 0 p).2.1`. Use `c2 := fun o => by`.

Consider the cases of `o with`. Consider the case `none => exact (hmem 1 (τ, a)).2.2`. Consider the case `some p => exact (hmem 0 p).2.2 }`. Establish `hsame : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X), SamePot A Set.univ P P` using `fun A P x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun y _ => by simp⟩`. Set `Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)` to `{ eps_a₀ := by simp [xiCoef] SW := SW q := q holo := hq bdry_eq := fun i => by`.

Use extensionality with `x`. Use `show BM.s (pr x) (pr x) ≠ 0 ↔ FA.S.s (q i x) (q i x) ≠ 0`. Rewrite using `[FA.s_eq]`. Use `show _ ↔ BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) x) ≠ 0`. Rewrite using `[hpq i]`.

Use `t₀_le := ht₀`. Use `th0 := fun p => hsame _ _`. Use `th1 := hsame _ _`. Use `ph0 := fun _ => rfl`. Use `ph1 := rfl`.

Use `phase_some_eq_comp_first_projection := fun _ _ => rfl`. Use `phase_none_eq_comp_second_projection := fun _ => rfl`. Use `base_ph := fun p hp => (hbp p hp).1`. Use `base_phT := fun p hp t => (hbp p hp).2 t`. Use the proof step `L' := L'`.

Use `v := v`. Use `Dg := Dg`. Use `cst := cst`. Use the proof step `potL' := potL'`. Use `secv := secv`.

Use `sncv := sncv`. Use `sncsv := sncsv`. Use `normv := normv`. Use `U := U`. Use `B := B`.

Use `G := G`. Use `α := α`. Use `ΦY := ΦY`. Use `ΦW := ΦW`. Use `U_open := U_open`.

Use `B_meas := B_meas`. Use `G_pos := G_pos`. Use `G_smooth := G_smooth`. Use `α_smooth := fun m p => α_smooth m p`. Use `coverY := coverY`.

Use `coverW := coverW`. Use `ΦY_open := ΦY_open`. Use `first_projection_chart_compat := fun m z hz => by`. Take `⟨l, H, bp, -, -, -, -, -, -, h⟩` from `hfc m`. Conclude with `(h z hz).1`.

Use `second_projection_chart_compat := fun m z hz => by`. Take `⟨l, H, bp, -, -, -, -, -, -, h⟩` from `hfc m`. Conclude with `(h z hz).2`. Use `xi_pot := xi_pot`. Use `base_pot := base_pot`.

Use `norm_hom := norm_hom }`. Establish `hsurj : ∀ w, ∃ x₀, FA.Re.π x₀ = w` using `fun w => by`. Establish `hd` using `FA.Re.degree`. Rewrite `hd` using `[FA.deg_one, FA.br_empty]`. Take `⟨x₀, hx₀⟩` from `Set.ncard_eq_one.1 (hd.2.2.2.2.1 w (Set.notMem_empty w))`.

Conclude with `⟨x₀, (hx₀ ▸ Set.mem_singleton x₀ : x₀ ∈ FA.Re.π ⁻¹' {w})⟩`. Use `⟨Q, RW, id, ⟨continuous_id, fun j k => RW.A.holo j k⟩, isDegreeOff_id RW.A, hl0, ?_, hinj, ?_⟩` and prove the remaining obligations. Introduce `x x₀ hx`. Use `⟨sndPt k₀ (RW.lift x x), hl1 x x₀ hx, fun p hp => ?_, fun m => ?_⟩` and prove the remaining obligations. Use `show RW.lift x x (v₁ k₀ p) = _`.

Rewrite using `[v₁_ne hp]`. Use `show RW.lift x x (v₁ k₀ ⟨k₀, m⟩) = _`. Rewrite using `[v₁_self]`. Introduce `x z₀ z₁ F h t hF hG h0 h1 hh hd ht hE0 hE1`. Take `⟨x₀, hx₀⟩` from `hsurj (q 0 x)`.

Take `⟨x₁, hx₁⟩` from `hsurj (q 1 x)`. Conclude with `hN x z₀ z₁ F h t hF hG (orbit_trans (orbit_symm (h0 x₀ hx₀)) (hl0 x x₀ hx₀)) (orbit_trans (orbit_symm (h1 x₁ hx₁)) (hl1 x x₁ hx₁)) hh hd ht hE0 hE1`.
-/
theorem ansq_exists : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∃ (Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a)) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → Q.SW.X), HoloMap RW.A Q.SW.A e ∧ IsDegreeOff Q.SW.A RW.A e 1 ∅ ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) fun p => RW.lift x x ⟨some p.1, p.2⟩) ∧ (∀ x x₀, FA.Re.π x₀ = Q.q 1 (e x) → ∃ z₁, SameOrbit (FA.Re.R.lift x₀ x₀) z₁ ∧ (∀ p : (Σ k, ι k), p.1 ≠ k₀ → z₁ p = RW.lift x x ⟨some p.1, p.2⟩) ∧ ∀ m : ι k₀, z₁ ⟨k₀, m⟩ = RW.lift x x ⟨none, m⟩) ∧ (Function.Injective fun w => (Q.q 0 w, Q.q 1 w)) ∧ ∀ x (z₀ z₁ : (Σ k, ι k) → ℂ) F (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → (∀ x₀, FA.Re.π x₀ = Q.q 0 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₀) → (∀ x₀, FA.Re.π x₀ = Q.q 1 (e x) → SameOrbit (FA.Re.R.lift x₀ x₀) z₁) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → logNormSec Q.L' Q.v (e x) + Q.cst = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1) else minorIJ h (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
  intro hin K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har
  have hdim := GlobalTheory.T.flag_analytic_dimension_count K ι Φ y Ψ N j M n d BM FA
  obtain ⟨RW, pr, hpr, hbase, hch⟩ := GlobalTheory.T.flag_adjacent_rows_resolution K ι Φ y Ψ N j M n d BM.Rb τ a b k₀ ca cb hb hs hk hca hcb har hdim
  obtain ⟨q, hq, hpq, hl0, hl1, hinj, hbp⟩ :=
    GlobalTheory.T.flag_adjacent_rows_analytic K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr hbase
  have hch' : ∀ x, ∃ (ψ : OpenPartialHomeomorph RW.X (Fin (d + 2) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 2)),
      IsCompatChart RW.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i)) := fun x => by
    obtain ⟨ψ, kb, σ, i₀, F, H, hx, h1, -, -, h4, -⟩ := hch x
    exact ⟨ψ, kb, σ, h1, hx, h4⟩
  obtain ⟨pL, sL, nL, -⟩ := GlobalTheory.T.snc_adapted_atlas_projection (d + 2) n RW.X BM.Rb.X RW.A BM.Rb.A BM.Bat pr hpr BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch'
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.T.log_resolution_fubini_study_positive (Option K) (fun o => ι (o.getD k₀)) _ (d + 2) RW
  have hL : ∀ i, (FA.S.comap some).L.pullback (q i) (hq i).1 = BM.L.pullback pr hpr.1 := fun i => by
    show FA.S.L.pullback (q i) (hq i).1 = _
    have e := FA.L_eq
    revert e
    generalize FA.S.L = LL
    intro e
    subst e
    exact pullback_pullback _ _ _ _ _ _ _ (hpq i)
  have hs' : ∀ i, (fun x y => (FA.S.comap some).s (q i x) (q i y)) = fun x y => BM.s (pr x) (pr y) := fun i => by
    funext x y
    show FA.S.s (q i x) (q i y) = _
    rw [FA.s_eq]
    show BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) y) = _
    rw [hpq i]
  obtain ⟨C₅, C, t₀, ht₀, hmem⟩ := GlobalTheory.T.two_map_pullback_energy (d + 1) (d + 2) (Ψ × Fin N) (FA.S.comap some) RW.X RW.A
    (potOf RW (fsHerm _ fun _ => 1)) (BM.L.pullback pr hpr.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) q hq hin.pullback (hA _ hfs) hΘ pL sL nL (fun x => BM.norm_le (pr x)) hL hs'
  obtain ⟨L', v, Dg, cst, potL', secv, sncv, sncsv, normv, hN⟩ :=
    GlobalTheory.T.flag_adjacent_rows_base_metric K ι Φ y Ψ N j M n d BM τ a b k₀ ca cb hb hs hk hca hcb har RW pr hpr.1 ⟨hpr, hbase, hch⟩
  obtain ⟨U, B, G, ΦY, ΦW, U_open, B_meas, coverY, coverW, ΦY_open, hfc⟩ :=
    GlobalTheory.T.flag_adjacent_rows_dimension K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq hl0 hl1 hinj
  obtain ⟨α, G_pos, G_smooth, α_smooth, xi_pot, base_pot, norm_hom⟩ :=
    GlobalTheory.T.flag_adjacent_rows_log_resolution K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq hl0 hl1 L' v cst hN U G ΦY ΦW U_open hfc
  let SW : AnSys (d + 2) (Option (Ψ × Fin N)) :=
    { X := RW.X
      A := RW.A
      Θ := potOf RW (fsHerm _ fun _ => 1)
      L := BM.L.pullback pr hpr.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := fun x => BM.norm_le (pr x)
      th := fun o => o.elim (((FA.S.comap some).th (τ, a)).pullback (q 1) (hq 1).1)
        fun p => ((FA.S.comap some).th p).pullback (q 0) (hq 0).1
      ph := fun o => o.elim ((FA.S.comap some).ph (τ, a) ∘ q 1) fun p => (FA.S.comap some).ph p ∘ q 0
      phT := fun o => o.elim (fun t => (FA.S.comap some).phT (τ, a) t ∘ q 1)
        fun p t => (FA.S.comap some).phT p t ∘ q 0
      C₅ := C₅
      C := C
      t₀ := t₀
      sing := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).1
        | some p => exact (hmem 0 p).1
      reg := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.1
        | some p => exact (hmem 0 p).2.1
      c2 := fun o => by
        cases o with
        | none => exact (hmem 1 (τ, a)).2.2
        | some p => exact (hmem 0 p).2.2 }
  have hsame : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X), SamePot A Set.univ P P :=
    fun A P x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun y _ => by simp⟩
  let Q : AnSq (FA.S.comap some) (τ, a) (xiCoef τ a) :=
    { eps_a₀ := by simp [xiCoef]
      SW := SW
      q := q
      holo := hq
      bdry_eq := fun i => by
        ext x
        show BM.s (pr x) (pr x) ≠ 0 ↔ FA.S.s (q i x) (q i x) ≠ 0
        rw [FA.s_eq]
        show _ ↔ BM.s ((FA.pr ∘ q i) x) ((FA.pr ∘ q i) x) ≠ 0
        rw [hpq i]
      t₀_le := ht₀
      th0 := fun p => hsame _ _
      th1 := hsame _ _
      ph0 := fun _ => rfl
      ph1 := rfl
      phase_some_eq_comp_first_projection := fun _ _ => rfl
      phase_none_eq_comp_second_projection := fun _ => rfl
      base_ph := fun p hp => (hbp p hp).1
      base_phT := fun p hp t => (hbp p hp).2 t
      L' := L'
      v := v
      Dg := Dg
      cst := cst
      potL' := potL'
      secv := secv
      sncv := sncv
      sncsv := sncsv
      normv := normv
      U := U
      B := B
      G := G
      α := α
      ΦY := ΦY
      ΦW := ΦW
      U_open := U_open
      B_meas := B_meas
      G_pos := G_pos
      G_smooth := G_smooth
      α_smooth := fun m p => α_smooth m p
      coverY := coverY
      coverW := coverW
      ΦY_open := ΦY_open
      first_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).1
      second_projection_chart_compat := fun m z hz => by
        obtain ⟨l, H, bp, -, -, -, -, -, -, h⟩ := hfc m
        exact (h z hz).2
      xi_pot := xi_pot
      base_pot := base_pot
      norm_hom := norm_hom }
  have hsurj : ∀ w, ∃ x₀, FA.Re.π x₀ = w := fun w => by
    have hd := FA.Re.degree
    rw [FA.deg_one, FA.br_empty] at hd
    obtain ⟨x₀, hx₀⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 w (Set.notMem_empty w))
    exact ⟨x₀, (hx₀ ▸ Set.mem_singleton x₀ : x₀ ∈ FA.Re.π ⁻¹' {w})⟩
  refine ⟨Q, RW, id, ⟨continuous_id, fun j k => RW.A.holo j k⟩, isDegreeOff_id RW.A, hl0, ?_, hinj, ?_⟩
  · intro x x₀ hx
    refine ⟨sndPt k₀ (RW.lift x x), hl1 x x₀ hx, fun p hp => ?_, fun m => ?_⟩
    · show RW.lift x x (v₁ k₀ p) = _
      rw [v₁_ne hp]
    · show RW.lift x x (v₁ k₀ ⟨k₀, m⟩) = _
      rw [v₁_self]
  · intro x z₀ z₁ F h t hF hG h0 h1 hh hd ht hE0 hE1
    obtain ⟨x₀, hx₀⟩ := hsurj (q 0 x)
    obtain ⟨x₁, hx₁⟩ := hsurj (q 1 x)
    exact hN x z₀ z₁ F h t hF hG (orbit_trans (orbit_symm (h0 x₀ hx₀)) (hl0 x x₀ hx₀)) (orbit_trans (orbit_symm (h1 x₁ hx₁)) (hl1 x x₁ hx₁))
      hh hd ht hE0 hE1

end GlobalTheory.CompanionTheory.Ar.PB.WSq
