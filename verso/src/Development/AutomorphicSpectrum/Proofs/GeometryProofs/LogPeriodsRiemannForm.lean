import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocallyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpansStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnectedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotientStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrixStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeFamilyLocalSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Link

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ n a C hpq hσ`. Take `⟨g', ty, hty⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q`. Take `⟨FU⟩` from `GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty`. Establish `hsemi : IsSemiAbelian C.t.G` using `C.t.semi`. Take `⟨ε, hε, hεB, ⟨e₀⟩⟩` from `GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0 (Metric.mem_ball_self one_pos)`.

Establish `h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε` using `Metric.mem_ball_self hε`. Take `⟨Γ₀, hΓ₀, -, hfin, hfree⟩` from `GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε`. Set `Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ)` to `fun b => AddSubgroup.closure (e₀.per b)`. Establish `hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b` using `fun b hb p => mem_closure_per e₀ hb p`. Establish `hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧ DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b`.

Introduce `x`. Take `⟨ε', s, h0, hsub, hd, hs0, hs⟩` from `GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x (by rw [← hΓ₀]; exact x.2)`. Conclude with `⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩`. Take `⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩` from `exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp`. Establish `hρ1 : ρ ≤ 1` using `hρc.trans (min_le_left _ _)`.

Establish `hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε` using `Metric.ball_subset_ball (hρc.trans (min_le_right _ _))`. Establish `hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1` using `Metric.ball_subset_ball hρ1`. Establish `h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ` using `Metric.mem_ball_self hρ0`. Set `e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ` to `restrict e₀ Metric.isOpen_ball hball`. Establish `hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b` using `fun b hb p => hQ b (hball hb) p`.

Establish `hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0` using `hΓ₀`. Establish `hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b` using `fun x b hb => (hQ' b hb _).1 (hSq x b hb)`. Take `⟨i, Hf, hrank, hopen, hloc⟩` from `GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1`. Take `⟨hfreeL, hfinL, -⟩` from `GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)`. Establish `hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ` using `fun z hz => (smul_mem_punct hρ0).2 hz`.

Establish `hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z)` using `differentiable_id.fun_const_smul _`. Establish `key : ∃ L : LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z))`. Use `GlobalTheory.T.lattice_family_local_sections n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z)) (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩`. Introduce `z₀ hz₀`.

Take `⟨N, hNo, hzN, hNp, P, hPd, hP⟩` from `hloc _ (hU z₀ hz₀)`. Use `⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN, fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `(hPd x).comp hsm.differentiableOn (fun z hz => hz)`. Take `⟨h1, h2, h3⟩` from `hP _ hz`. Use `⟨h1, ?_, h3⟩` and prove the remaining obligations.

Use extensionality with `p`. Establish `h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z)`. Rewrite using `[← SetLike.mem_coe, h2]`. Rewrite using `[h4]`. Conclude with `(hQ' _ (punct_subset_ball (hNp hz)) p).symm`.

Introduce `x`. Use `⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_, fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩` and prove the remaining obligations. Use `show S x ((ρ : ℂ) • 0) = x`. Rewrite using `[smul_zero]`. Conclude with `hS0 x`.

Conclude with `fun x y z => hSa x y _`. Introduce `s hs hsU`. Take `⟨u, hu, huU⟩` from `exists_seq_punct (n := n) (a := a)`. Establish `hρc' : (ρ : ℂ) ≠ 0` using `by exact_mod_cast hρ0.ne'`. Establish `htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0)`.

Establish `h` using `hu.const_smul (ρ : ℂ)`. Rewrite `h` using `[smul_zero]`. Then use the resulting hypothesis. Establish `hcl` using `GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b)) (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _)) (htend.frequent …`. Use `⟨punct_subset_ball (hU _ (huU k)), ?_⟩` and prove the remaining obligations. Use `show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]`. Conclude with `(hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))`. Establish `h0 : s 0 ∈ e.per 0` using `by simpa using hcl`. Rewrite `h0` using `[← hΓ₀']`. Conclude with `h0`.

Rewrite using `[hΓ₀']`. Conclude with `GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ`. Introduce `N hN`. Take `⟨T, hT, hTw⟩` from `GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN`. Use `⟨T, hT, fun x y hx z hz => ?_⟩` and prove the remaining obligations.

Establish `hb` using `hU z hz`. Establish `hbm` using `punct_subset_ball hb`. Establish `hc` using `cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by`. Rewrite using `[hS0 x, hS0 y]`. Establish `h1 : unitOn (1 : ℂˣ) = 1` using `map_one _`.

Rewrite using `[h1]`. Conclude with `hTw x y hx) _ hbm`. Establish `hz'` using `(hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc`. Conclude with `exists_int_of_exp_eq_one hN hz'`. Take `⟨L, hLH⟩` from `key`.

Use `⟨ρ, (FU.Di i).La, inferInstance, L, hρ0, hρ1, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hLH]`. Conclude with `(hopen _ (hU z hz)).2.2.1`.
-/
theorem exists_logPeriods_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : LogPeriods n a C.g Λ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) := by
    refine GlobalTheory.T.lattice_family_local_sections n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, hρ0, hρ1, fun z hz => ?_⟩
  rw [hLH]
  exact (hopen _ (hU z hz)).2.2.1

end GlobalTheory.CompanionTheory.Ar.Flat
