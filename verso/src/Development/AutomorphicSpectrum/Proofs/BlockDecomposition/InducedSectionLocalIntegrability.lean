import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

/- English proof (translation)
Establish `e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ)`. Use `Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) integral_complex_ofReal` and prove the remaining obligations. Conclude with `Complex.ext (by simp) (by simp [(hn x).2])`. Rewrite using `[e2]`. Conclude with `⟨by simpa using integral_nonneg fun x => (hn x).1, by simp⟩`.
-/
theorem integral_nonneg_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : 0 ≤ (∫ x, f x ∂μ).re ∧ (∫ x, f x ∂μ).im = 0 := by
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) integral_complex_ofReal
    exact Complex.ext (by simp) (by simp [(hn x).2])
  rw [e2]
  exact ⟨by simpa using integral_nonneg fun x => (hn x).1, by simp⟩

/- English proof (translation)
Establish `e : ∀ x, f x = ((f x).re : ℂ)` using `fun x => Complex.ext (by simp) (by simp [(hn x).2])`. Establish `hr : Integrable (fun x => (f x).re) μ` using `hf.re`. Establish `h0 : 0 ≤ ∫ x, (f x).re ∂μ` using `integral_nonneg fun x => (hn x).1`. Establish `e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ)`. Conclude with `Eq.trans (integral_congr_ae (ae_of_all _ e)) integral_complex_ofReal`.

Establish `e3 : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x).re` using `fun x => by conv_lhs => rw [e x]`. Rewrite using `[← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hn x).1]`. Rewrite using `[lintegral_congr e3, ← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun x => (hn x).1), e2, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]`.
-/
theorem lintegral_enorm_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ)
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : ∫⁻ x, ‖f x‖ₑ ∂μ = ‖∫ x, f x ∂μ‖ₑ := by
  have e : ∀ x, f x = ((f x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [(hn x).2])
  have hr : Integrable (fun x => (f x).re) μ := hf.re
  have h0 : 0 ≤ ∫ x, (f x).re ∂μ := integral_nonneg fun x => (hn x).1
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    exact Eq.trans (integral_congr_ae (ae_of_all _ e)) integral_complex_ofReal
  have e3 : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x).re := fun x => by
    conv_lhs => rw [e x]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hn x).1]
  rw [lintegral_congr e3, ← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun x => (hn x).1), e2,
    ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, h⟩` from `h`. Conclude with `(GlobalTheory.RegSch.IkSchwartz.pure d hθ μ f g hg Φ h).1 a`. Consider the case `zero => exact integrable_zero _ _ _`.

Consider the case `add Φ Ψ _ _ h1 h2 => exact h1.add h2`. Consider the case `smul c Φ _ h => exact h.smul c`.
-/
theorem integrable_ik {θ : InfFam D} (hθ : IsInfFam θ) {T T' : HSp D} {t n : ℕ} (d : HypDec T T' t)
    (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure] {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n)
    (a : Mx D T'.rank n) : Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact (GlobalTheory.RegSch.IkSchwartz.pure d hθ μ f g hg Φ h).1 a
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

/- English proof (translation)
Use `isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)` as an intermediate fact. Take `⟨-, k2, -, -, k5, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T`. Establish `hB : BorelSpace (GA D T)` using `⟨rfl⟩`. Establish `hKB : BorelSpace K` using `Subtype.borelSpace _`. Establish `: CompactSpace K` using `isCompact_iff_compactSpace.1 hK`.

Establish `hc : Continuous fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x)` using `hΦ.comp (((continuous_mt T).comp continuous_subtype_val.inv).matrix_mul continuous_const)`. Conclude with `hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem integrable_K {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)} (hK : IsCompact (K : Set (GA D T))) (ν : Measure K)
    [IsProbabilityMeasure ν] {Φ : Mx D T.rank n → ℂ} (hΦ : Continuous Φ) (x : Mx D T.rank n) :
    Integrable (fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x)) ν := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hB : BorelSpace (GA D T) := ⟨rfl⟩
  have hKB : BorelSpace K := Subtype.borelSpace _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : Continuous fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x) :=
    hΦ.comp (((continuous_mt T).comp continuous_subtype_val.inv).matrix_mul continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting

open IkLintProof in

/- English proof (translation)
Introduce `D n t B W d I θ hθ M hM hn a`. Use `haveI := I.probK`. Take `⟨𝓕, hμ⟩` from `I.cov₁`. Use `haveI := hμ.1`. Establish `hK` using `(GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d I.good).2`.

Establish `hP : projS I.νK M ∈ schwartzA θ B.rank n` using `GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK _ hM`. Establish `hc : Continuous M` using `(GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1`. Establish `hi` using `fun x => integrable_K hK I.νK hc x`. Establish `inner : ∀ x, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) x)‖ₑ ∂I.νK = ‖projS I.νK M x‖ₑ` using `fun x => lintegral_enorm_eq (hi x) fun k => hn _`. Establish `pos : ∀ x, 0 ≤ (projS I.νK M x).re ∧ (projS I.νK M x).im = 0` using `fun x => integral_nonneg_real fun k => hn _`.

Rewrite using `[lintegral_congr fun U => inner _]`. Conclude with `lintegral_enorm_eq (integrable_ik hθ d I.μ₁ hP a) fun U => pos _`.
-/
theorem ikLint : IkLint := by
  intro D n t B W d I θ hθ M hM hn a
  haveI := I.probK
  obtain ⟨𝓕, hμ⟩ := I.cov₁
  haveI := hμ.1
  have hK := (GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d I.good).2
  have hP : projS I.νK M ∈ schwartzA θ B.rank n := GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B n I.l.K hK I.νK I.probK _ hM
  have hc : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hi := fun x => integrable_K hK I.νK hc x
  have inner : ∀ x, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) x)‖ₑ ∂I.νK = ‖projS I.νK M x‖ₑ :=
    fun x => lintegral_enorm_eq (hi x) fun k => hn _
  have pos : ∀ x, 0 ≤ (projS I.νK M x).re ∧ (projS I.νK M x).im = 0 :=
    fun x => integral_nonneg_real fun k => hn _
  rw [lintegral_congr fun U => inner _]
  exact lintegral_enorm_eq (integrable_ik hθ d I.μ₁ hP a) fun U => pos _

end GlobalTheory.CompanionTheory.ColumnSplitting

end
