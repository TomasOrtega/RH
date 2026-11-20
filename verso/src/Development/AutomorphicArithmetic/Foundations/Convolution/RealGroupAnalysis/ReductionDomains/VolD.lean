import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IdeleCover
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.IsClosedRangeNU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.UnfL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ _ M₀`. Take `⟨c, hc, hred⟩` from `UpperTheory.ConvolutionTheory.R2.red F`. Take `⟨C, ρ, hC, hρ, hcov⟩` from `M.ideleCover F c hc`. Take `⟨hSm, hfin⟩` from `M.siegJ F M₀ C ρ hC hρ`. Take `⟨⟨σ, hσ⟩, hcos⟩` from `M.rowCosets F`.

Use `set S : Set (G1 F) := {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} with hS`. Use `set u : G1 F → ℝ≥0∞ := Set.indicator S 1 with hu`. Establish `hum : Measurable u` using `measurable_one.indicator hSm`. Establish `hSinv : ∀ (b : A F) g, nU b * g ∈ S ↔ g ∈ S`. Establish `key : ∀ (b : A F) g, g ∈ S → nU b * g ∈ S`.

Introduce and unpack `b g ⟨b', n, x, hx, k, hk, rfl⟩`. Conclude with `⟨b + b', n, x, hx, k, hk, by rw [M.nU_add]; simp only [mul_assoc]⟩`. Use `fun b g => ⟨fun h => ?_, key b g⟩` and prove the remaining obligations. Use `key (-b) _ h` as an intermediate fact. Rewrite `this` using `[M.nU_neg, inv_mul_cancel_left]`. Then use the resulting hypothesis.

Establish `huinv : ∀ (b : A F) g, u (nU b * g) = u g`. Introduce `b g`. Distinguish the cases in `h : g ∈ S`. Rewrite using `[hu, Set.indicator_of_mem h, Set.indicator_of_mem ((hSinv b g).2 h)]`. Both sides reduce to the same expression.

Rewrite using `[hu, Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hSinv b g).1 h'))]`. Establish `hcover : ∀ g : G1 F, 1 ≤ ∑' r, u (ratS F (σ r) * g)`. Introduce `g`. Take `⟨γ, b, a, k, hk, heq, hle⟩` from `hred g`. Take `⟨t, n, x, hx, hta⟩` from `hcov a hle`.

Establish `hmem : mD (IdeleGroup.diagonal F t) * ratS F γ ∈ Gam F` using `(Gam F).mul_mem (M.mD_diag_mem t) ⟨γ, rfl⟩`. Take `⟨⟨r, ξ⟩, hp, -⟩` from `hcos σ hσ ⟨_, hmem⟩`. Establish `hp' : mD (IdeleGroup.diagonal F t) * ratS F γ = nU (rt ξ) * ratS F (σ r)` using `hp`. Establish `hin : nU (rt ξ) * (ratS F (σ r) * g) ∈ S`. Use `⟨((IdeleGroup.diagonal F t : (A F)ˣ) : A F) ^ 2 * b, n, x, hx, k, hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[← mul_assoc, ← hp', mul_assoc, heq, ← hta, M.mD_mul, ← mul_assoc, ← mul_assoc, M.mD_mul_nU]`. Simplify using `only [mul_assoc]`. Establish `hone : u (ratS F (σ r) * g) = 1`. Rewrite using `[← huinv (rt ξ), hu, Set.indicator_of_mem hin]`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation. Establish `hfs : ∀ g, ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) = u g`. Introduce `g`. Simplify using `only [huinv]`. Rewrite using `[lintegral_const, Measure.restrict_apply_univ, adeleMeasure_fundamentalSet, mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[M.unfL F M₀ σ u hσ hum (fun ξ g => huinv _ g)]`. Simplify using `only [hfs]`. Use `_ < ⊤ := hfin`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.volD :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M₀ : Meas F), M₀.μ M₀.D < ⊤ := by
  intro F _ _ _ M₀
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨C, ρ, hC, hρ, hcov⟩ := M.ideleCover F c hc
  obtain ⟨hSm, hfin⟩ := M.siegJ F M₀ C ρ hC hρ
  obtain ⟨⟨σ, hσ⟩, hcos⟩ := M.rowCosets F
  set S : Set (G1 F) := {g : G1 F | ∃ (b : A F) (n : ℕ), ∃ x ∈ C, ∃ k ∈ KK F, g = nU b * mD (ρ ^ n * x) * k} with hS
  set u : G1 F → ℝ≥0∞ := Set.indicator S 1 with hu
  have hum : Measurable u := measurable_one.indicator hSm
  have hSinv : ∀ (b : A F) g, nU b * g ∈ S ↔ g ∈ S := by
    have key : ∀ (b : A F) g, g ∈ S → nU b * g ∈ S := by
      rintro b g ⟨b', n, x, hx, k, hk, rfl⟩
      exact ⟨b + b', n, x, hx, k, hk, by rw [M.nU_add]; simp only [mul_assoc]⟩
    refine fun b g => ⟨fun h => ?_, key b g⟩
    have := key (-b) _ h
    rwa [M.nU_neg, inv_mul_cancel_left] at this
  have huinv : ∀ (b : A F) g, u (nU b * g) = u g := by
    intro b g
    by_cases h : g ∈ S
    · rw [hu, Set.indicator_of_mem h, Set.indicator_of_mem ((hSinv b g).2 h)]; rfl
    · rw [hu, Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hSinv b g).1 h'))]
  have hcover : ∀ g : G1 F, 1 ≤ ∑' r, u (ratS F (σ r) * g) := by
    intro g
    obtain ⟨γ, b, a, k, hk, heq, hle⟩ := hred g
    obtain ⟨t, n, x, hx, hta⟩ := hcov a hle
    have hmem : mD (IdeleGroup.diagonal F t) * ratS F γ ∈ Gam F :=
      (Gam F).mul_mem (M.mD_diag_mem t) ⟨γ, rfl⟩
    obtain ⟨⟨r, ξ⟩, hp, -⟩ := hcos σ hσ ⟨_, hmem⟩
    have hp' : mD (IdeleGroup.diagonal F t) * ratS F γ = nU (rt ξ) * ratS F (σ r) := hp
    have hin : nU (rt ξ) * (ratS F (σ r) * g) ∈ S := by
      refine ⟨((IdeleGroup.diagonal F t : (A F)ˣ) : A F) ^ 2 * b, n, x, hx, k, hk, ?_⟩
      rw [← mul_assoc, ← hp', mul_assoc, heq, ← hta, M.mD_mul, ← mul_assoc, ← mul_assoc, M.mD_mul_nU]
      simp only [mul_assoc]
    have hone : u (ratS F (σ r) * g) = 1 := by
      rw [← huinv (rt ξ), hu, Set.indicator_of_mem hin]; rfl
    calc (1 : ℝ≥0∞) = u (ratS F (σ r) * g) := hone.symm
      _ ≤ ∑' r, u (ratS F (σ r) * g) := ENNReal.le_tsum r
  have hfs : ∀ g, ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) = u g := by
    intro g
    simp only [huinv]
    rw [lintegral_const, Measure.restrict_apply_univ, adeleMeasure_fundamentalSet, mul_one]
  calc M₀.μ M₀.D = ∫⁻ _ in M₀.D, 1 ∂M₀.μ := by simp
    _ ≤ ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := lintegral_mono fun g => hcover g
    _ = M.J0 M₀ u := by
      rw [M.unfL F M₀ σ u hσ hum (fun ξ g => huinv _ g)]
      simp only [hfs]
    _ < ⊤ := hfin
