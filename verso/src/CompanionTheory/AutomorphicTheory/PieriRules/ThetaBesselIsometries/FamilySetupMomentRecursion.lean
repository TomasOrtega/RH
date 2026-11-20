import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ImportsTer
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyExistsAndAny
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsLowestKFiniteVectorDiscreteSeriesStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModularStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModuleStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyRecursionStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.ProductMomentBoundDensityMassOneImports
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyProductBoundConstantLeImports
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProd

/- English proof (translation)
Introduce `hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν hnz`. Establish `hK : PI.KFinSmooth` using `hH.1.2.2.1`. Establish `hNum` using `hS.1`. Establish `hFam` using `hS.2.1`. Establish `hSide` using `hS.2.2.1`.

Establish `hSF` using `hS.2.2.2`. Establish `hk : 1 ≤ k` using `hNum.1`. Establish `hν0 : n1 ν ≤ q0` using `le_trans (Nat.le_add_right _ _) hν`. Take `⟨Q, hQ⟩` from `(GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk`. Establish `hQu : IsUnit Q` using `hQ.1.1`.

Establish `hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub, n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E`. Introduce `ν'`. Distinguish the cases in `h' : n1 ν' ≤ q0`. Take `⟨E, hE⟩` from `GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu`. Conclude with `⟨E, fun _ => hE⟩`.

Conclude with `⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩`. Use `choose E hE using hE`. Establish `hDS` using `hFam ν hν0`. Take `⟨w, hw1, -, hwK, hwF⟩` from `GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1`. Establish `hMod` using `GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1`.

Establish `hLev` using `GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF`. Establish `hw1' : ‖(w : (R ν).H)‖ = 1` using `hw1`. Establish `hwsm : (w : (R ν).H) ∈ (R ν).sm` using `w.2`. Use `⟨(w : (R ν).H), hwsm, hw1', ?_⟩` and prove the remaining obligations. Take `⟨hG, -, hlen, hmeas⟩` from `GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide`.

Take `⟨hBeL, hdg, -⟩` from `hSF ν hν0`. Establish `hT : 0 < Formalism.QuantumDeterminants.Tz k r z` using `hSide.2.1`. Take `⟨⟨hb1, hb2, -, -, -⟩, -⟩` from `GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum`. Establish `hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2`. Introduce `q hq`.

Establish `: (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2` using `Nat.pow_le_pow_left (by omega) 2`. Use linear arithmetic over natural numbers and integers. Establish `hb : (1 : ℝ) ≤ b` using `by linarith`. Establish `hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2)))`. Establish `: 0 ≤ bv` using `by linarith`.

Check the signs of the components of the expression. Establish `hmain` using `GlobalTheory.T.product_moment_bound_density_mass_one (Formalism.QuantumDeterminants.Mt k r) νq r (fun a x => lenA k r z (Matrix.of x) a) (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) …`. Apply the tactic sequence `have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm`. Simplify `this)` using `only [one_mul, hw1', one_pow, ENNReal.ofReal_one]`. Use `hA (one_le_pow₀ hb)`.

Use the proof step `(fun q hq => by`. Use `GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν (by omega) 0 (hq2 q hq) w hLev` as an intermediate fact. Simplify `this)` using `only [hw1, one_pow, mul_one]`. Use the proof step `(fun a q hq => by`. Use `GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0 0 q (hq2 q hq) a w hLev` as an intermediate fact.

Simplify `this)` using `only [hw1, one_pow, mul_one]`. Use `hmain.trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (mul_nonneg hA (by positivity)) (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT) _`.
-/
theorem product_moment : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (l ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a, lenA k r z (Matrix.of x) a ^ 2) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ (r + 1)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν hnz
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  obtain ⟨w, hw1, -, hwK, hwF⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hK k r _ _ (R ν) hDS Q (E ν) hQ (hE ν hν0).1
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDS Q (E ν) hQ (hE ν hν0).1
  have hLev := GlobalTheory.lev_zero_of_kHighest _ _ _ (E ν) _ w hMod.1 hMod.2.1 hwK hwF
  have hw1' : ‖(w : (R ν).H)‖ = 1 := hw1
  have hwsm : (w : (R ν).H) ∈ (R ν).sm := w.2
  refine ⟨(w : (R ν).H), hwsm, hw1', ?_⟩
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hq2 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hmain := GlobalTheory.T.product_moment_bound_density_mass_one (Formalism.QuantumDeterminants.Mt k r) νq r (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
    hlen
    (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
    (((hmeas (l ν) hBeL.1 w hwsm).norm.aemeasurable.pow_const 2).const_mul _)
    (fun x => mul_nonneg hdg.le (by positivity))
    (by
      have := ((GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν0).2 hnz).2 w hwsm
      simpa only [one_mul, hw1', one_pow, ENNReal.ofReal_one] using this)
    hA (one_le_pow₀ hb)
    (fun q hq => by
      have := GlobalTheory.T.family_setup_cayley_recursion hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q ν
        (by omega) 0 (hq2 q hq) w hLev
      simpa only [hw1, one_pow, mul_one] using this)
    (fun a q hq => by
      have := GlobalTheory.T.family_setup_cayley_bound hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν0
        0 q (hq2 q hq) a w hLev
      simpa only [hw1, one_pow, mul_one] using this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (by positivity))
    (GlobalTheory.T.numericalFamily_productBound_constant_le k r lam u b bv ga h q0 _ hNum hT) _

end GlobalTheory.MomProd
