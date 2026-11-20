import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockActMemRangeMapSubtype
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapEqOfMemNabStd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramLocallyUnimodular

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.PairInt

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Distinguish the cases in `h0 : a = 0`. Rewrite using `[h0, zero_mul, ValuationRepresentative.vw_zero]`. Distinguish the cases in `h1 : b = 0`. Rewrite using `[h1, mul_zero, ValuationRepresentative.vw_zero]`. Rewrite using `[ValuationRepresentative.vw_mul w a b h0 h1]`.

Conclude with `add_nonneg ha hb`.
-/
theorem val_mul_nonneg (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : 0 ≤ vw w a) (hb : 0 ≤ vw w b) :
    0 ≤ vw w (a * b) := by
  by_cases h0 : a = 0
  · rw [h0, zero_mul, ValuationRepresentative.vw_zero]
  by_cases h1 : b = 0
  · rw [h1, mul_zero, ValuationRepresentative.vw_zero]
  rw [ValuationRepresentative.vw_mul w a b h0 h1]
  exact add_nonneg ha hb

/- English proof (translation)
Distinguish the cases in `h0 : a = 0`. Substitute `h0` using the available equality. Break down `k with _ | k` into its components or cases. Rewrite using `[pow_zero, ValuationRepresentative.vw_one]`. Rewrite using `[pow_succ, mul_zero, ValuationRepresentative.vw_zero]`.

Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, ValuationRepresentative.vw_one]`. Consider the case `succ k ih => rw [pow_succ, ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ h0) h0, ih, ha, add_zero]`.
-/
theorem val_pow_eq_zero (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : vw w a = 0) (k : ℕ) : vw w (a ^ k) = 0 := by
  by_cases h0 : a = 0
  · subst h0
    rcases k with _ | k
    · rw [pow_zero, ValuationRepresentative.vw_one]
    · rw [pow_succ, mul_zero, ValuationRepresentative.vw_zero]
  induction k with
  | zero => rw [pow_zero, ValuationRepresentative.vw_one]
  | succ k ih => rw [pow_succ, ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ h0) h0, ih, ha, add_zero]

/- English proof (translation)
Take `⟨k, rfl | rfl⟩` from `e.eq_nat_or_neg`. Rewrite using `[zpow_natCast, val_pow_eq_zero w ha]`. Rewrite using `[zpow_neg, zpow_natCast, ValuationRepresentative.vw_inv, val_pow_eq_zero w ha, neg_zero]`.
-/
theorem val_zpow_eq_zero (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : vw w a = 0) (e : ℤ) : vw w (a ^ e) = 0 := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · rw [zpow_natCast, val_pow_eq_zero w ha]
  · rw [zpow_neg, zpow_natCast, ValuationRepresentative.vw_inv, val_pow_eq_zero w ha, neg_zero]

/- English proof (translation)
The claim follows from `Finset.prod_induction f (fun a => 0 ≤ vw w a) (fun _ _ ha hb => val_mul_nonneg w ha hb) (ValuationRepresentative.vw_one w).ge hf`.
-/
theorem val_prod_nonneg (w : HeightOneSpectrum (𝓞 K)) {ι : Type} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, 0 ≤ vw w (f i)) : 0 ≤ vw w (∏ i ∈ s, f i) :=
  Finset.prod_induction f (fun a => 0 ≤ vw w a) (fun _ _ ha hb => val_mul_nonneg w ha hb)
    (ValuationRepresentative.vw_one w).ge hf

/- English proof (translation)
Introduce `K _ _ _ ι _ n lam G M hG hdet hM x hx y hy`. Take `⟨hglob, hloc⟩` from `GlobalTheory.LocInt.localIntegrality K`. Use `hglob _ fun w => ?_` and prove the remaining obligations. Use `choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ).1 (conjPl w)`. Use `choose B' hB' using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ).1 w`.

Establish `hx' : x.1 ∈ nabP lam M` using `hx`. Establish `hy' : y.1 ∈ nabP lam M` using `hy`. Simplify using `only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars] at hx' hy'`. Establish `hF` using `hx' (conjPl w) B hB`. Establish `hF'` using `hy' w B' hB'`.

Establish `ex : x.1 = actP lam B (actP lam B⁻¹ x.1)` using `by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]`. Establish `ey : y.1 = actP lam B' (actP lam B'⁻¹ y.1)` using `by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]`. Take `⟨q, hq, hq'⟩` from `extNormPos K ι n lam`. Establish `hne : extNorm K lam ≠ 0`. Rewrite using `[hq']`.

Simplify using `using hq.ne'`. Establish `hP` using `fun τ => GlobalTheory.GramLoc.gram_locally_unimodular K n (G τ) (M τ) (hG τ) (hdet τ) (hM τ) w (B τ) (B' τ) (hB τ) (hB' τ)`. Rewrite using `[pairK_apply, ex, ey, pairTransport K ι n lam G B B', pairP_apply, ← mul_assoc, mul_div_cancel₀ _ hne, fockL_apply]`. Use `val_mul_nonneg w ?_ ?_` and prove the remaining obligations. Conclude with `val_prod_nonneg w _ _ fun τ _ => (val_zpow_eq_zero w (hP τ).2 _).ge`.

Conclude with `GlobalTheory.TestLat.vw_fockS_blockAct_nonneg K ι n w _ _ _ (hloc ι n lam (conjPl w) _ hF) (hloc ι n lam w _ hF') fun τ a b => (hP τ).1 b a`.
-/
theorem extNorm_mul_pairK_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, (G τ)ᴴ = G τ) → (∀ τ, IsUnit (G τ).det) → (∀ τ, IsSelfDualK (G τ) (M τ)) → ∀ x ∈ nabK lam M, ∀ y ∈ nabK lam M, extNorm K lam * pairK lam G x y ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ _ ι _ n lam G M hG hdet hM x hx y hy
  obtain ⟨hglob, hloc⟩ := GlobalTheory.LocInt.localIntegrality K
  refine hglob _ fun w => ?_
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ).1 (conjPl w)
  choose B' hB' using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ).1 w
  have hx' : x.1 ∈ nabP lam M := hx
  have hy' : y.1 ∈ nabP lam M := hy
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars] at hx' hy'
  have hF := hx' (conjPl w) B hB
  have hF' := hy' w B' hB'
  have ex : x.1 = actP lam B (actP lam B⁻¹ x.1) := by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  have ey : y.1 = actP lam B' (actP lam B'⁻¹ y.1) := by rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  obtain ⟨q, hq, hq'⟩ := extNormPos K ι n lam
  have hne : extNorm K lam ≠ 0 := by
    rw [hq']
    simpa using hq.ne'
  have hP := fun τ => GlobalTheory.GramLoc.gram_locally_unimodular K n (G τ) (M τ) (hG τ) (hdet τ) (hM τ) w (B τ) (B' τ) (hB τ) (hB' τ)
  rw [pairK_apply, ex, ey, pairTransport K ι n lam G B B', pairP_apply, ← mul_assoc, mul_div_cancel₀ _ hne,
    fockL_apply]
  refine val_mul_nonneg w ?_ ?_
  · exact val_prod_nonneg w _ _ fun τ _ => (val_zpow_eq_zero w (hP τ).2 _).ge
  · exact GlobalTheory.TestLat.vw_fockS_blockAct_nonneg K ι n w _ _ _ (hloc ι n lam (conjPl w) _ hF) (hloc ι n lam w _ hF')
      fun τ a b => (hP τ).1 b a

end GlobalTheory.PairInt
