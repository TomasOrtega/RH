import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugateStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set
open scoped Manifold

namespace PlaceWeightSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockSq (z : (Σ k, ι k) → ℂ) (k : K) : ℝ := ∑ i, ‖z ⟨k, i⟩‖ ^ 2

def prMap (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩) / (blockSq z q.1 : ℂ)

def nzBlocks (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def unitBlocks (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ k, blockSq z k = 1}

/- English proof (translation)
Unfold `blockSq`. Simplify using `only [norm_mul, mul_pow, Finset.mul_sum]`.
-/
theorem blockSq_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (k : K) :
    blockSq (fun p => c p.1 * z p) k = ‖c k‖ ^ 2 * blockSq z k := by
  unfold blockSq
  simp only [norm_mul, mul_pow, Finset.mul_sum]

/- English proof (translation)
Take `⟨i, hi⟩` from `h`. Unfold `blockSq`. Conclude with `Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩`.
-/
theorem blockSq_pos {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < blockSq z k := by
  obtain ⟨i, hi⟩ := h
  unfold blockSq
  exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

/- English proof (translation)
Use function extensionality and compare the values at `q`. Establish `hq : c q.1 * (starRingEnd ℂ) (c q.1) ≠ 0` using `mul_ne_zero (hc _) ((map_ne_zero _).mpr (hc _))`. Establish `hn : ((‖c q.1‖ ^ 2 : ℝ) : ℂ) = c q.1 * (starRingEnd ℂ) (c q.1)`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Unfold `prMap`.

Rewrite using `[blockSq_smul, Complex.ofReal_mul, hn, map_mul, show c q.1 * z ⟨q.1, q.2.1⟩ * ((starRingEnd ℂ) (c q.1) * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)) = (c q.1 * (starRingEnd ℂ) (c q.1)) * (z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)) by ring, mul_div_mul_left _ _ hq]`.
-/
theorem prMap_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    prMap (fun p => c p.1 * z p) = prMap z := by
  funext q
  have hq : c q.1 * (starRingEnd ℂ) (c q.1) ≠ 0 := mul_ne_zero (hc _) ((map_ne_zero _).mpr (hc _))
  have hn : ((‖c q.1‖ ^ 2 : ℝ) : ℂ) = c q.1 * (starRingEnd ℂ) (c q.1) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold prMap
  rw [blockSq_smul, Complex.ofReal_mul, hn, map_mul,
    show c q.1 * z ⟨q.1, q.2.1⟩ * ((starRingEnd ℂ) (c q.1) * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)) =
      (c q.1 * (starRingEnd ℂ) (c q.1)) * (z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)) by ring,
    mul_div_mul_left _ _ hq]

/- English proof (translation)
Establish `h : nzBlocks K ι = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using `[nzBlocks]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_nzBlocks : IsOpen (nzBlocks K ι) := by
  have h : nzBlocks K ι = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp [nzBlocks]
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

/- English proof (translation)
Unfold `blockSq`. Conclude with `ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))`.
-/
theorem blockSq_contDiff (k : K) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun z : (Σ k, ι k) → ℂ => blockSq z k := by
  unfold blockSq
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))

/- English proof (translation)
Rewrite using `[contDiffOn_pi]`. Introduce `q`. Establish `hq : (fun z : (Σ k, ι k) → ℂ => prMap z q) = fun z => (blockSq z q.1)⁻¹ • (z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩))`. Use function extensionality and compare the values at `z`. Rewrite using `[Complex.real_smul, Complex.ofReal_inv, prMap, div_eq_inv_mul]`.

Rewrite using `[hq]`. Establish `hs : ContDiff ℝ n fun z : (Σ k, ι k) → ℂ => (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)`. Establish `h0` using `Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ (n := n) (⟨q.1, q.2.2⟩ : Σ k, ι k))`. Simplify `h0` using `[Function.comp_def]`. Establish `h1 : ContDiffOn ℝ n (fun z : (Σ k, ι k) → ℂ => (blockSq z q.1)⁻¹) (nzBlocks K ι)` using `(blockSq_contDiff q.1).contDiffOn.inv fun z hz => (blockSq_pos ((show ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 from hz) q.1)).ne'`.

Establish `h2 : ContDiffOn ℝ n (fun z : (Σ k, ι k) → ℂ => z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)) (nzBlocks K ι)` using `((contDiff_apply ℝ ℂ (n := n) (⟨q.1, q.2.1⟩ : Σ k, ι k)).mul hs).contDiffOn`. Conclude with `ContDiffOn.smul h1 h2`.
-/
theorem prMap_contDiffOn {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (prMap (K := K) (ι := ι)) (nzBlocks K ι) := by
  rw [contDiffOn_pi]
  intro q
  have hq : (fun z : (Σ k, ι k) → ℂ => prMap z q) = fun z =>
      (blockSq z q.1)⁻¹ • (z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩)) := by
    funext z
    rw [Complex.real_smul, Complex.ofReal_inv, prMap, div_eq_inv_mul]
  rw [hq]
  have hs : ContDiff ℝ n fun z : (Σ k, ι k) → ℂ => (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩) := by
    have h0 := Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ (n := n) (⟨q.1, q.2.2⟩ : Σ k, ι k))
    simpa [Function.comp_def] using h0
  have h1 : ContDiffOn ℝ n (fun z : (Σ k, ι k) → ℂ => (blockSq z q.1)⁻¹) (nzBlocks K ι) :=
    (blockSq_contDiff q.1).contDiffOn.inv fun z hz =>
      (blockSq_pos ((show ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 from hz) q.1)).ne'
  have h2 : ContDiffOn ℝ n (fun z : (Σ k, ι k) → ℂ => z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ) (z ⟨q.1, q.2.2⟩))
      (nzBlocks K ι) :=
    ((contDiff_apply ℝ ℂ (n := n) (⟨q.1, q.2.1⟩ : Σ k, ι k)).mul hs).contDiffOn
  exact ContDiffOn.smul h1 h2

/- English proof (translation)
Conclude with `(prMap_contDiffOn (K := K) (ι := ι) (n := 0)).continuousOn.continuousAt (isOpen_nzBlocks.mem_nhds hz)`.
-/
theorem prMap_continuousAt {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) :
    ContinuousAt (prMap (K := K) (ι := ι)) z := by
  exact (prMap_contDiffOn (K := K) (ι := ι) (n := 0)).continuousOn.continuousAt
    (isOpen_nzBlocks.mem_nhds hz)

/- English proof (translation)
Establish `hz1 : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0` using `hz`. Establish `hB : ∀ k, 0 < blockSq z k` using `fun k => blockSq_pos (hz1 k)`. Establish `hB' : ∀ k, 0 < blockSq z' k` using `fun k => blockSq_pos ((show ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hz') k)`. Use `choose i0 hi0 using hz1`. Establish `key : ∀ k i j, z ⟨k, i⟩ * (starRingEnd ℂ) (z ⟨k, j⟩) / (blockSq z k : ℂ) = z' ⟨k, i⟩ * (starRingEnd ℂ) (z' ⟨k, j⟩) / (blockSq z' k : ℂ)` using `fun k i j => congrFun h ⟨k, i, j⟩`.

Establish `h4 : ∀ k, (blockSq z k : ℂ) ≠ 0` using `fun k => by exact_mod_cast (hB k).ne'`. Establish `h3 : ∀ k, (blockSq z' k : ℂ) ≠ 0` using `fun k => by exact_mod_cast (hB' k).ne'`. Establish `hz'0 : ∀ k, z' ⟨k, i0 k⟩ ≠ 0`. Introduce `k h0`. Establish `e` using `key k (i0 k) (i0 k)`.

Rewrite `e` using `[h0, map_zero, mul_zero, zero_div, div_eq_zero_iff, mul_eq_zero, map_eq_zero, or_self]`. Break down `e with e | e` into its components or cases. Conclude with `hi0 k e`. Conclude with `h4 k e`. Establish `h1 : ∀ k, (starRingEnd ℂ) (z ⟨k, i0 k⟩) ≠ 0` using `fun k => (map_ne_zero _).mpr (hi0 k)`.

Establish `h2 : ∀ k, (starRingEnd ℂ) (z' ⟨k, i0 k⟩) ≠ 0` using `fun k => (map_ne_zero _).mpr (hz'0 k)`. Use `⟨fun k => (starRingEnd ℂ) (z ⟨k, i0 k⟩) * (blockSq z' k : ℂ) / ((blockSq z k : ℂ) * (starRingEnd ℂ) (z' ⟨k, i0 k⟩)), fun k => div_ne_zero (mul_ne_zero (h1 k) (h3 k)) (mul_ne_zero (h4 k) (h2 k)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Take `⟨k, i⟩` from `p`. Establish `e` using `key k i (i0 k)`.

Rewrite `e` using `[div_eq_div_iff (h4 k) (h3 k)]`. Use `show z' ⟨k, i⟩ = (starRingEnd ℂ) (z ⟨k, i0 k⟩) * (blockSq z' k : ℂ) / ((blockSq z k : ℂ) * (starRingEnd ℂ) (z' ⟨k, i0 k⟩)) * z ⟨k, i⟩`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (h4 k) (h2 k))]`. Take the linear combination `(-1 : ℂ) * e`.
-/
theorem orbit_of_prMap_eq {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) (hz' : z' ∈ nzBlocks K ι)
    (h : prMap z = prMap z') : ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = fun p => c p.1 * z p := by
  have hz1 : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  have hB : ∀ k, 0 < blockSq z k := fun k => blockSq_pos (hz1 k)
  have hB' : ∀ k, 0 < blockSq z' k := fun k => blockSq_pos ((show ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hz') k)
  choose i0 hi0 using hz1
  have key : ∀ k i j, z ⟨k, i⟩ * (starRingEnd ℂ) (z ⟨k, j⟩) / (blockSq z k : ℂ) =
      z' ⟨k, i⟩ * (starRingEnd ℂ) (z' ⟨k, j⟩) / (blockSq z' k : ℂ) := fun k i j =>
    congrFun h ⟨k, i, j⟩
  have h4 : ∀ k, (blockSq z k : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  have h3 : ∀ k, (blockSq z' k : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB' k).ne'
  have hz'0 : ∀ k, z' ⟨k, i0 k⟩ ≠ 0 := by
    intro k h0
    have e := key k (i0 k) (i0 k)
    rw [h0, map_zero, mul_zero, zero_div, div_eq_zero_iff, mul_eq_zero, map_eq_zero, or_self] at e
    rcases e with e | e
    · exact hi0 k e
    · exact h4 k e
  have h1 : ∀ k, (starRingEnd ℂ) (z ⟨k, i0 k⟩) ≠ 0 := fun k => (map_ne_zero _).mpr (hi0 k)
  have h2 : ∀ k, (starRingEnd ℂ) (z' ⟨k, i0 k⟩) ≠ 0 := fun k => (map_ne_zero _).mpr (hz'0 k)
  refine ⟨fun k => (starRingEnd ℂ) (z ⟨k, i0 k⟩) * (blockSq z' k : ℂ) /
      ((blockSq z k : ℂ) * (starRingEnd ℂ) (z' ⟨k, i0 k⟩)), fun k =>
      div_ne_zero (mul_ne_zero (h1 k) (h3 k)) (mul_ne_zero (h4 k) (h2 k)), ?_⟩
  funext p
  obtain ⟨k, i⟩ := p
  have e := key k i (i0 k)
  rw [div_eq_div_iff (h4 k) (h3 k)] at e
  show z' ⟨k, i⟩ = (starRingEnd ℂ) (z ⟨k, i0 k⟩) * (blockSq z' k : ℂ) /
      ((blockSq z k : ℂ) * (starRingEnd ℂ) (z' ⟨k, i0 k⟩)) * z ⟨k, i⟩
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (h4 k) (h2 k))]
  linear_combination (-1 : ℂ) * e

/- English proof (translation)
Apply `Metric.isCompact_of_isClosed_isBounded` to reduce the goal to its premises. Establish `h : unitBlocks K ι = ⋂ k, (fun z : (Σ k, ι k) → ℂ => blockSq z k) ⁻¹' {1}`. Use extensionality with `z`. Simplify using `[unitBlocks]`. Rewrite using `[h]`.

Conclude with `isClosed_iInter fun k => isClosed_singleton.preimage (blockSq_contDiff (n := 0) k).continuous`. Rewrite using `[Metric.isBounded_iff_subset_closedBall 0]`. Use `⟨1, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce and unpack `⟨k, i⟩`.

Establish `h1 : blockSq z k = 1` using `(show ∀ k, blockSq z k = 1 from hz) k`. Establish `h2 : ‖z ⟨k, i⟩‖ ^ 2 ≤ blockSq z k`. Unfold `blockSq`. Conclude with `Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)`. Rewrite `h2` using `[h1]`.

Use polynomial arithmetic with `[norm_nonneg (z ⟨k, i⟩)]`.
-/
theorem isCompact_unitBlocks : IsCompact (unitBlocks K ι) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h : unitBlocks K ι = ⋂ k, (fun z : (Σ k, ι k) → ℂ => blockSq z k) ⁻¹' {1} := by
      ext z
      simp [unitBlocks]
    rw [h]
    exact isClosed_iInter fun k => isClosed_singleton.preimage (blockSq_contDiff (n := 0) k).continuous
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun z hz => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    have h1 : blockSq z k = 1 := (show ∀ k, blockSq z k = 1 from hz) k
    have h2 : ‖z ⟨k, i⟩‖ ^ 2 ≤ blockSq z k := by
      unfold blockSq
      exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)
    rw [h1] at h2
    nlinarith [norm_nonneg (z ⟨k, i⟩)]

/- English proof (translation)
Introduce `z hz`. Use `show ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0`. Introduce `k`. Assume the negation of the conclusion as `h`. Establish `h' : ∀ i, z ⟨k, i⟩ = 0` using `fun i => by`.

Assume the negation of the conclusion as `hi`. Conclude with `h ⟨i, hi⟩`. Establish `h0 : blockSq z k = 0` using `by simp [blockSq, h']`. Establish `h1 : blockSq z k = 1` using `(show ∀ k, blockSq z k = 1 from hz) k`. Rewrite `h1` using `[h0]`.

Conclude with `zero_ne_one h1`.
-/
theorem unitBlocks_subset : unitBlocks K ι ⊆ nzBlocks K ι := by
  intro z hz
  show ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  intro k
  by_contra h
  have h' : ∀ i, z ⟨k, i⟩ = 0 := fun i => by
    by_contra hi
    exact h ⟨i, hi⟩
  have h0 : blockSq z k = 0 := by simp [blockSq, h']
  have h1 : blockSq z k = 1 := (show ∀ k, blockSq z k = 1 from hz) k
  rw [h0] at h1
  exact zero_ne_one h1

/- English proof (translation)
Establish `hz1 : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0` using `hz`. Use `⟨fun k => (((Real.sqrt (blockSq z k))⁻¹ : ℝ) : ℂ), fun k => ?_, ?_⟩` and prove the remaining obligations. Use `show (((Real.sqrt (blockSq z k))⁻¹ : ℝ) : ℂ) ≠ 0`. Establish `h` using `Real.sqrt_pos.mpr (blockSq_pos (hz1 k))`. Conclude with `(inv_pos.mpr h).ne'` after adjusting the coercions.

Use `show ∀ k, blockSq _ k = 1`. Introduce `k`. Establish `hB` using `blockSq_pos (hz1 k)`. Rewrite using `[blockSq_smul (fun k => (((Real.sqrt (blockSq z k))⁻¹ : ℝ) : ℂ)) z k, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hB.le, inv_mul_cancel₀ hB.ne']`.
-/
theorem exists_normalize {z : (Σ k, ι k) → ℂ} (hz : z ∈ nzBlocks K ι) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (fun p => c p.1 * z p) ∈ unitBlocks K ι := by
  have hz1 : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  refine ⟨fun k => (((Real.sqrt (blockSq z k))⁻¹ : ℝ) : ℂ), fun k => ?_, ?_⟩
  · show (((Real.sqrt (blockSq z k))⁻¹ : ℝ) : ℂ) ≠ 0
    have h := Real.sqrt_pos.mpr (blockSq_pos (hz1 k))
    exact_mod_cast (inv_pos.mpr h).ne'
  · show ∀ k, blockSq _ k = 1
    intro k
    have hB := blockSq_pos (hz1 k)
    rw [blockSq_smul (fun k => (((Real.sqrt (blockSq z k))⁻¹ : ℝ) : ℂ)) z k, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hB.le, inv_mul_cancel₀ hB.ne']

variable {Ω : Type} [Field Ω] {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `⟨mcPts_smul ?_ c hc hz.1, fun a d g h hg hh e => ?_⟩` and prove the remaining obligations. Conclude with `GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y`. Establish `e2` using `hz.2 a d g h hg hh e`. Simplify using `only [evC] at e2 ⊢`. Rewrite using `[eval_smul_homog g d hg, eval_smul_homog h d hh, e2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ptOver_smul {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : PtOver y φ σ z) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) :
    PtOver y φ σ (fun p => c p.1 * z p) := by
  refine ⟨mcPts_smul ?_ c hc hz.1, fun a d g h hg hh e => ?_⟩
  · exact GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y
  · have e2 := hz.2 a d g h hg hh e
    simp only [evC] at e2 ⊢
    rw [eval_smul_homog g d hg, eval_smul_homog h d hh, e2]
    ring

def overSet (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) : Set ((Σ k, ι k) → ℂ) :=
  {z | z ∈ unitBlocks K ι ∧ PtOver y φ σ z}

/- English proof (translation)
Conclude with `MvPolynomial.continuous_eval _`.
-/
theorem evC_continuous (f : MRing ι) : Continuous fun z : (Σ k, ι k) → ℂ => evC z f := by
  exact MvPolynomial.continuous_eval _

/- English proof (translation)
Establish `hset : overSet y φ σ = unitBlocks K ι ∩ ((⋂ f ∈ mCoordIdeal y, {z : (Σ k, ι k) → ℂ | evC z f = 0}) ∩ ⋂ a : F, ⋂ d : K → ℕ, ⋂ g : MRing ι, ⋂ h : MRing ι, {z : (Σ k, ι k) → ℂ | IsMultiHomog g d → IsMultiHomog h d → aeval y g = φ a * aeval y h → evC z g = σ a * evC z h})`. Use extensionality with `z`. Simplify using `only [overSet, PtOver, mcPts, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, ⟨_, h1⟩, h2⟩`.

Conclude with `⟨hu, h1, h2⟩`. Introduce and unpack `⟨hu, h1, h2⟩`. Conclude with `⟨hu, ⟨unitBlocks_subset hu, h1⟩, h2⟩`. Rewrite using `[hset]`. Use `isCompact_unitBlocks.inter_right (IsClosed.inter (isClosed_biInter fun f _ => isClosed_eq (evC_continuous f) continuous_const) ?_)` and prove the remaining obligations.

Use `isClosed_iInter fun a => isClosed_iInter fun d => isClosed_iInter fun g => isClosed_iInter fun h => ?_` and prove the remaining obligations. Distinguish the cases in `hp : IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y g = φ a * aeval y h`. Establish `hs : {z : (Σ k, ι k) → ℂ | IsMultiHomog g d → IsMultiHomog h d → aeval y g = φ a * aeval y h → evC z g = σ a * evC z h} = {z | evC z g = σ a * evC z h}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq]`.

Conclude with `⟨fun H => H hp.1 hp.2.1 hp.2.2, fun H _ _ _ => H⟩`. Rewrite using `[hs]`. Conclude with `isClosed_eq (evC_continuous g) (continuous_const.mul (evC_continuous h))`. Establish `hs : {z : (Σ k, ι k) → ℂ | IsMultiHomog g d → IsMultiHomog h d → aeval y g = φ a * aeval y h → evC z g = σ a * evC z h} = Set.univ`. Use extensionality with `z`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Introduce `h1 h2 h3`. Conclude with `absurd ⟨h1, h2, h3⟩ hp`. Rewrite using `[hs]`. Conclude with `isClosed_univ`.
-/
theorem isCompact_overSet (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) :
    IsCompact (overSet y φ σ) := by
  have hset : overSet y φ σ = unitBlocks K ι ∩
      ((⋂ f ∈ mCoordIdeal y, {z : (Σ k, ι k) → ℂ | evC z f = 0}) ∩
        ⋂ a : F, ⋂ d : K → ℕ, ⋂ g : MRing ι, ⋂ h : MRing ι,
          {z : (Σ k, ι k) → ℂ | IsMultiHomog g d → IsMultiHomog h d → aeval y g = φ a * aeval y h →
            evC z g = σ a * evC z h}) := by
    ext z
    simp only [overSet, PtOver, mcPts, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hu, ⟨_, h1⟩, h2⟩
      exact ⟨hu, h1, h2⟩
    · rintro ⟨hu, h1, h2⟩
      exact ⟨hu, ⟨unitBlocks_subset hu, h1⟩, h2⟩
  rw [hset]
  refine isCompact_unitBlocks.inter_right
    (IsClosed.inter (isClosed_biInter fun f _ => isClosed_eq (evC_continuous f) continuous_const) ?_)
  refine isClosed_iInter fun a => isClosed_iInter fun d => isClosed_iInter fun g =>
    isClosed_iInter fun h => ?_
  by_cases hp : IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y g = φ a * aeval y h
  · have hs : {z : (Σ k, ι k) → ℂ | IsMultiHomog g d → IsMultiHomog h d →
        aeval y g = φ a * aeval y h → evC z g = σ a * evC z h} = {z | evC z g = σ a * evC z h} := by
      ext z
      simp only [Set.mem_setOf_eq]
      exact ⟨fun H => H hp.1 hp.2.1 hp.2.2, fun H _ _ _ => H⟩
    rw [hs]
    exact isClosed_eq (evC_continuous g) (continuous_const.mul (evC_continuous h))
  · have hs : {z : (Σ k, ι k) → ℂ | IsMultiHomog g d → IsMultiHomog h d →
        aeval y g = φ a * aeval y h → evC z g = σ a * evC z h} = Set.univ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2 h3
      exact absurd ⟨h1, h2, h3⟩ hp
    rw [hs]
    exact isClosed_univ

/- English proof (translation)
Take `⟨c, hc, hu⟩` from `exists_normalize hz.1.1`. Conclude with `⟨_, ⟨hu, ptOver_smul hz c hc⟩, prMap_smul c z hc⟩`.
-/
theorem prMap_mem_image {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : PtOver y φ σ z) : prMap z ∈ prMap '' overSet y φ σ := by
  obtain ⟨c, hc, hu⟩ := exists_normalize hz.1.1
  exact ⟨_, ⟨hu, ptOver_smul hz c hc⟩, prMap_smul c z hc⟩

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce and unpack `w ⟨z, ⟨hzu, hzp⟩, rfl⟩ ⟨z', ⟨hzu', hzp'⟩, he⟩`. Take `⟨c, hc, rfl⟩` from `orbit_of_prMap_eq (unitBlocks_subset hzu) (unitBlocks_subset hzu') he.symm`. Conclude with `hne ((GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hO _ hzp'.1).unique (ptOver_smul hzp c hc) hzp')`.
-/
theorem disjoint_image {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ) {σ τ : F →+* ℂ} (hne : σ ≠ τ) :
    Disjoint (prMap '' overSet y φ σ) (prMap '' overSet y φ τ) := by
  rw [Set.disjoint_left]
  rintro w ⟨z, ⟨hzu, hzp⟩, rfl⟩ ⟨z', ⟨hzu', hzp'⟩, he⟩
  obtain ⟨c, hc, rfl⟩ := orbit_of_prMap_eq (unitBlocks_subset hzu) (unitBlocks_subset hzu') he.symm
  exact hne ((GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hO _ hzp'.1).unique (ptOver_smul hzp c hc) hzp')

/- English proof (translation)
Take `⟨U, hU, hsU, hUt⟩` from `normal_exists_closure_subset hs ht.isOpen_compl hd.subset_compl_right`. Take `⟨W, hW, htW, hWU⟩` from `normal_exists_closure_subset ht (isClosed_closure (s := U)).isOpen_compl (fun x hx hxU => hUt hxU hx)`. Take `⟨g1, hg1s, hg1, hg1r⟩` from `(isClosed_closure (s := W)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)`. Take `⟨g2, hg2s, hg2, hg2r⟩` from `(isClosed_closure (s := U)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)`. Establish `hnn1 : ∀ x, 0 ≤ g1 x` using `fun x => (hg1r ⟨x, rfl⟩).1`.

Establish `hnn2 : ∀ x, 0 ≤ g2 x` using `fun x => (hg2r ⟨x, rfl⟩).1`. Establish `hpos : ∀ x, g1 x + g2 x ≠ 0`. Introduce `x`. Distinguish the cases in `hx : x ∈ closure U`. Establish `h1 : x ∈ Function.support g1`.

Rewrite using `[hg1s]`. Conclude with `fun hxW => hWU hxW hx`. Conclude with `(add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hnn1 x) (Ne.symm h1)) (hnn2 x)).ne'`. Establish `h2 : x ∈ Function.support g2`. Rewrite using `[hg2s]`.

Conclude with `hx`. Conclude with `(add_pos_of_nonneg_of_pos (hnn1 x) (lt_of_le_of_ne (hnn2 x) (Ne.symm h2))).ne'`. Use `⟨fun x => g1 x / (g1 x + g2 x), hg1.div (hg1.add hg2) hpos, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhdsSet.mpr hsU] with x hx`. Establish `h2 : g2 x = 0`.

Assume the negation of the conclusion as `h`. Establish `h' : x ∈ Function.support g2` using `h`. Rewrite `h'` using `[hg2s]`. Conclude with `h' (subset_closure hx)`. Establish `h1 : x ∈ Function.support g1`.

Rewrite using `[hg1s]`. Conclude with `fun hxW => hWU hxW (subset_closure hx)`. Rewrite using `[h2, add_zero, div_self h1]`. Use `filter_upwards [hW.mem_nhdsSet.mpr htW] with x hx`. Establish `h1 : g1 x = 0`.

Assume the negation of the conclusion as `h`. Establish `h' : x ∈ Function.support g1` using `h`. Rewrite `h'` using `[hg1s]`. Conclude with `h' (subset_closure hx)`. Rewrite using `[h1, zero_div]`.
-/
private theorem exists_smooth_sep_lemma {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧
      ∀ᶠ x in 𝓝ˢ t, f x = 0 := by
  obtain ⟨U, hU, hsU, hUt⟩ := normal_exists_closure_subset hs ht.isOpen_compl hd.subset_compl_right
  obtain ⟨W, hW, htW, hWU⟩ := normal_exists_closure_subset ht (isClosed_closure (s := U)).isOpen_compl
    (fun x hx hxU => hUt hxU hx)
  obtain ⟨g1, hg1s, hg1, hg1r⟩ := (isClosed_closure (s := W)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g2, hg2s, hg2, hg2r⟩ := (isClosed_closure (s := U)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hnn1 : ∀ x, 0 ≤ g1 x := fun x => (hg1r ⟨x, rfl⟩).1
  have hnn2 : ∀ x, 0 ≤ g2 x := fun x => (hg2r ⟨x, rfl⟩).1
  have hpos : ∀ x, g1 x + g2 x ≠ 0 := by
    intro x
    by_cases hx : x ∈ closure U
    · have h1 : x ∈ Function.support g1 := by
        rw [hg1s]
        exact fun hxW => hWU hxW hx
      exact (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hnn1 x) (Ne.symm h1)) (hnn2 x)).ne'
    · have h2 : x ∈ Function.support g2 := by
        rw [hg2s]
        exact hx
      exact (add_pos_of_nonneg_of_pos (hnn1 x) (lt_of_le_of_ne (hnn2 x) (Ne.symm h2))).ne'
  refine ⟨fun x => g1 x / (g1 x + g2 x), hg1.div (hg1.add hg2) hpos, ?_, ?_⟩
  · filter_upwards [hU.mem_nhdsSet.mpr hsU] with x hx
    have h2 : g2 x = 0 := by
      by_contra h
      have h' : x ∈ Function.support g2 := h
      rw [hg2s] at h'
      exact h' (subset_closure hx)
    have h1 : x ∈ Function.support g1 := by
      rw [hg1s]
      exact fun hxW => hWU hxW (subset_closure hx)
    rw [h2, add_zero, div_self h1]
  · filter_upwards [hW.mem_nhdsSet.mpr htW] with x hx
    have h1 : g1 x = 0 := by
      by_contra h
      have h' : x ∈ Function.support g1 := h
      rw [hg1s] at h'
      exact h' (subset_closure hx)
    rw [h1, zero_div]

/- English proof (translation)
Use `Fintype.ofFinite A` as an intermediate fact. Set `T : A → Set E` to `fun a => ⋃ b ∈ {b | b ≠ a}, S b`. Establish `hT : ∀ a, IsClosed (T a)` using `fun a => (Set.toFinite {b | b ≠ a}).isClosed_biUnion fun b _ => hS b`. Establish `hdis : ∀ a, Disjoint (S a) (T a)`. Introduce `a`.

Rewrite using `[Set.disjoint_left]`. Introduce `x hxa hx`. Take `⟨b, hb, hxb⟩` from `Set.mem_iUnion₂.mp hx`. Conclude with `Set.disjoint_left.mp (hd b a hb) hxb hxa`. Use `choose f hf hf1 hf0 using fun a => exists_smooth_sep_lemma (hS a) (hT a) (hdis a)`.

Use `⟨fun x => ∑ b, t b * f b x, ?_, fun a => ?_⟩` and prove the remaining obligations. Conclude with `ContDiff.sum fun b _ => contDiff_const.mul (hf b)`. Establish `h : ∀ᶠ x in 𝓝ˢ (S a), ∀ b, f b x = if b = a then 1 else 0`. Rewrite using `[Filter.eventually_all]`. Introduce `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `using hf1 b`. Establish `hsub : S a ⊆ T b` using `fun x hx => Set.mem_iUnion₂.mpr ⟨a, Ne.symm hb, hx⟩`. Simplify `(hf0 b).filter_mono (nhdsSet_mono hsub)` using `[hb]`.

Use `filter_upwards [h] with x hx`. Simplify using `[hx]`.
-/
theorem exists_smooth_sep {A E : Type} [Finite A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (S : A → Set E) (hS : ∀ a, IsClosed (S a))
    (hd : ∀ a b, a ≠ b → Disjoint (S a) (S b)) (t : A → ℝ) :
    ∃ v : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v ∧ ∀ a, ∀ᶠ x in 𝓝ˢ (S a), v x = t a := by
  classical
  have := Fintype.ofFinite A
  let T : A → Set E := fun a => ⋃ b ∈ {b | b ≠ a}, S b
  have hT : ∀ a, IsClosed (T a) := fun a =>
    (Set.toFinite {b | b ≠ a}).isClosed_biUnion fun b _ => hS b
  have hdis : ∀ a, Disjoint (S a) (T a) := by
    intro a
    rw [Set.disjoint_left]
    intro x hxa hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    exact Set.disjoint_left.mp (hd b a hb) hxb hxa
  choose f hf hf1 hf0 using fun a => exists_smooth_sep_lemma (hS a) (hT a) (hdis a)
  refine ⟨fun x => ∑ b, t b * f b x, ?_, fun a => ?_⟩
  · exact ContDiff.sum fun b _ => contDiff_const.mul (hf b)
  · have h : ∀ᶠ x in 𝓝ˢ (S a), ∀ b, f b x = if b = a then 1 else 0 := by
      rw [Filter.eventually_all]
      intro b
      by_cases hb : b = a
      · subst hb
        simpa using hf1 b
      · have hsub : S a ⊆ T b := fun x hx => Set.mem_iUnion₂.mpr ⟨a, Ne.symm hb, hx⟩
        simpa [hb] using (hf0 b).filter_mono (nhdsSet_mono hsub)
    filter_upwards [h] with x hx
    simp [hx]

/- English proof (translation)
Take `⟨v, hv, hvt⟩` from `exists_smooth_sep (fun σ : F →+* ℂ => prMap '' overSet y φ σ) (fun σ => ((isCompact_overSet y φ σ).image_of_continuousOn ((prMap_contDiffOn (K := K) (ι := ι) (n := 0)).continuousOn.mono fun z hz => unitBlocks_subset hz.1)).isClosed) (fun σ τ h => disjoint_image hO h) t`. Use `⟨fun z => v (prMap z), ⟨fun c z hc => by simp only [prMap_smul c z hc], ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `hv.comp_contDiffOn prMap_contDiffOn`. Introduce `σ z hz`. Establish `h1 : ∀ᶠ w in 𝓝 (prMap z), v w = t σ` using `(hvt σ).filter_mono (nhds_le_nhdsSet (prMap_mem_image hz))`.

Conclude with `Filter.Tendsto.eventually (prMap_continuousAt hz.1.1) h1`.
-/
theorem exists_base {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ) (t : (F →+* ℂ) → ℝ) :
    ∃ u, IsPlaceWeight y φ t u := by
  classical
  obtain ⟨v, hv, hvt⟩ := exists_smooth_sep (fun σ : F →+* ℂ => prMap '' overSet y φ σ)
    (fun σ => ((isCompact_overSet y φ σ).image_of_continuousOn
      ((prMap_contDiffOn (K := K) (ι := ι) (n := 0)).continuousOn.mono
        fun z hz => unitBlocks_subset hz.1)).isClosed)
    (fun σ τ h => disjoint_image hO h) t
  refine ⟨fun z => v (prMap z), ⟨fun c z hc => by simp only [prMap_smul c z hc], ?_, ?_⟩⟩
  · exact hv.comp_contDiffOn prMap_contDiffOn
  · intro σ z hz
    have h1 : ∀ᶠ w in 𝓝 (prMap z), v w = t σ :=
      (hvt σ).filter_mono (nhds_le_nhdsSet (prMap_mem_image hz))
    exact Filter.Tendsto.eventually (prMap_continuousAt hz.1.1) h1

def cj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => (starRingEnd ℂ) (z p)

/- English proof (translation)
Rewrite using `[contDiff_pi]`. Introduce `p`. Use `show ContDiff ℝ n fun z : (Σ k, ι k) → ℂ => (starRingEnd ℂ) (z p)`. Establish `h0` using `Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ (n := n) p)`. Simplify `h0` using `[Function.comp_def]`.
-/
theorem cj_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n (cj (K := K) (ι := ι)) := by
  rw [contDiff_pi]
  intro p
  show ContDiff ℝ n fun z : (Σ k, ι k) → ℂ => (starRingEnd ℂ) (z p)
  have h0 := Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ (n := n) p)
  simpa [Function.comp_def] using h0

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `[cj]`.
-/
theorem cj_cj (z : (Σ k, ι k) → ℂ) : cj (cj z) = z := by
  funext p
  simp [cj]

/- English proof (translation)
Establish `hconj : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), cj (fun p => c p.1 * z p) = fun p => (starRingEnd ℂ) (c p.1) * cj z p`. Introduce `c z`. Use function extensionality and compare the values at `p`. Simplify using `[cj]`. Use `⟨fun c z hc => ?_, ?_, fun σ z hz => ?_⟩` and prove the remaining obligations.

Rewrite using `[hu.inv c z hc, hconj, hu.inv _ _ fun k => (map_ne_zero _).mpr (hc k)]`. Establish `hmaps : Set.MapsTo (cj (K` using `K) (ι := ι)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by`. Introduce `z hz k`. Take `⟨i, hi⟩` from `hz k`. Conclude with `⟨i, by simpa [cj] using hi⟩`.

Conclude with `(hu.smooth.add (hu.smooth.comp cj_contDiff.contDiffOn hmaps)).div_const 2`. Establish `h1` using `hu.near σ z hz`. Establish `h3` using `hu.near (ComplexEmbedding.conjugate σ) (cj z) (GlobalTheory.T.complex_point_conjugate K ι Ω F y φ σ z hz)`. Rewrite `h3` using `[ht σ]`. Establish `h2 : ∀ᶠ z' in 𝓝 z, u (cj z') = t σ` using `Filter.Tendsto.eventually ((cj_contDiff (K := K) (ι := ι) (n := 0)).continuous.continuousAt) h3`.

Use `filter_upwards [h1, h2] with z' e1 e2`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem average {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} {t : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsPlaceWeight y φ t u) (ht : ∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) :
    IsPlaceWeight y φ t (fun z => (u z + u (cj z)) / 2) := by
  have hconj : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ),
      cj (fun p => c p.1 * z p) = fun p => (starRingEnd ℂ) (c p.1) * cj z p := by
    intro c z
    funext p
    simp [cj]
  refine ⟨fun c z hc => ?_, ?_, fun σ z hz => ?_⟩
  · rw [hu.inv c z hc, hconj, hu.inv _ _ fun k => (map_ne_zero _).mpr (hc k)]
  · have hmaps : Set.MapsTo (cj (K := K) (ι := ι)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
        {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
      intro z hz k
      obtain ⟨i, hi⟩ := hz k
      exact ⟨i, by simpa [cj] using hi⟩
    exact (hu.smooth.add (hu.smooth.comp cj_contDiff.contDiffOn hmaps)).div_const 2
  · have h1 := hu.near σ z hz
    have h3 := hu.near (ComplexEmbedding.conjugate σ) (cj z) (GlobalTheory.T.complex_point_conjugate K ι Ω F y φ σ z hz)
    rw [ht σ] at h3
    have h2 : ∀ᶠ z' in 𝓝 z, u (cj z') = t σ :=
      Filter.Tendsto.eventually ((cj_contDiff (K := K) (ι := ι) (n := 0)).continuous.continuousAt) h3
    filter_upwards [h1, h2] with z' e1 e2
    rw [e1, e2]
    ring

end PlaceWeightSmooth

open PlaceWeightSmooth in

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_base hO t`. Distinguish the cases in `ht : ∀ σ, t (ComplexEmbedding.conjugate σ) = t σ`. Use `⟨_, average hu ht, fun _ z => ?_⟩ show (u (cj z) + u (cj (cj z))) / 2 = (u z + u (cj z)) / 2` and prove the remaining obligations. Rewrite using `[cj_cj, add_comm]`. Conclude with `⟨u, hu, fun h => absurd h ht⟩`.
-/
theorem exists_placeWeight (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (t : (F →+* ℂ) → ℝ)
    (hO : OverInt y φ) :
    ∃ u, IsPlaceWeight y φ t u ∧ ((∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∀ z : (Σ k, ι k) → ℂ, u (fun p => (starRingEnd ℂ) (z p)) = u z) := by
  obtain ⟨u, hu⟩ := exists_base hO t
  by_cases ht : ∀ σ, t (ComplexEmbedding.conjugate σ) = t σ
  · refine ⟨_, average hu ht, fun _ z => ?_⟩
    show (u (cj z) + u (cj (cj z))) / 2 = (u z + u (cj z)) / 2
    rw [cj_cj, add_comm]
  · exact ⟨u, hu, fun h => absurd h ht⟩

end GlobalTheory.CompanionTheory.Ar.Flat
