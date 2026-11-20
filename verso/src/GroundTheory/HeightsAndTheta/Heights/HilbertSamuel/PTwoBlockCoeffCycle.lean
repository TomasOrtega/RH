import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCoeffCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockHorizDiv
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricTransportSmooth
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace TwoBlockCoeffCycle

variable {κ : Type} [Fintype κ]

/- English proof (translation)
Establish `hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, FinTwoTypeFamily κ k) → ℂ => fun p : Ix κ => z ⟨b, p.2⟩)` using `contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (⟨b, p.2⟩ : Σ k, FinTwoTypeFamily κ k)`. Conclude with `hm.comp hL.contDiffOn fun z hz h0 => by`. Take `⟨i, hi⟩` from `hz b`. Conclude with `hi (congrFun h0 ⟨(), i⟩)`.
-/
theorem isSmoothHerm_blockLine {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) (b : Fin 2) :
    IsSmoothHerm (blockLine m b) := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, FinTwoTypeFamily κ k) → ℂ => fun p : Ix κ => z ⟨b, p.2⟩) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (⟨b, p.2⟩ : Σ k, FinTwoTypeFamily κ k)
  exact hm.comp hL.contDiffOn fun z hz h0 => by
    obtain ⟨i, hi⟩ := hz b
    exact hi (congrFun h0 ⟨(), i⟩)

/- English proof (translation)
Introduce `mo hmo k`. Rewrite `hmo` using `[support_X, Finset.mem_singleton]`. Substitute `hmo` using the available equality. Distinguish the cases in `hk : k = b`. Substitute `hk` using the available equality.

Simplify using `[Finsupp.single_apply]`. Simplify using `[hk]`.
-/
theorem isMultiHomog_X_blk (b : Fin 2) (i : κ) :
    IsMultiHomog (X ⟨b, i⟩ : MRing (FinTwoTypeFamily κ)) (Pi.single b 1) := by
  classical
  intro mo hmo k
  rw [support_X, Finset.mem_singleton] at hmo
  subst hmo
  by_cases hk : k = b
  · subst hk
    simp [Finsupp.single_apply]
  · simp [hk]

/- English proof (translation)
Introduce `mo hmo k`. Unfold `twoBlockNum at hmo`. Take `⟨j, -, hj⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)`. Rewrite `hj` using `[C_mul']`. Conclude with `isMultiHomog_X_blk 1 j.2 mo (MvPolynomial.support_smul hj) k`.
-/
theorem isMultiHomog_twoBlockNum (l : Ix κ → ℤ) : IsMultiHomog (twoBlockNum l) (Pi.single 1 1) := by
  classical
  intro mo hmo k
  unfold twoBlockNum at hmo
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
  rw [C_mul'] at hj
  exact isMultiHomog_X_blk 1 j.2 mo (MvPolynomial.support_smul hj) k

variable {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Simplify using `only [mConeMap, map_sum, map_mul, aeval_X, eq_intCast, map_intCast]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_lin (x x' : Ix κ → Ω) (b : Fin 2) (a : Ix κ → ℤ) :
    mConeMap (pair x x') (∑ k : Ix κ, C (a k) * X (⟨b, k.2⟩ : Σ k, FinTwoTypeFamily κ k)) =
      C (∑ k, (a k : Ω) * pair x x' ⟨b, k.2⟩) * X b := by
  simp only [mConeMap, map_sum, map_mul, aeval_X, eq_intCast, map_intCast]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Simplify using `[mConeMap]`.
-/
theorem mConeMap_X (x x' : Ix κ → Ω) (p : Σ k, FinTwoTypeFamily κ k) :
    mConeMap (pair x x') (X p) = C (pair x x' p) * X p.1 := by
  simp [mConeMap]

/- English proof (translation)
Simplify using `[pair]`.
-/
theorem pair_one (x x' : Ix κ → Ω) (k : Ix κ) : pair x x' ⟨1, k.2⟩ = x' k := by
  simp [pair]

/- English proof (translation)
Introduce `h`. Establish `h' : mConeMap (pair x x') (twoBlockNum l) = 0` using `h`. Rewrite `h'` using `[twoBlockNum, mConeMap_lin]`. Simplify using `only [pair_one, ← hl] at h'`. Simplify using `[hc, X_ne_zero] at h'`.
-/
theorem twoBlockNum_not_mem {x x' : Ix κ → Ω} {c : κ} {l : Ix κ → ℤ}
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j) (hc : x ⟨(), c⟩ ≠ 0) : twoBlockNum l ∉ twoBlockIdeal x x' := by
  intro h
  have h' : mConeMap (pair x x') (twoBlockNum l) = 0 := h
  rw [twoBlockNum, mConeMap_lin] at h'
  simp only [pair_one, ← hl] at h'
  simp [hc, X_ne_zero] at h'

/- English proof (translation)
Introduce `h`. Establish `h' : mConeMap (pair x x') (twoBlockDen c) = 0` using `h`. Rewrite `h'` using `[twoBlockDen, mConeMap_X]`. Simplify using `[pair, hc, X_ne_zero] at h'`.
-/
theorem twoBlockDen_not_mem {x x' : Ix κ → Ω} {c : κ} (hc : x ⟨(), c⟩ ≠ 0) : twoBlockDen c ∉ twoBlockIdeal x x' := by
  intro h
  have h' : mConeMap (pair x x') (twoBlockDen c) = 0 := h
  rw [twoBlockDen, mConeMap_X] at h'
  simp [pair, hc, X_ne_zero] at h'

/- English proof (translation)
Simplify using `[pair]`.
-/
theorem pair_zero' (x x' : Ix κ → Ω) (c : κ) : pair x x' ⟨0, c⟩ = x ⟨(), c⟩ := by
  simp [pair]

/- English proof (translation)
Use `show mConeMap (pair x x') _ = 0`. Rewrite using `[map_sub, map_mul, map_mul, map_mul, map_intCast, mConeMap_X, mConeMap_X, twoBlockNum, mConeMap_lin, mConeMap_lin]`. Simplify using `only [pair_one, pair_zero', ← hl, hN, map_mul, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_mem {x x' : Ix κ → Ω} {c : κ} {l : Ix κ → ℤ} (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j)
    (d : ℤ) (N : Ix κ → ℤ) (j : Ix κ) (hN : ∑ k, (N k : Ω) * x k = (d : Ω) * x' j) :
    (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j.2⟩ - twoBlockNum l * ∑ k : Ix κ, C (N k) * X ⟨0, k.2⟩ ∈
      twoBlockIdeal x x' := by
  show mConeMap (pair x x') _ = 0
  rw [map_sub, map_mul, map_mul, map_mul, map_intCast, mConeMap_X, mConeMap_X, twoBlockNum, mConeMap_lin,
    mConeMap_lin]
  simp only [pair_one, pair_zero', ← hl, hN, map_mul, map_intCast]
  ring

/- English proof (translation)
Take `⟨d, hd, hN⟩` from `ChangeOfLattice.exists_clear_den B`. Use `choose N hN using hN`. Use `set u : Ix κ → ℂ := fun p => z ⟨0, p.2⟩ with hu`. Use `set w : Ix κ → ℂ := fun p => z ⟨1, p.2⟩ with hw`. Use `set L : ℂ := ∑ i, (l i : ℂ) * w i with hL`.

Establish `hNΩ : ∀ j, ∑ k, ((N j k : ℤ) : Ω) * x k = ((d : ℤ) : Ω) * matAct B x j` using `fun j => by`. Simplify using `only [matAct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun q : ℚ => (q : Ω)) (hN j k)`. Move the coercions through the operations in `at h`.

Rewrite using `[← h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hNC : ∀ j, ∑ k, ((N j k : ℤ) : ℂ) * u k = (d : ℂ) * matActC B u j` using `fun j => by`. Simplify using `only [matActC, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun q : ℚ => (q : ℂ)) (hN j k)`. Move the coercions through the operations in `at h`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ j, z ⟨0, c⟩ * w j = L * matActC B u j` using `fun j => by`. Establish `h0` using `hz.2 _ (rel_mem hl (d : ℤ) (N j) j (hNΩ j))`. Establish `h0' : (d : ℂ) * z ⟨0, c⟩ * w j - L * ∑ k, ((N j k : ℤ) : ℂ) * u k = 0`. Simplify `h0` using `[twoBlockNum, hL, hw, hu, map_sum]`. Rewrite `h0'` using `[hNC j]`.

Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd`. Apply `mul_left_cancel₀ hd'` to reduce the goal to its premises. Take the linear combination `h0'`. Establish `hvec : z ⟨0, c⟩ • w = L • matActC B u` using `funext fun j => by simpa using key j`. Establish `hnorm : ‖z ⟨0, c⟩‖ * m'.ρ w = ‖L‖ * m.ρ u`.

Rewrite using `[← m'.smul, hvec, m'.smul, hm']`. Establish `hu0 : u ≠ 0` using `fun h0 => by`. Take `⟨i, hi⟩` from `hz.1 0`. Conclude with `hi (congrFun h0 ⟨(), i⟩)`. Establish `hw0 : w ≠ 0` using `fun h0 => by`.

Take `⟨i, hi⟩` from `hz.1 1`. Conclude with `hi (congrFun h0 ⟨(), i⟩)`. Establish `hmu` using `m.pos u hu0`. Establish `hmw` using `m'.pos w hw0`. Establish `hnum : eval z (map (Int.castRingHom ℂ) (twoBlockNum l)) = L`.

Simplify using `[twoBlockNum, hL, hw, map_sum]`. Establish `hden : eval z (map (Int.castRingHom ℂ) (twoBlockDen c)) = z ⟨0, c⟩`. Simplify using `[twoBlockDen]`. Use `show Real.log (‖eval z (map (Int.castRingHom ℂ) (twoBlockNum l))‖ / m'.ρ w) = Real.log (‖eval z (map (Int.castRingHom ℂ) (twoBlockDen c))‖ / m.ρ u)`. Rewrite using `[hnum, hden]`.

Distinguish the cases in `hc0 : z ⟨0, c⟩ = 0`. Take `⟨B', -, hB'B⟩` from `isInvMat_mul hB`. Establish `hBu : matActC B u ≠ 0` using `fun h0 => by`. Apply `hu0` to reduce the goal to its premises. Establish `h` using `congrArg (matActC B') h0`.

Rewrite `h` using `[ChangeOfLattice.matActC_mul, hB'B, MetricTransportSmooth.matActC_one, MetricTransportSmooth.matActC_zero]`. Then use the resulting hypothesis. Establish `hL0 : L = 0`. Establish `h : L • matActC B u = 0` using `by rw [← hvec, hc0, zero_smul]`. Conclude with `(smul_eq_zero.mp h).resolve_right hBu`. Simplify using `[hc0, hL0]`.

Use `congr 1`. Rewrite using `[div_eq_div_iff hmw.ne' hmu.ne']`. Combine the linear relations using `[hnorm]`.
-/
theorem logNorm_eq {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {m m' : ConeMetric ℂ (Ix κ)} {c : κ}
    {l : Ix κ → ℤ} (hB : IsInvMat B) (hm' : ∀ z, m'.ρ (matActC B z) = m.ρ z)
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) {z : (Σ k, FinTwoTypeFamily κ k) → ℂ}
    (hz : z ∈ mcPts (twoBlockIdeal x (matAct B x))) :
    logNorm (blockLine m' 1) (twoBlockNum l) z = logNorm (blockLine m 0) (twoBlockDen c) z := by
  classical
  obtain ⟨d, hd, hN⟩ := ChangeOfLattice.exists_clear_den B
  choose N hN using hN
  set u : Ix κ → ℂ := fun p => z ⟨0, p.2⟩ with hu
  set w : Ix κ → ℂ := fun p => z ⟨1, p.2⟩ with hw
  set L : ℂ := ∑ i, (l i : ℂ) * w i with hL
  have hNΩ : ∀ j, ∑ k, ((N j k : ℤ) : Ω) * x k = ((d : ℤ) : Ω) * matAct B x j := fun j => by
    simp only [matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := congrArg (fun q : ℚ => (q : Ω)) (hN j k)
    push_cast at h
    rw [← h]
    push_cast
    ring
  have hNC : ∀ j, ∑ k, ((N j k : ℤ) : ℂ) * u k = (d : ℂ) * matActC B u j := fun j => by
    simp only [matActC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := congrArg (fun q : ℚ => (q : ℂ)) (hN j k)
    push_cast at h
    rw [← h]
    ring
  have key : ∀ j, z ⟨0, c⟩ * w j = L * matActC B u j := fun j => by
    have h0 := hz.2 _ (rel_mem hl (d : ℤ) (N j) j (hNΩ j))
    have h0' : (d : ℂ) * z ⟨0, c⟩ * w j - L * ∑ k, ((N j k : ℤ) : ℂ) * u k = 0 := by
      simpa [twoBlockNum, hL, hw, hu, map_sum] using h0
    rw [hNC j] at h0'
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    apply mul_left_cancel₀ hd'
    linear_combination h0'
  have hvec : z ⟨0, c⟩ • w = L • matActC B u := funext fun j => by simpa using key j
  have hnorm : ‖z ⟨0, c⟩‖ * m'.ρ w = ‖L‖ * m.ρ u := by
    rw [← m'.smul, hvec, m'.smul, hm']
  have hu0 : u ≠ 0 := fun h0 => by
    obtain ⟨i, hi⟩ := hz.1 0
    exact hi (congrFun h0 ⟨(), i⟩)
  have hw0 : w ≠ 0 := fun h0 => by
    obtain ⟨i, hi⟩ := hz.1 1
    exact hi (congrFun h0 ⟨(), i⟩)
  have hmu := m.pos u hu0
  have hmw := m'.pos w hw0
  have hnum : eval z (map (Int.castRingHom ℂ) (twoBlockNum l)) = L := by
    simp [twoBlockNum, hL, hw, map_sum]
  have hden : eval z (map (Int.castRingHom ℂ) (twoBlockDen c)) = z ⟨0, c⟩ := by
    simp [twoBlockDen]
  show Real.log (‖eval z (map (Int.castRingHom ℂ) (twoBlockNum l))‖ / m'.ρ w) =
    Real.log (‖eval z (map (Int.castRingHom ℂ) (twoBlockDen c))‖ / m.ρ u)
  rw [hnum, hden]
  by_cases hc0 : z ⟨0, c⟩ = 0
  · obtain ⟨B', -, hB'B⟩ := isInvMat_mul hB
    have hBu : matActC B u ≠ 0 := fun h0 => by
      apply hu0
      have h := congrArg (matActC B') h0
      rwa [ChangeOfLattice.matActC_mul, hB'B, MetricTransportSmooth.matActC_one, MetricTransportSmooth.matActC_zero] at h
    have hL0 : L = 0 := by
      have h : L • matActC B u = 0 := by rw [← hvec, hc0, zero_smul]
      exact (smul_eq_zero.mp h).resolve_right hBu
    simp [hc0, hL0]
  · congr 1
    rw [div_eq_div_iff hmw.ne' hmu.ne']
    linarith [hnorm]

open Classical in

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.AI.I2.cycR ReciprocityTheory.ChartRestriction.G.AI.I2.vertR`. Rewrite using `[← finsum_mem_add_distrib (divSupp_finite P s)]`. Use `finsum_mem_congr rfl fun W _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem cycR_split {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (s : MRing ι) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.cycR I P L s =
      (∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * (if IsHorizontal W then I W n L else 0)) +
        ReciprocityTheory.ChartRestriction.G.AI.I2.vertR P L s := by
  unfold ReciprocityTheory.ChartRestriction.G.AI.I2.cycR ReciprocityTheory.ChartRestriction.G.AI.I2.vertR
  rw [← finsum_mem_add_distrib (divSupp_finite P s)]
  refine finsum_mem_congr rfl fun W _ => ?_
  split_ifs <;> ring

open Classical in

/- English proof (translation)
Rewrite using `[finsum_mem_def, finsum_mem_def]`. Use `congr 1`. Use function extensionality and compare the values at `W`. Distinguish the cases in `hW : IsHorizontal W`. Take `⟨hiff, hmul⟩` from `hH Ω κ x B c l hsp hl W hW`.

Distinguish the cases in `h1 : W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l)`. Simplify using `only [Set.indicator_apply, h1, hiff.1 h1, if_true, hmul h1]`. Establish `h2 : W ∉ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c)` using `mt hiff.2 h1`. Simplify using `only [Set.indicator_apply, h1, h2, if_false]`. Simplify using `[Set.indicator_apply, hW]`.
-/
theorem horiz_eq (hH : TwoBlockHorizDiv.Statement) {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ}
    {l : Ix κ → ℤ} (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) (f : Ideal (MRing (FinTwoTypeFamily κ)) → ℝ) :
    ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l),
        (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W : ℝ) *
          (if IsHorizontal W then f W else 0) =
      ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c),
        (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
          (if IsHorizontal W then f W else 0) := by
  rw [finsum_mem_def, finsum_mem_def]
  congr 1
  funext W
  by_cases hW : IsHorizontal W
  · obtain ⟨hiff, hmul⟩ := hH Ω κ x B c l hsp hl W hW
    by_cases h1 : W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l)
    · simp only [Set.indicator_apply, h1, hiff.1 h1, if_true, hmul h1]
    · have h2 : W ∉ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) := mt hiff.2 h1
      simp only [Set.indicator_apply, h1, h2, if_false]
  · simp [Set.indicator_apply, hW]

end TwoBlockCoeffCycle

open TwoBlockCoeffCycle in

/- English proof (translation)
Introduce `D Ω _ _ κ _ I x B m m' c l hI hx hxi hB hm hm' hsp hl i hi`. Take `⟨hFp, -⟩` from `hF Ω κ x B hB`. Establish `hxA : IsArithVar (mCoordIdeal (ι` using `GlobalTheory κ) x) (D + 1) := by`. Rewrite using `[← coordIdeal_eq_mCoordIdeal]`. Conclude with `hx`.

Establish `hx0 : x ≠ 0` using `fun h => hxi.ne_zero ⟨(), c⟩ (by rw [h]; rfl)`. Take `⟨B', -, hB'⟩` from `isInvMat_mul hB`. Establish `hBx0 : matAct B x ≠ 0` using `fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)`. Take `⟨⟨⟨⟩, i₀⟩, hi₀⟩` from `Function.ne_iff.mp hx0`. Take `⟨⟨⟨⟩, i₁⟩, hi₁⟩` from `Function.ne_iff.mp hBx0`.

Establish `hP : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1)` using `hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩ (fun k => by fin_cases k`. Conclude with `⟨i₀, by simpa [pair] using hi₀⟩`. Conclude with `⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA`. Establish `hms' : IsSmoothMetric m'` using `MetricTransportSmooth.proof κ B m m' hB hm hm'`. Establish `hxc : x ⟨(), c⟩ ≠ 0` using `hxi.ne_zero _`.

Use `set ii : Fin (D + 1) := ⟨i, Nat.lt_succ_of_le hi⟩ with hii`. Use `set L' : Fin D → HermLine (FinTwoTypeFamily κ) := fun j => twoBlockList m m' D i (ii.succAbove j) with hL'`. Use `set τ : Equiv.Perm (Fin (D + 1)) := (finSuccEquiv' (Fin.last D)).trans (finSuccEquiv' ii).symm with hτ`. Establish `hτ_last : τ (Fin.last D) = ii`. Simplify using `[hτ, finSuccEquiv'_at]`.

Establish `hτ_cs : ∀ j : Fin D, τ j.castSucc = ii.succAbove j` using `fun j => by`. Simplify using `[hτ, finSuccEquiv'_below (Fin.castSucc_lt_last j)]`. Establish `hl1 : twoBlockList m m' D i ∘ τ = Fin.snoc L' (blockLine m' 1)`. Use function extensionality and compare the values at `k`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last => simp [hτ_last, twoBlockList, hii]`. Consider the case `cast j => simp [hτ_cs, hL']`. Establish `hl0 : twoBlockList m m' D (i + 1) ∘ τ = Fin.snoc L' (blockLine m 0)`. Use function extensionality and compare the values at `k`. Proceed by induction on `k using Fin.lastCases with`.

Consider the case `last => simp [hτ_last, twoBlockList, hii]`. Consider the case `cast j`. Simplify using `only [Function.comp_apply, hτ_cs, Fin.snoc_castSucc, hL', twoBlockList]`. Unfold `Fin.succAbove`. Apply the tactic sequence `split_ifs <;> simp_all [Fin.lt_def] <;> omega`.

Establish `hsm : ∀ i' j, IsSmoothHerm (twoBlockList m m' D i' j)` using `fun i' j => by`. Unfold `twoBlockList`. Use `split_ifs`. Conclude with `isSmoothHerm_blockLine hm 0`. Conclude with `isSmoothHerm_blockLine hms' 1`.

Establish `hL's : ∀ j, IsSmoothHerm (L' j)` using `fun j => hsm i _`. Establish `hfam` using `hI (Fin 2) (FinTwoTypeFamily κ)`. Establish `e1 : I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (twoBlockList m m' D i) = recR (I (Fin 2) (FinTwoTypeFamily κ)) (twoBlockIdeal x (matAct B x)) L' (blockLine m' 1) (twoBlockNum l)`. Rewrite using `[← hfam.1 _ _ _ τ hP (hsm i), hl1]`. Apply the tactic sequence `exact hfam.2.2 _ D L' _ _ (Pi.single 1 1) hP hL's (isSmoothHerm_blockLine hms' 1) (fun k => by fin_cases k <;> simp [blockLine]) (isMultiHomog_twoBlockNum l) (twoBlockNum_not_mem hl hxc)`.

Establish `e0 : I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (twoBlockList m m' D (i + 1)) = recR (I (Fin 2) (FinTwoTypeFamily κ)) (twoBlockIdeal x (matAct B x)) L' (blockLine m 0) (twoBlockDen c)`. Rewrite using `[← hfam.1 _ _ _ τ hP (hsm (i + 1)), hl0]`. Apply the tactic sequence `exact hfam.2.2 _ D L' _ _ (Pi.single 0 1) hP hL's (isSmoothHerm_blockLine hm 0) (fun k => by fin_cases k <;> simp [blockLine]) (isMultiHomog_X_blk 0 c) (twoBlockDen_not_mem hxc)`. Establish `hdeg : (fun j => (L' j).a) = twoBlockDegList D i`. Use function extensionality and compare the values at `j`.

Rewrite using `[twoBlockDegList_eq m m' D i j, hL']`. Use `congr 2`. Establish `hint : arInt (twoBlockIdeal x (matAct B x)) (twoBlockNum l) (blockLine m' 1) L' = arInt (twoBlockIdeal x (matAct B x)) (twoBlockDen c) (blockLine m 0) L'` using `GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) fun z hz => logNorm_eq hB hm' hl hz`. Establish `hhor` using `horiz_eq hH hsp hl (fun W => I (Fin 2) (FinTwoTypeFamily κ) W D L')`. Unfold `twoBlockCoeff twoBlockVert`.

Rewrite using `[e1, e0, ReciprocityTheory.ChartRestriction.G.AI.I2.recR_eq, ReciprocityTheory.ChartRestriction.G.AI.I2.recR_eq, cycR_split, cycR_split, hint, hhor, vertR_eq_vertCycleNum, vertR_eq_vertCycleNum, hdeg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem TwoBlockCoeffCycle.proof (hA : CoordArithOfFnField.Statement) (hF : TwoBlockFnField.Statement)
    (hH : TwoBlockHorizDiv.Statement) : TwoBlockCoeffCycle.Statement := by
  classical
  intro D Ω _ _ κ _ I x B m m' c l hI hx hxi hB hm hm' hsp hl i hi

  obtain ⟨hFp, -⟩ := hF Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hx
  have hx0 : x ≠ 0 := fun h => hxi.ne_zero ⟨(), c⟩ (by rw [h]; rfl)
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hP : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    hA Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hms' : IsSmoothMetric m' := MetricTransportSmooth.proof κ B m m' hB hm hm'
  have hxc : x ⟨(), c⟩ ≠ 0 := hxi.ne_zero _

  set ii : Fin (D + 1) := ⟨i, Nat.lt_succ_of_le hi⟩ with hii
  set L' : Fin D → HermLine (FinTwoTypeFamily κ) := fun j => twoBlockList m m' D i (ii.succAbove j) with hL'
  set τ : Equiv.Perm (Fin (D + 1)) := (finSuccEquiv' (Fin.last D)).trans (finSuccEquiv' ii).symm with hτ
  have hτ_last : τ (Fin.last D) = ii := by
    simp [hτ, finSuccEquiv'_at]
  have hτ_cs : ∀ j : Fin D, τ j.castSucc = ii.succAbove j := fun j => by
    simp [hτ, finSuccEquiv'_below (Fin.castSucc_lt_last j)]
  have hl1 : twoBlockList m m' D i ∘ τ = Fin.snoc L' (blockLine m' 1) := by
    funext k
    induction k using Fin.lastCases with
    | last => simp [hτ_last, twoBlockList, hii]
    | cast j => simp [hτ_cs, hL']
  have hl0 : twoBlockList m m' D (i + 1) ∘ τ = Fin.snoc L' (blockLine m 0) := by
    funext k
    induction k using Fin.lastCases with
    | last => simp [hτ_last, twoBlockList, hii]
    | cast j =>
      simp only [Function.comp_apply, hτ_cs, Fin.snoc_castSucc, hL', twoBlockList]
      unfold Fin.succAbove
      split_ifs <;> simp_all [Fin.lt_def] <;> omega
  have hsm : ∀ i' j, IsSmoothHerm (twoBlockList m m' D i' j) := fun i' j => by
    unfold twoBlockList
    split_ifs
    · exact isSmoothHerm_blockLine hm 0
    · exact isSmoothHerm_blockLine hms' 1
  have hL's : ∀ j, IsSmoothHerm (L' j) := fun j => hsm i _
  have hfam := hI (Fin 2) (FinTwoTypeFamily κ)

  have e1 : I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (twoBlockList m m' D i) =
      recR (I (Fin 2) (FinTwoTypeFamily κ)) (twoBlockIdeal x (matAct B x)) L' (blockLine m' 1) (twoBlockNum l) := by
    rw [← hfam.1 _ _ _ τ hP (hsm i), hl1]
    exact hfam.2.2 _ D L' _ _ (Pi.single 1 1) hP hL's (isSmoothHerm_blockLine hms' 1)
      (fun k => by fin_cases k <;> simp [blockLine]) (isMultiHomog_twoBlockNum l) (twoBlockNum_not_mem hl hxc)
  have e0 : I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (twoBlockList m m' D (i + 1)) =
      recR (I (Fin 2) (FinTwoTypeFamily κ)) (twoBlockIdeal x (matAct B x)) L' (blockLine m 0) (twoBlockDen c) := by
    rw [← hfam.1 _ _ _ τ hP (hsm (i + 1)), hl0]
    exact hfam.2.2 _ D L' _ _ (Pi.single 0 1) hP hL's (isSmoothHerm_blockLine hm 0)
      (fun k => by fin_cases k <;> simp [blockLine]) (isMultiHomog_X_blk 0 c) (twoBlockDen_not_mem hxc)
  have hdeg : (fun j => (L' j).a) = twoBlockDegList D i := by
    funext j
    rw [twoBlockDegList_eq m m' D i j, hL']
    congr 2

  have hint : arInt (twoBlockIdeal x (matAct B x)) (twoBlockNum l) (blockLine m' 1) L' =
      arInt (twoBlockIdeal x (matAct B x)) (twoBlockDen c) (blockLine m 0) L' :=
    GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl)
      fun z hz => logNorm_eq hB hm' hl hz
  have hhor := horiz_eq hH hsp hl (fun W => I (Fin 2) (FinTwoTypeFamily κ) W D L')
  unfold twoBlockCoeff twoBlockVert
  rw [e1, e0, ReciprocityTheory.ChartRestriction.G.AI.I2.recR_eq, ReciprocityTheory.ChartRestriction.G.AI.I2.recR_eq, cycR_split, cycR_split, hint, hhor,
    vertR_eq_vertCycleNum, vertR_eq_vertCycleNum, hdeg]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
