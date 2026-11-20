import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SectionInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace MultiProjectiveCoordinates

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using Algebra.subset_adjoin hx⟩`. Consider the case `algebraMap r`. Use `⟨r.den, r.den_pos, ?_⟩` and prove the remaining obligations. Establish `: (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω)`.

Establish `h : ((r.den : ℚ) * r) = (r.num : ℚ)` using `Rat.den_mul_eq_num r`. Use `congrArg (algebraMap ℚ Ω) h` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_intCast]`. Then use the resulting hypothesis. Rewrite using `[this]`. Conclude with `intCast_mem _ _`.

Consider the case `add x y _ _ hx hy`. Take `⟨N, hN, hx⟩` from `hx`. Take `⟨M, hM, hy⟩` from `hy`. Use `⟨N * M, mul_pos hN hM, ?_⟩` and prove the remaining obligations. Establish `: ((N * M : ℕ) : Ω) * (x + y) = (M : Ω) * (N * x) + (N : Ω) * (M * y)` using `by push_cast; ring`.

Rewrite using `[this]`. Conclude with `add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)`. Consider the case `mul x y _ _ hx hy`. Take `⟨N, hN, hx⟩` from `hx`. Take `⟨M, hM, hy⟩` from `hy`.

Use `⟨N * M, mul_pos hN hM, ?_⟩` and prove the remaining obligations. Establish `: ((N * M : ℕ) : Ω) * (x * y) = (N * x) * (M * y)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `mul_mem hx hy`.
-/
theorem adjoin_rat_clear {Ω : Type} [Field Ω] [CharZero Ω] (T : Set Ω) (x : Ω) (hx : x ∈ Algebra.adjoin ℚ T) :
    ∃ N : ℕ, 0 < N ∧ (N : Ω) * x ∈ Algebra.adjoin ℤ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have h : ((r.den : ℚ) * r) = (r.num : ℚ) := Rat.den_mul_eq_num r
      have := congrArg (algebraMap ℚ Ω) h
      rwa [map_mul, map_natCast, map_intCast] at this
    rw [this]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : Ω) * (x + y) = (M : Ω) * (N * x) + (N : Ω) * (M * y) := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : Ω) * (x * y) = (N * x) * (M * y) := by push_cast; ring
    rw [this]
    exact mul_mem hx hy

/- English proof (translation)
Take `⟨p, hmon, hp⟩` from `hx`. Establish `hc : ∀ i, ∃ N : ℕ, 0 < N ∧ (N : Ω) * (p.coeff i : Ω) ∈ Algebra.adjoin ℤ T` using `fun i => adjoin_rat_clear T _ (p.coeff i).2`. Use `choose N hN hNm using hc`. Take `⟨M, hM⟩ : ∃ M, M = ∏ i ∈ Finset.range (p.natDegree + 1), N i` from `⟨_, rfl⟩`. Establish `hMpos : 0 < M` using `hM ▸ Finset.prod_pos fun i _ => hN i`.

Establish `hMc : ∀ i, (M : Ω) * (p.coeff i : Ω) ∈ Algebra.adjoin ℤ T`. Introduce `i`. Distinguish the cases in `hi : i ∈ Finset.range (p.natDegree + 1)`. Rewrite using `[hM, ← Finset.mul_prod_erase _ _ hi, Nat.cast_mul, mul_comm (N i : Ω), mul_assoc]`. Conclude with `mul_mem (natCast_mem _ _) (hNm i)`.

Rewrite `hi` using `[Finset.mem_range, not_lt]`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]`. Simplify using the standard rewrite rules. Establish `hlift : Polynomial.C (M : Ω) * p.map (algebraMap (Algebra.adjoin ℚ T) Ω) ∈ Polynomial.lifts (algebraMap (Algebra.adjoin ℤ T) Ω)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `n`. Rewrite using `[Polynomial.coeff_C_mul, Polynomial.coeff_map]`. Conclude with `⟨⟨_, hMc n⟩, rfl⟩`. Take `⟨q, hq⟩` from `(Polynomial.mem_lifts _).mp hlift`. Establish `hinj : Function.Injective (algebraMap (Algebra.adjoin ℤ T) Ω)` using `Subtype.val_injective`.

Establish `hpm : (p.map (algebraMap (Algebra.adjoin ℚ T) Ω)).Monic` using `hmon.map _`. Establish `hlc : algebraMap _ Ω q.leadingCoeff = (M : Ω)`. Rewrite using `[← Polynomial.leadingCoeff_map_of_injective hinj, hq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hpm.leadingCoeff, mul_one]`. Establish `hroot : Polynomial.aeval x q = 0`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, hp, mul_zero]`.

Establish `hint` using `isIntegral_leadingCoeff_smul q x hroot`. Use `⟨M, hMpos, ?_⟩` and prove the remaining obligations. Rewrite `hint` using `[Algebra.smul_def, hlc]`. Then use the resulting hypothesis.
-/
theorem integral_rat_clear {Ω : Type} [Field Ω] [CharZero Ω] (T : Set Ω) (x : Ω)
    (hx : IsIntegral (Algebra.adjoin ℚ T) x) :
    ∃ N : ℕ, 0 < N ∧ IsIntegral (Algebra.adjoin ℤ T) ((N : Ω) * x) := by
  classical
  obtain ⟨p, hmon, hp⟩ := hx
  have hc : ∀ i, ∃ N : ℕ, 0 < N ∧ (N : Ω) * (p.coeff i : Ω) ∈ Algebra.adjoin ℤ T :=
    fun i => adjoin_rat_clear T _ (p.coeff i).2
  choose N hN hNm using hc
  obtain ⟨M, hM⟩ : ∃ M, M = ∏ i ∈ Finset.range (p.natDegree + 1), N i := ⟨_, rfl⟩
  have hMpos : 0 < M := hM ▸ Finset.prod_pos fun i _ => hN i
  have hMc : ∀ i, (M : Ω) * (p.coeff i : Ω) ∈ Algebra.adjoin ℤ T := by
    intro i
    by_cases hi : i ∈ Finset.range (p.natDegree + 1)
    · rw [hM, ← Finset.mul_prod_erase _ _ hi, Nat.cast_mul, mul_comm (N i : Ω), mul_assoc]
      exact mul_mem (natCast_mem _ _) (hNm i)
    · rw [Finset.mem_range, not_lt] at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have hlift : Polynomial.C (M : Ω) * p.map (algebraMap (Algebra.adjoin ℚ T) Ω) ∈
      Polynomial.lifts (algebraMap (Algebra.adjoin ℤ T) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    exact ⟨⟨_, hMc n⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp hlift
  have hinj : Function.Injective (algebraMap (Algebra.adjoin ℤ T) Ω) := Subtype.val_injective
  have hpm : (p.map (algebraMap (Algebra.adjoin ℚ T) Ω)).Monic := hmon.map _
  have hlc : algebraMap _ Ω q.leadingCoeff = (M : Ω) := by
    rw [← Polynomial.leadingCoeff_map_of_injective hinj, hq, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, hpm.leadingCoeff, mul_one]
  have hroot : Polynomial.aeval x q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_map, hp, mul_zero]
  have hint := isIntegral_leadingCoeff_smul q x hroot
  refine ⟨M, hMpos, ?_⟩
  rwa [Algebra.smul_def, hlc] at hint

/- English proof (translation)
Introduce `K _ ι _ Ω _ y _ d a s hs`. Establish `hc : ∀ c : ∀ k, ι k, ∃ N : ℕ, 0 < N ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegral (chartRingZ y c) ((N : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))))`. Introduce `c`. Distinguish the cases in `hy : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨N, hN, hint⟩` from `integral_rat_clear _ _ (hs c hy)`.

Conclude with `⟨N, hN, fun _ => hint⟩`. Conclude with `⟨1, one_pos, fun h => absurd h hy⟩`. Use `choose N hN hNint using hc`. Use `⟨∏ c, N c, Finset.prod_pos fun c _ => hN c, ?_⟩` and prove the remaining obligations. Introduce `c hy`.

Rewrite using `[mem_integralClosure_iff]`. Simplify using `only [Nat.cast_one, one_mul]`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Nat.cast_mul, mul_comm (N c : Ω), mul_assoc, mul_assoc]`. Conclude with `IsIntegral.mul (isIntegral_natCast _) (by simpa only [mul_assoc] using hNint c hy)`.
-/
theorem exists_integer_multiple_in_lattice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) [CharZero Ω] (d : ℕ) (a : K → ℤ) (s : Ω), (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k)))) → ∃ N₀ : ℕ, 0 < N₀ ∧ (N₀ : Ω) * s ∈ chartLatNm y a 1 := by
  intro K _ ι _ Ω _ y _ d a s hs
  classical
  have hc : ∀ c : ∀ k, ι k, ∃ N : ℕ, 0 < N ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      IsIntegral (chartRingZ y c) ((N : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-(a k))))) := by
    intro c
    by_cases hy : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨N, hN, hint⟩ := integral_rat_clear _ _ (hs c hy)
      exact ⟨N, hN, fun _ => hint⟩
    · exact ⟨1, one_pos, fun h => absurd h hy⟩
  choose N hN hNint using hc
  refine ⟨∏ c, N c, Finset.prod_pos fun c _ => hN c, ?_⟩
  intro c hy
  rw [mem_integralClosure_iff]
  simp only [Nat.cast_one, one_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Nat.cast_mul, mul_comm (N c : Ω), mul_assoc, mul_assoc]
  exact IsIntegral.mul (isIntegral_natCast _) (by simpa only [mul_assoc] using hNint c hy)

end MultiProjectiveCoordinates
