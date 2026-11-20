import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.ChartDenom

/- English proof (translation)
Unfold `chartRingQ at hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, one_mul]`.

Conclude with `Algebra.subset_adjoin hx`. Consider the case `algebraMap r`. Use `⟨r.den, r.den_ne_zero, ?_⟩` and prove the remaining obligations. Establish `h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω)`. Establish `hd : ((r.den : ℕ) : Ω) ≠ 0` using `Nat.cast_ne_zero.2 r.den_ne_zero`.

Rewrite using `[eq_ratCast, Rat.cast_def]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h]`. Conclude with `intCast_mem _ _`. Consider the case `add u v _ _ hu hv`.

Take `⟨m, hm, hmu⟩` from `hu`. Take `⟨n, hn, hnv⟩` from `hv`. Use `⟨m * n, mul_ne_zero hm hn, ?_⟩` and prove the remaining obligations. Establish `e : ((m * n : ℕ) : Ω) * (u + v) = (n : Ω) * ((m : Ω) * u) + (m : Ω) * ((n : Ω) * v)` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `add_mem (mul_mem (natCast_mem _ _) hmu) (mul_mem (natCast_mem _ _) hnv)`. Consider the case `mul u v _ _ hu hv`. Take `⟨m, hm, hmu⟩` from `hu`. Take `⟨n, hn, hnv⟩` from `hv`. Use `⟨m * n, mul_ne_zero hm hn, ?_⟩` and prove the remaining obligations.

Establish `e : ((m * n : ℕ) : Ω) * (u * v) = ((m : Ω) * u) * ((n : Ω) * v)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `mul_mem hmu hnv`.
-/
theorem exists_nat_mul_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingQ y c) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : Ω) * x ∈ chartRingZ y c := by
  unfold chartRingQ at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Nat.cast_one, one_mul]
    exact Algebra.subset_adjoin hx
  | algebraMap r =>
    refine ⟨r.den, r.den_ne_zero, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_ne_zero
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [h]
    exact intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u + v) = (n : Ω) * ((m : Ω) * u) + (m : Ω) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hmu) (mul_mem (natCast_mem _ _) hnv)
  | mul u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have e : ((m * n : ℕ) : Ω) * (u * v) = ((m : Ω) * u) * ((n : Ω) * v) := by
      push_cast; ring
    rw [e]
    exact mul_mem hmu hnv

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y a τ s hs`. Establish `hex : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) → (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) ∈ chartRingZ y c)`. Introduce `c`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Take `⟨n, hn, h⟩` from `exists_nat_mul_mem_chartRingZ y c (hs c hc)`.

Conclude with `⟨n, hn, fun _ => h⟩`. Conclude with `⟨1, one_ne_zero, fun h => absurd h hc⟩`. Use `choose n hn0 hn using hex`. Establish `hN : (∏ c, n c) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun c _ => hn0 c`. Establish `hNΩ : (((∏ c, n c : ℕ)) : Ω) ≠ 0` using `Nat.cast_ne_zero.2 hN`.

Establish `hmem : (((∏ c, n c : ℕ)) : Ω) * s ∈ chartLatNm y a τ`. Introduce `c hc`. Establish `e : ((((∏ c, n c : ℕ)) : Ω) * s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) * ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))))`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `h : (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) * ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) ∈ chartRingZ y c` using `mul_mem (natCast_mem _ _) (hn c hc)`. Conclude with `Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω) (⟨_, h⟩ : chartRingZ y c)`. Establish `h1 : (((∏ c, n c : ℕ)) : Ω) * s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω)` using `Submodule.subset_span hmem`.

Establish `h2` using `Submodule.smul_mem _ (((∏ c, n c : ℕ) : ℚ)⁻¹) h1`. Establish `e : (((∏ c, n c : ℕ) : ℚ)⁻¹) • ((((∏ c, n c : ℕ)) : Ω) * s) = s`. Rewrite using `[Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hNΩ, one_mul]`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem chartLatQ_le_span_chartLatNm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ),
      chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  intro K _ ι _ Ω _ _ y a τ s hs
  classical
  have hex : ∀ c : ∀ k, ι k, ∃ n : ℕ, n ≠ 0 ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_chartRingZ y c (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hc⟩
  choose n hn0 hn using hex
  have hN : (∏ c, n c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hn0 c
  have hNΩ : (((∏ c, n c : ℕ)) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : (((∏ c, n c : ℕ)) : Ω) * s ∈ chartLatNm y a τ := by
    intro c hc
    have e : ((((∏ c, n c : ℕ)) : Ω) * s) * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
          ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      push_cast; ring
    rw [e]
    have h : (((∏ c' ∈ Finset.univ.erase c, n c' : ℕ)) : Ω) *
        ((n c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)))) ∈ chartRingZ y c :=
      mul_mem (natCast_mem _ _) (hn c hc)
    exact Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω) (⟨_, h⟩ : chartRingZ y c)
  have h1 : (((∏ c, n c : ℕ)) : Ω) * s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω) :=
    Submodule.subset_span hmem
  have h2 := Submodule.smul_mem _ (((∏ c, n c : ℕ) : ℚ)⁻¹) h1
  have e : (((∏ c, n c : ℕ) : ℚ)⁻¹) • ((((∏ c, n c : ℕ)) : Ω) * s) = s := by
    rw [Rat.smul_def, Rat.cast_inv, Rat.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hNΩ, one_mul]
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.ChartDenom
