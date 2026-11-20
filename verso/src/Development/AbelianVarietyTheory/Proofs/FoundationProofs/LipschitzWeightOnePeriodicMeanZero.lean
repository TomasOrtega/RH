import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccInvResidueCotStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPeriodicCotEqQExpansionFourierStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummablePeriodicMulInvSubInvFloorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccPeriodicMulInvFloorDivStatement

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LipOne

/- English proof (translation)
Break down `Nat.eq_zero_or_pos L with rfl | hL` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← Finset.sum_product']`. Establish `hL' : (0:ℤ) < L` using `by exact_mod_cast hL`. Use `Finset.sum_nbij' (fun d => ((d % L).toNat, d / L)) (fun p => (p.1 : ℤ) + p.2 * L) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `d hd`. Simplify using `only [Finset.mem_coe, Finset.mem_Ico] at hd`. Simplify using `only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]`. Establish `h1` using `Int.emod_nonneg d hL'.ne'`. Establish `h2` using `Int.emod_lt_of_pos d hL'`.

Establish `h3` using `Int.emod_add_mul_ediv d L`. Use `⟨by omega, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h push_neg at h`. Establish `: (L:ℤ) * (d / L) ≤ L * (-(N:ℤ) - 1)`. Apply `mul_le_mul_of_nonneg_left (by omega) hL'.le` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Assume the negation of the conclusion as `h push_neg at h`. Establish `: (L:ℤ) * (N + 1) ≤ L * (d / L)`. Apply `mul_le_mul_of_nonneg_left (by omega) hL'.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Introduce `p hp`. Simplify using `only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp`. Simplify using `only [Finset.mem_coe, Finset.mem_Ico]`. Take `⟨h1, h2, h3⟩` from `hp`. Establish `h1' : (p.1 : ℤ) < L` using `by exact_mod_cast h1`.

Establish `h0 : (0:ℤ) ≤ p.1` using `by positivity`. Apply the tactic sequence `constructor <;> nlinarith`. Introduce `d hd`. Simplify using `only`. Establish `h1` using `Int.emod_nonneg d hL'.ne'`.

Rewrite using `[Int.toNat_of_nonneg h1]`. Use `Int.emod_add_mul_ediv d L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `p hp`. Simplify using `only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp`.

Establish `h1' : (p.1 : ℤ) < L` using `by exact_mod_cast hp.1`. Use `ext`. Simplify using `only`. Rewrite using `[Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) h1']`. Simplify using the standard rewrite rules.

Simplify using `only`. Rewrite using `[Int.add_mul_ediv_right _ _ hL'.ne', Int.ediv_eq_zero_of_lt (by positivity) h1']`. Simplify using the standard rewrite rules. Introduce `d hd`. Simplify using `only`.

Use `congr 1`. Establish `h1` using `Int.emod_nonneg d hL'.ne'`. Rewrite using `[Int.toNat_of_nonneg h1]`. Use `Int.emod_add_mul_ediv d L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem block (L : ℕ) (f : ℤ → ℂ) (N : ℕ) :
    ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), f d =
      ∑ r ∈ Finset.range L, ∑ n ∈ Finset.Icc (-(N:ℤ)) N, f (r + n * L) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [← Finset.sum_product']
  have hL' : (0:ℤ) < L := by exact_mod_cast hL
  refine Finset.sum_nbij' (fun d => ((d % L).toNat, d / L)) (fun p => (p.1 : ℤ) + p.2 * L) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_Ico] at hd
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
    have h1 := Int.emod_nonneg d hL'.ne'
    have h2 := Int.emod_lt_of_pos d hL'
    have h3 := Int.emod_add_mul_ediv d L
    refine ⟨by omega, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (d / L) ≤ L * (-(N:ℤ) - 1) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
    · by_contra h
      push_neg at h
      have : (L:ℤ) * (N + 1) ≤ L * (d / L) := by
        apply mul_le_mul_of_nonneg_left (by omega) hL'.le
      nlinarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hp
    simp only [Finset.mem_coe, Finset.mem_Ico]
    obtain ⟨h1, h2, h3⟩ := hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast h1
    have h0 : (0:ℤ) ≤ p.1 := by positivity
    constructor <;> nlinarith
  · intro d hd
    simp only
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
    have h1' : (p.1 : ℤ) < L := by exact_mod_cast hp.1
    ext
    · simp only
      rw [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) h1']
      simp
    · simp only
      rw [Int.add_mul_ediv_right _ _ hL'.ne', Int.ediv_eq_zero_of_lt (by positivity) h1']
      simp
  · intro d hd
    simp only
    congr 1
    have h1 := Int.emod_nonneg d hL'.ne'
    rw [Int.toNat_of_nonneg h1]
    have := Int.emod_add_mul_ediv d L
    linarith

/- English proof (translation)
Introduce `L φ z hL hz h0`. Establish `hLz : (L:ℤ) ≠ 0` using `by exact_mod_cast hL.ne'`. Establish `htrm : ∀ w : ℂ, trm 1 0 w = w⁻¹`. Introduce `w`. Simplify using `[trm]`.

Simplify using `only [htrm]`. Establish `hsum0 : ∑ r ∈ Finset.range L, φ r = 0` using `by simpa [hat] using h0`. Use `set g : ℤ → ℂ := fun d => φ d * ((z + d)⁻¹ - (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) with hg`. Establish `hs : Summable g` using `T.summable_periodic_mul_inv_sub_inv_floor' L φ z hL hz`. Establish `hsplit : ∀ s : Finset ℤ, ∑ d ∈ s, φ d * (z + d)⁻¹ = ∑ d ∈ s, g d + ∑ d ∈ s, φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹`.

Introduce `s`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [hg]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmonoF : Monotone (fun R : ℕ => Finset.Icc (-(R:ℤ)) R)`. Introduce `a b hab`. Establish `: (a:ℤ) ≤ b` using `by exact_mod_cast hab`. Conclude with `Finset.Icc_subset_Icc (by omega) (by omega)`. Establish `hcovF : ∀ d : ℤ, ∃ R : ℕ, d ∈ Finset.Icc (-(R:ℤ)) R`.

Introduce `d`. Conclude with `⟨d.natAbs, by simp only [Finset.mem_Icc]; omega⟩`. Establish `hmonoG : Monotone (fun N : ℕ => Finset.Ico (-(N * L : ℤ)) ((N + 1) * L))`. Introduce `a b hab`. Establish `: (a:ℤ) ≤ b` using `by exact_mod_cast hab`.

Establish `hL0 : (0:ℤ) ≤ L` using `by positivity`. Conclude with `Finset.Ico_subset_Ico (by nlinarith) (by nlinarith)`. Establish `hcovG : ∀ d : ℤ, ∃ N : ℕ, d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L)`. Introduce `d`. Use `⟨d.natAbs, ?_⟩` and prove the remaining obligations.

Establish `h1 : (1:ℤ) ≤ L` using `by exact_mod_cast hL`. Establish `h3 : (d.natAbs : ℤ) = |d|` using `Int.natCast_natAbs d`. Establish `h4 : (0:ℤ) ≤ |d|` using `abs_nonneg d`. Simplify using `only [Finset.mem_Ico]`. Rewrite using `[h3]`.

Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[neg_abs_le d]`. Use polynomial arithmetic with `[le_abs_self d]`. Establish `hF` using `Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoF hcovF)`. Establish `hG` using `Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoG hcovG)`.

Establish `hzero : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ = 0`. Introduce `N`. Rewrite using `[block L (fun d : ℤ => φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) N]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Establish `hr' : (r:ℤ) < L` using `by exact_mod_cast Finset.mem_range.mp hr`. Rewrite using `[Int.add_mul_ediv_right _ _ hLz, Int.ediv_eq_zero_of_lt (by positivity) hr', zero_add]`. Use `congr 1`.

Use `push_cast`. Simplify using `[ZMod.natCast_self]`. Use `_ = 0 := by rw [← Finset.sum_mul, hsum0, zero_mul]`. Establish `hb : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), φ d * (z + d)⁻¹ = ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹`. Introduce `N`.

Rewrite using `[block L (fun d : ℤ => φ d * (z + d)⁻¹) N]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `push_cast`.

Simplify using `only [ZMod.natCast_self, mul_zero, add_zero]`. Put the polynomial expressions in normal form. Establish `hmain` using `tendsto_finset_sum (Finset.range L) fun r (_ : r ∈ Finset.range L) => (T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot L z r hL hz).const_mul (φ r)`. Rewrite `hmain` using `[T.sum_periodic_cot_eq_qExpansion_fourier L φ z hL hz h0]`. Establish `hT : ∑' d, g d = -2 * ↑π * Complex.I / ↑L * ∑' (m : ℕ), hat φ ↑(m + 1) * cexp (2 * ↑π * Complex.I * ↑(m + 1) * z / ↑L)`.

Use `tendsto_nhds_unique ?_ hmain` and prove the remaining obligations. Use `hG.congr fun N => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← hb N, hsplit, hzero N, add_zero]`. Establish `hlim` using `hF.add (T.tendsto_sum_Icc_periodic_mul_inv_floor_div L φ z hL hz h0)`.

Rewrite `hlim` using `[add_zero, hT]`. Use `hlim.congr fun R => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[hsplit]`.
-/
theorem lipschitz_one : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm 1 0 (z + d)) atTop (𝓝 (-2 * π * Complex.I / L * ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro L φ z hL hz h0
  have hLz : (L:ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have htrm : ∀ w : ℂ, trm 1 0 w = w⁻¹ := by
    intro w
    simp [trm]
  simp only [htrm]
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by simpa [hat] using h0
  set g : ℤ → ℂ := fun d => φ d * ((z + d)⁻¹ - (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) with hg
  have hs : Summable g := T.summable_periodic_mul_inv_sub_inv_floor' L φ z hL hz
  have hsplit : ∀ s : Finset ℤ, ∑ d ∈ s, φ d * (z + d)⁻¹ =
      ∑ d ∈ s, g d + ∑ d ∈ s, φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ := by
    intro s
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have hmonoF : Monotone (fun R : ℕ => Finset.Icc (-(R:ℤ)) R) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  have hcovF : ∀ d : ℤ, ∃ R : ℕ, d ∈ Finset.Icc (-(R:ℤ)) R := by
    intro d
    exact ⟨d.natAbs, by simp only [Finset.mem_Icc]; omega⟩
  have hmonoG : Monotone (fun N : ℕ => Finset.Ico (-(N * L : ℤ)) ((N + 1) * L)) := by
    intro a b hab
    have : (a:ℤ) ≤ b := by exact_mod_cast hab
    have hL0 : (0:ℤ) ≤ L := by positivity
    exact Finset.Ico_subset_Ico (by nlinarith) (by nlinarith)
  have hcovG : ∀ d : ℤ, ∃ N : ℕ, d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L) := by
    intro d
    refine ⟨d.natAbs, ?_⟩
    have h1 : (1:ℤ) ≤ L := by exact_mod_cast hL
    have h3 : (d.natAbs : ℤ) = |d| := Int.natCast_natAbs d
    have h4 : (0:ℤ) ≤ |d| := abs_nonneg d
    simp only [Finset.mem_Ico]
    rw [h3]
    constructor
    · nlinarith [neg_abs_le d]
    · nlinarith [le_abs_self d]
  have hF := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoF hcovF)
  have hG := Filter.Tendsto.comp hs.hasSum (Filter.tendsto_atTop_finset_of_monotone hmonoG hcovG)
  have hzero : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L),
      φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹ = 0 := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + ((L:ℤ) * (d / L) : ℤ))⁻¹) N]
    calc _ = ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + ((L:ℤ) * n : ℤ))⁻¹ := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          have hr' : (r:ℤ) < L := by exact_mod_cast Finset.mem_range.mp hr
          rw [Int.add_mul_ediv_right _ _ hLz, Int.ediv_eq_zero_of_lt (by positivity) hr', zero_add]
          congr 1
          push_cast
          simp [ZMod.natCast_self]
      _ = 0 := by rw [← Finset.sum_mul, hsum0, zero_mul]
  have hb : ∀ N : ℕ, ∑ d ∈ Finset.Ico (-(N * L : ℤ)) ((N + 1) * L), φ d * (z + d)⁻¹ =
      ∑ r ∈ Finset.range L, φ r * ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹ := by
    intro N
    rw [block L (fun d : ℤ => φ d * (z + d)⁻¹) N]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero]
    ring_nf
  have hmain := tendsto_finset_sum (Finset.range L)
    fun r (_ : r ∈ Finset.range L) => (T.tendsto_sum_Icc_inv_add_mul_eq_pi_div_mul_cot L z r hL hz).const_mul (φ r)
  rw [T.sum_periodic_cot_eq_qExpansion_fourier L φ z hL hz h0] at hmain
  have hT : ∑' d, g d = -2 * ↑π * Complex.I / ↑L * ∑' (m : ℕ), hat φ ↑(m + 1) *
      cexp (2 * ↑π * Complex.I * ↑(m + 1) * z / ↑L) := by
    refine tendsto_nhds_unique ?_ hmain
    refine hG.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← hb N, hsplit, hzero N, add_zero]
  have hlim := hF.add (T.tendsto_sum_Icc_periodic_mul_inv_floor_div L φ z hL hz h0)
  rw [add_zero, hT] at hlim
  refine hlim.congr fun R => ?_
  simp only [Function.comp_apply]
  rw [hsplit]

end GlobalTheory.EisM.LipOne
