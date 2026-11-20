import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMonicOperatorPolynomials
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.MidThree

open GlobalTheory.LeviHC.MidBlock (stab mem_stab glComm comm_qdet)
open Polynomial

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Use `⟨fun i => ∑ k ∈ s, (f k).coeff i • a k, ?_, fun u => ?_⟩` and prove the remaining obligations. Use `show ∑ k ∈ s, (f k).coeff d • a k = a k₀`. Rewrite using `[Finset.sum_eq_single_of_mem k₀ hk₀ fun k hk hne => by`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (hlt k hk hne), zero_smul]]`. Rewrite using `[← hd, hm.coeff_natDegree, one_smul]`.

Simplify using `only [Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : (f k).natDegree < d + 1`. Distinguish the cases in `h : k = k₀`.

Rewrite using `[h, hd]`. Use linear arithmetic over natural numbers and integers. Use `hlt k hk h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[eval_eq_sum_range' hk', Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`.
-/
theorem polyMap_of_sum {ι : Type} (s : Finset ι) (f : ι → ℂ[X]) (a : ι → A) (d : ℕ) (k₀ : ι) (hk₀ : k₀ ∈ s)
    (hm : (f k₀).Monic) (hd : (f k₀).natDegree = d) (hlt : ∀ k ∈ s, k ≠ k₀ → (f k).natDegree < d) :
    ∃ b : ℕ → A, b d = a k₀ ∧ ∀ u, ∑ k ∈ s, (f k).eval u • a k = ∑ i ∈ Finset.range (d + 1), u ^ i • b i := by
  refine ⟨fun i => ∑ k ∈ s, (f k).coeff i • a k, ?_, fun u => ?_⟩
  · show ∑ k ∈ s, (f k).coeff d • a k = a k₀
    rw [Finset.sum_eq_single_of_mem k₀ hk₀ fun k hk hne => by
      rw [coeff_eq_zero_of_natDegree_lt (hlt k hk hne), zero_smul]]
    rw [← hd, hm.coeff_natDegree, one_smul]
  · simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (f k).natDegree < d + 1 := by
      by_cases h : k = k₀
      · rw [h, hd]; omega
      · have := hlt k hk h; omega
    rw [eval_eq_sum_range' hk', Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]

/- English proof (translation)
Take `⟨d, a, ha, hp⟩` from `hp`. Establish `hdeg : ∀ i, ((X - C t) ^ i).natDegree = i` using `fun i => by`. Rewrite using `[(monic_X_sub_C t).natDegree_pow, natDegree_X_sub_C, mul_one]`. Take `⟨b, hb, e⟩` from `polyMap_of_sum (Finset.range (d + 1)) (fun i => (X - C t) ^ i) a d d (Finset.self_mem_range_succ d) ((monic_X_sub_C t).pow d) (hdeg d) fun k hk hne => by`. Rewrite using `[hdeg]`.

Use `Finset.mem_range.1 hk` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨d, b, hb.trans ha, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hp, ← e]`. Simplify using the standard rewrite rules.
-/
theorem monic_shift {p : ℂ → A} (t : ℂ)
    (hp : ∃ (d : ℕ) (a : ℕ → A), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) :
    ∃ (d : ℕ) (a : ℕ → A), a d = 1 ∧ ∀ u, p (u - t) = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
  obtain ⟨d, a, ha, hp⟩ := hp
  have hdeg : ∀ i, ((X - C t) ^ i).natDegree = i := fun i => by
    rw [(monic_X_sub_C t).natDegree_pow, natDegree_X_sub_C, mul_one]
  obtain ⟨b, hb, e⟩ := polyMap_of_sum (Finset.range (d + 1)) (fun i => (X - C t) ^ i) a d d
    (Finset.self_mem_range_succ d) ((monic_X_sub_C t).pow d) (hdeg d) fun k hk hne => by
      rw [hdeg]; have := Finset.mem_range.1 hk; omega
  refine ⟨d, b, hb.trans ha, fun u => ?_⟩
  rw [hp, ← e]
  simp

end Alg

end GlobalTheory.LeviHC.MidThree

end
