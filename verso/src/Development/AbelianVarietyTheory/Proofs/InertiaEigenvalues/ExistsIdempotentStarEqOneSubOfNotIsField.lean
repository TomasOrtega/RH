import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

/- English proof (translation)
Introduce `F E _ _ _ _ _ A hK hL`. Take `⟨-, hinj, hN, hT, hnd⟩` from `Et.quadratic_structure F E A`. Establish `hnt : ∃ x y : A.L, x ≠ y`. Take `⟨x, y, hxy⟩` from `hK.exists_pair_ne`. Conclude with `⟨_, _, hinj.ne hxy⟩`.

Establish `hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩`. Take `⟨y, hy0, hyu⟩` from `hy`.

Establish `hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hy0 (hnd y hcon)`. Take `⟨z, hz⟩` from `hz`.

Take `⟨s, hs⟩` from `hK.mul_inv_cancel hz`. Establish `hn : y * star y = 0`. Assume the negation of the conclusion as `hne`. Establish `h1 : A.NL y ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hN, h0, map_zero]`. Take `⟨n, hn⟩` from `hK.mul_inv_cancel h1`. Apply `hyu (star y * algebraMap A.K A.L n)` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← hN, ← map_mul, hn, map_one]`.

Establish `hs'` using `congrArg (algebraMap A.K A.L) hs`. Rewrite `hs'` using `[map_mul, hT, map_one, star_mul', star_star]`. Establish `hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s`. Rewrite using `[star_mul', star_mul', star_star, A.star_K]`. Use `⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩` and prove the remaining obligations.

Take the linear combination `(star y * z * algebraMap A.K A.L s) * hs' - (z * star z * algebraMap A.K A.L s ^ 2) * hn`. Rewrite using `[hst]`. Take the linear combination `hs'`.
-/
theorem exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'

end GlobalTheory.JR.Hyp
