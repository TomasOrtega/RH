import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaMemIdealPowOfMemPowSuccStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ A _ D J hl n x y hy`. Establish `hy' : y ∈ J ^ n` using `Ideal.pow_le_pow_right (Nat.le_succ n) hy`. Establish `hδ : D.δ y ∈ J ^ n` using `GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l A D J hl n y hy`. Rewrite using `[D.δ_add x y]`. Establish `e : D.δ x + D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) - D.δ x = D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k)` using `by ring`.

Rewrite using `[e]`. Use `Ideal.sub_mem _ hδ (Ideal.sum_mem _ fun k hk => ?_)` and prove the remaining obligations. Establish `hk' : 0 < l - k` using `Nat.sub_pos_of_lt (Finset.mem_Ioo.1 hk).2`. Establish `: y ^ (l - k) ∈ J ^ n`. Take `⟨m, hm⟩ : ∃ m, l - k = m + 1` from `⟨l - k - 1, by omega⟩`.

Rewrite using `[hm, pow_succ]`. Conclude with `Ideal.mul_mem_left _ _ hy'`. Conclude with `Ideal.mul_mem_left _ _ this`.
-/
theorem delta_add_sub_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  intro l _ A _ D J hl n x y hy
  have hy' : y ∈ J ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hy
  have hδ : D.δ y ∈ J ^ n := GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l A D J hl n y hy
  rw [D.δ_add x y]
  have e : D.δ x + D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) - D.δ x
      = D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) := by ring
  rw [e]
  refine Ideal.sub_mem _ hδ (Ideal.sum_mem _ fun k hk => ?_)
  have hk' : 0 < l - k := Nat.sub_pos_of_lt (Finset.mem_Ioo.1 hk).2
  have : y ^ (l - k) ∈ J ^ n := by
    obtain ⟨m, hm⟩ : ∃ m, l - k = m + 1 := ⟨l - k - 1, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ hy'
  exact Ideal.mul_mem_left _ _ this

end GlobalTheory.BSP
