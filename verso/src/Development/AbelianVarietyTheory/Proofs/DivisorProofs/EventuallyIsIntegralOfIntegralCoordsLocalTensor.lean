import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

open IsDedekindDomain

/- English proof (translation)
Establish `h` using `(algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2`. Use `filter_upwards [h] with v hv`. Conclude with `hv`.
-/
theorem eventually_rat_mem_adicCompletionIntegers (q : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have h := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  filter_upwards [h] with v hv
  exact hv

/- English proof (translation)
Introduce `p _ G`. Use `set b := Module.finBasis ℚ G.C with hb`. Establish `hev : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k j l, algebraMap ℚ (w.1.adicCompletion ℚ) (b.repr (b k * b j) l) ∈ w.1.adicCompletionIntegers ℚ`. Rewrite using `[Filter.eventually_all]`. Introduce `k`.

Rewrite using `[Filter.eventually_all]`. Introduce `j`. Rewrite using `[Filter.eventually_all]`. Introduce `l`. Conclude with `Subtype.val_injective.tendsto_cofinite.eventually (eventually_rat_mem_adicCompletionIntegers _)`.

Use `filter_upwards [hev] with w hw`. Introduce `x hx`. Use `set B := Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) b with hB`. Establish `hent : ∀ i j, Algebra.leftMulMatrix B x i j ∈ w.1.adicCompletionIntegers ℚ`. Introduce `i j`.

Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul]`. Rewrite using `[← B.sum_repr x]`. Rewrite using `[Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Establish `e : B k * B j = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (b k * b j)`. Simplify using `[hB, Algebra.TensorProduct.basis_apply]`. Rewrite using `[e, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [one_smul, Finsupp.mapRange_apply]`. Conclude with `mul_mem (hx k) (hw k j i)`.

Use `⟨(Algebra.leftMulMatrix B x).charpoly, Matrix.charpoly_monic _, ?_, ?_⟩` and prove the remaining obligations. Introduce `n`. Set `M : Matrix (Fin (Module.finrank ℚ G.C)) (Fin (Module.finrank ℚ G.C)) (w.1.adicCompletionIntegers ℚ)` to `fun i j => ⟨_, hent i j⟩`. Establish `hM : Algebra.leftMulMatrix B x = M.map (algebraMap (w.1.adicCompletionIntegers ℚ) (w.1.adicCompletion ℚ))`. Use extensionality with `i j`.

Both sides reduce to the same expression. Rewrite using `[hM, Matrix.charpoly_map, Polynomial.coeff_map]`. Conclude with `(M.charpoly.coeff n).2`. Apply `Algebra.leftMulMatrix_injective B` to reduce the goal to its premises. Rewrite using `[← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]`.
-/
theorem intC_isIntegral : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧
      (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C with hb
  have hev : ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k j l,
      algebraMap ℚ (w.1.adicCompletion ℚ) (b.repr (b k * b j) l) ∈ w.1.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_all]; intro k
    rw [Filter.eventually_all]; intro j
    rw [Filter.eventually_all]; intro l
    exact Subtype.val_injective.tendsto_cofinite.eventually (eventually_rat_mem_adicCompletionIntegers _)
  filter_upwards [hev] with w hw
  intro x hx
  set B := Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) b with hB
  have hent : ∀ i j, Algebra.leftMulMatrix B x i j ∈ w.1.adicCompletionIntegers ℚ := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← B.sum_repr x]
    rw [Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun k _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have e : B k * B j = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (b k * b j) := by
      simp [hB, Algebra.TensorProduct.basis_apply]
    rw [e, Algebra.TensorProduct.basis_repr_tmul]
    simp only [one_smul, Finsupp.mapRange_apply]
    exact mul_mem (hx k) (hw k j i)
  refine ⟨(Algebra.leftMulMatrix B x).charpoly, Matrix.charpoly_monic _, ?_, ?_⟩
  · intro n
    let M : Matrix (Fin (Module.finrank ℚ G.C)) (Fin (Module.finrank ℚ G.C)) (w.1.adicCompletionIntegers ℚ) :=
      fun i j => ⟨_, hent i j⟩
    have hM : Algebra.leftMulMatrix B x = M.map (algebraMap (w.1.adicCompletionIntegers ℚ) (w.1.adicCompletion ℚ)) := by
      ext i j; rfl
    rw [hM, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff n).2
  · apply Algebra.leftMulMatrix_injective B
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]

end GlobalTheory.FinClsLoc
