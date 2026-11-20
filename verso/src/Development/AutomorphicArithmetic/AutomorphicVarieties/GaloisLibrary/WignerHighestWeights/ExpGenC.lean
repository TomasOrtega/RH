import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExpSq
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf11.expSq N h`.
-/
private theorem expSq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (h : N * N = 0) :
    NormedSpace.exp N = 1 + N :=
  _root_.UpperTheory.Reformulated.B.Qf11.expSq N h

/- English proof (translation)
Introduce `n H hH g hg`. Use `Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_` and prove the remaining obligations. Introduce `D hD`. Establish `hD' : ∀ i, D i ≠ 0`. Rewrite `hD` using `[Matrix.det_diagonal, Finset.prod_ne_zero_iff]`.

Conclude with `fun i => hD i (Finset.mem_univ i)`. Use `hH (Matrix.diagonal fun i => Complex.log (D i))` as an intermediate fact. Rewrite `this` using `[Matrix.exp_diagonal]`. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.exp_def]`. Simplify using `only [← Complex.exp_eq_exp_ℂ]`. Conclude with `(Complex.exp_log (hD' i)).symm`. Introduce `t`. Use `hH (Matrix.single t.i t.j t.c)` as an intermediate fact.

Rewrite `this` using `[expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)]`. Conclude with `this`. Introduce `A B _ _ hA hB`. Conclude with `H.mul_mem hA hB`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.expGenC :
    ∀ (n : ℕ) (H : Submonoid (Matrix (Fin n) (Fin n) ℂ)), (∀ X : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp X ∈ H) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, g.det ≠ 0 → g ∈ H := by
  intro n H hH g hg
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
      exact fun i => hD i (Finset.mem_univ i)
    have := hH (Matrix.diagonal fun i => Complex.log (D i))
    rw [Matrix.exp_diagonal] at this
    convert this using 2
    funext i
    rw [Pi.exp_def]
    simp only [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_log (hD' i)).symm
  · intro t
    have := hH (Matrix.single t.i t.j t.c)
    rw [expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)] at this
    exact this
  · intro A B _ _ hA hB
    exact H.mul_mem hA hB
