import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonomialSign

/- English proof (translation)
Establish `hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i)`. Introduce `i`. Establish `h` using `congrFun (congrFun hM i) i`. Rewrite `h` using `[Matrix.diagonal_apply_eq, Matrix.mul_apply]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[← h]`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hex : ∀ i, ∃ a, M a i ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `hd i` to reduce the goal to its premises.

Rewrite using `[hsum i]`. Simplify using `[hne]`. Use `choose r hr using hex`. Establish `hinj : Function.Injective r` using `fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)`. Establish `hbij : Function.Bijective r` using `(Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩`.

Establish `huniq : ∀ a i, M a i ≠ 0 → a = r i`. Introduce `a i h`. Take `⟨j, rfl⟩` from `hbij.2 a`. Rewrite using `[hrow (r j) i j h (hr j)]`. Use extensionality with `a i`.

Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `h : M a i = 0`. Simplify using `[h]`. Establish `ha` using `huniq a i h`. Establish `hdi : d i = ε a * Complex.normSq (M a i)`.

Rewrite using `[hsum i]`. Use `Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)` and prove the remaining obligations. Establish `: M b i = 0`. Assume the negation of the conclusion as `hb'`. Conclude with `hb ((huniq b i hb').trans ha.symm)`.

Simplify using `[this]`. Establish `hpos : 0 < Complex.normSq (M a i)` using `Complex.normSq_pos.2 h`. Break down `hε a with h1 | h1` into its components or cases. Establish `: 0 < d i` using `by rw [hdi, h1]; linarith`. Simplify using `[this, h1]`.

Establish `: ¬ 0 < d i` using `by rw [hdi, h1]; linarith`. Simplify using `[this, h1]`.
-/
theorem diagonal_mul_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι) (ε : ι → ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (M : Matrix ι κ ℂ) (d : κ → ℝ) (hd : ∀ i, d i ≠ 0)
    (hM : Mᴴ * Matrix.diagonal (fun a => (ε a : ℂ)) * M = Matrix.diagonal (fun i => (d i : ℂ)))
    (hrow : ∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) :
    Matrix.diagonal (fun a => (ε a : ℂ)) * M
      = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  have hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i) := by
    intro i
    have h := congrFun (congrFun hM i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    apply Complex.ofReal_injective
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    ring
  have hex : ∀ i, ∃ a, M a i ≠ 0 := by
    intro i
    by_contra hne
    push Not at hne
    apply hd i
    rw [hsum i]
    simp [hne]
  choose r hr using hex
  have hinj : Function.Injective r := fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩
  have huniq : ∀ a i, M a i ≠ 0 → a = r i := by
    intro a i h
    obtain ⟨j, rfl⟩ := hbij.2 a
    rw [hrow (r j) i j h (hr j)]
  ext a i
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a i = 0
  · simp [h]
  · have ha := huniq a i h
    have hdi : d i = ε a * Complex.normSq (M a i) := by
      rw [hsum i]
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
      have : M b i = 0 := by
        by_contra hb'
        exact hb ((huniq b i hb').trans ha.symm)
      simp [this]
    have hpos : 0 < Complex.normSq (M a i) := Complex.normSq_pos.2 h
    rcases hε a with h1 | h1
    · have : 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]
    · have : ¬ 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]

/- English proof (translation)
Introduce `n p q hn M d hd hM hrow`. Establish `hJ : Formalism.UG.Jpq p q = Matrix.diagonal (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ))`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hM`, the goal using `[hJ]`. Use `diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow` and prove the remaining obligations. Apply the tactic sequence `rintro (a | a) <;> simp`.
-/
theorem Jpq_mul_eq : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  intro n p q hn M d hd hM hrow
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal
      (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ] at hM ⊢
  refine diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow
  rintro (a | a) <;> simp

end GlobalTheory.MonomialSign
