import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.FockSrcDec

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]`. Use `(MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.pderiv_monomial]`. Distinguish the cases in `h : s b = 0`. Simplify using `[h]`.

Use `le_trans ?_ (MvPolynomial.le_totalDegree hs)` and prove the remaining obligations. Rewrite using `[MvPolynomial.X, MvPolynomial.monomial_mul]`. Use `(MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1)`. Rewrite using `[add_tsub_cancel_of_le]`.

Conclude with `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)`. Use `conv_rhs => rw [h1]`. Rewrite using `[Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]`. Simplify using `[Function.id_def]`.
-/
theorem deg_X_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.X a * MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

/- English proof (translation)
Distinguish the cases in `h : MvPolynomial.pderiv b P = 0`. Simplify using `[h]`. Use `deg_X_pderiv b b P` as an intermediate fact. Rewrite `this` using `[MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _) h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem deg_pderiv {σ : Type} (b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  by_cases h : MvPolynomial.pderiv b P = 0
  · simp [h]
  · have := deg_X_pderiv b b P
    rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _) h] at this
    omega

/- English proof (translation)
Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `(MvPolynomial.totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.pderiv_X, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem deg_pderiv_X {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b (MvPolynomial.X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (MvPolynomial.totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (MvPolynomial.totalDegree_smul_le _ _).trans (h P)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_nonRaising {σ : Type} {L : Module.End ℂ (MvPolynomial σ ℂ)} :
    L ∈ nonRaising σ ↔ ∀ P, (L P).totalDegree ≤ P.totalDegree := Iff.rfl

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i : Fin b) (j k : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' i ≠ ε k then
    (sgn (ε j) * sgn (ε k)) • (MvPolynomial.X (τ, i, j) * MvPolynomial.X (τ, i, k)) else 0

/- English proof (translation)
Unfold `quad`. Use `split_ifs`. Conclude with `(MvPolynomial.homogeneousSubmodule _ ℂ 2).smul_mem _ ((MvPolynomial.isHomogeneous_X ℂ _).mul (MvPolynomial.isHomogeneous_X ℂ _))`. Conclude with `MvPolynomial.isHomogeneous_zero _ _ _`.
-/
theorem quad_hom (i : Fin b) (j k : Fin a) : (quad τ ε ε' i j k).IsHomogeneous 2 := by
  unfold quad
  split_ifs
  · exact (MvPolynomial.homogeneousSubmodule _ ℂ 2).smul_mem _
      ((MvPolynomial.isHomogeneous_X ℂ _).mul (MvPolynomial.isHomogeneous_X ℂ _))
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/- English proof (translation)
Unfold `raiO lowO quad`. Apply the tactic sequence `by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' i = ε k`. Rewrite using `[if_pos h1, if_pos h2, if_neg (fun h => h.2 h2), LinearMap.mulLeft_zero_eq_zero, sub_zero, smul_mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => deg_X_pderiv _ _ P)`. Rewrite using `[if_pos h1, if_neg h2, if_pos ⟨h1, h2⟩]`.

Use `Submodule.zero_mem _` and compare the differences between its conclusion and the goal. Rewrite using `[sub_eq_zero]`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Simplify using `[smul_smul, mul_assoc, mul_comm (sgn (ε k))]`. Rewrite using `[if_neg h1, if_pos h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero, smul_mul_smul_comm, neg_mul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.neg_mem _ (mem_nonRaising.2 fun P => (deg_pderiv _ _).trans (deg_pderiv _ P)))`. Rewrite using `[if_neg h1, if_neg h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero, smul_mul_smul_comm, neg_mul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.neg_mem _ (mem_nonRaising.2 fun P => deg_pderiv_X _ _ P))`.
-/
theorem term_mem (i : Fin b) (j k : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' i k - LinearMap.mulLeft ℂ (quad τ ε ε' i j k) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' i = ε k
  · rw [if_pos h1, if_pos h2, if_neg (fun h => h.2 h2), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm]
    exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => deg_X_pderiv _ _ P)
  · rw [if_pos h1, if_neg h2, if_pos ⟨h1, h2⟩]
    convert Submodule.zero_mem _
    rw [sub_eq_zero]
    refine LinearMap.ext fun P => ?_
    simp [smul_smul, mul_assoc, mul_comm (sgn (ε k))]
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm, neg_mul]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (mem_nonRaising.2 fun P => (deg_pderiv _ _).trans (deg_pderiv _ P)))
  · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm, neg_mul]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (mem_nonRaising.2 fun P => deg_pderiv_X _ _ P))

def quadS (X : Matrix (Fin a) (Fin a) ℂ) : PolF D b a :=
  ∑ j, ∑ k, X j k • ∑ i, quad τ ε ε' i j k

/- English proof (translation)
The claim follows from `(MvPolynomial.homogeneousSubmodule _ ℂ 2).sum_mem fun j _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ <| Submodule.sum_mem _ fun i _ => quad_hom τ ε ε' i j k`.
-/
theorem quadS_hom (X : Matrix (Fin a) (Fin a) ℂ) : (quadS τ ε ε' X).IsHomogeneous 2 :=
  (MvPolynomial.homogeneousSubmodule _ ℂ 2).sum_mem fun j _ =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ <|
      Submodule.sum_mem _ fun i _ => quad_hom τ ε ε' i j k

/- English proof (translation)
Establish `h : LinearMap.mulLeft ℂ (quadS τ ε ε' X) = ∑ j, ∑ k, X j k • ∑ i, LinearMap.mulLeft ℂ (quad τ ε ε' i j k)`. Use `LinearMap.ext fun P => ?_` and prove the remaining obligations. Simplify using `[quadS, Finset.sum_mul, LinearMap.sum_apply]`. Rewrite using `[h, fockS, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub, ← Finset.sum_sub_distrib]`. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[add_sub_right_comm]`.

Use `Submodule.add_mem _ (term_mem τ ε ε' i j k) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => le_rfl)`. Conclude with `Submodule.zero_mem _`.
-/
theorem rest_mem (X : Matrix (Fin a) (Fin a) ℂ) :
    fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X) ∈ nonRaising (FVar D b a) := by
  have h : LinearMap.mulLeft ℂ (quadS τ ε ε' X) =
      ∑ j, ∑ k, X j k • ∑ i, LinearMap.mulLeft ℂ (quad τ ε ε' i j k) := by
    refine LinearMap.ext fun P => ?_
    simp [quadS, Finset.sum_mul, LinearMap.sum_apply]
  rw [h, fockS, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
  rw [add_sub_right_comm]
  refine Submodule.add_mem _ (term_mem τ ε ε' i j k) ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => le_rfl)
  · exact Submodule.zero_mem _

/- English proof (translation)
Apply the tactic sequence `cases e <;> simp [sgn]`.
-/
theorem sgn_ne_zero (e : Bool) : sgn e ≠ 0 := by
  cases e <;> simp [sgn]

/- English proof (translation)
Introduce `h0`. Set `f : FVar D b a → ℂ` to `fun v => if v = (τ, i, j) ∨ v = (τ, i, k) then 1 else 0`. Establish `key : ∀ i' j' k', MvPolynomial.aeval f (quad τ ε ε' i' j' k') = if i' = i ∧ j' = j ∧ k' = k then sgn (ε j) * sgn (ε k) else 0`. Introduce `i' j' k'`. Distinguish the cases in `h : i' = i ∧ j' = j ∧ k' = k`.

Take `⟨rfl, rfl, rfl⟩` from `h`. Simplify using `[quad, hj, f, hj ▸ hk]`. Rewrite using `[if_neg h]`. Unfold `quad`. Use `split_ifs with h'`.

Simplify using `only [map_smul, map_mul, MvPolynomial.aeval_X, f, Prod.mk.injEq, true_and] split_ifs with h1 h2`. It suffices to derive a contradiction. Apply the tactic sequence `rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨-, rfl⟩ | ⟨-, rfl⟩`. Conclude with `h'.2 hj`. Conclude with `h ⟨rfl, rfl, rfl⟩`.

Conclude with `hk h'.1`. Conclude with `hk h'.1`. Apply the tactic sequence `all_goals simp`. Simplify using the standard rewrite rules. Establish `h1` using `congrArg (MvPolynomial.aeval f) h0`.

Simplify using `only [quadS, map_sum, map_smul, key, map_zero] at h1`. Rewrite `h1` using `[Finset.sum_eq_single j, Finset.sum_eq_single k, Finset.sum_eq_single i]`. Simplify using `[hX, sgn_ne_zero] at h1`. Introduce `i' _ h`. Simplify using `[h]`.

Simplify using the standard rewrite rules. Introduce `i' _ h`. Simplify using `[h]`. Simplify using the standard rewrite rules. Introduce `i' _ h`.

Simplify using `[h]`. Simplify using the standard rewrite rules.
-/
theorem quadS_ne_zero (X : Matrix (Fin a) (Fin a) ℂ) (i : Fin b) (j k : Fin a) (hj : ε' i = ε j)
    (hk : ε' i ≠ ε k) (hX : X j k ≠ 0) : quadS τ ε ε' X ≠ 0 := by
  classical
  intro h0
  let f : FVar D b a → ℂ := fun v => if v = (τ, i, j) ∨ v = (τ, i, k) then 1 else 0
  have key : ∀ i' j' k', MvPolynomial.aeval f (quad τ ε ε' i' j' k') =
      if i' = i ∧ j' = j ∧ k' = k then sgn (ε j) * sgn (ε k) else 0 := by
    intro i' j' k'
    by_cases h : i' = i ∧ j' = j ∧ k' = k
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [quad, hj, f, hj ▸ hk]
    · rw [if_neg h]
      unfold quad
      split_ifs with h'
      · simp only [map_smul, map_mul, MvPolynomial.aeval_X, f, Prod.mk.injEq, true_and]
        split_ifs with h1 h2
        · exfalso
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact h'.2 hj
          · exact h ⟨rfl, rfl, rfl⟩
          · exact hk h'.1
          · exact hk h'.1
        all_goals simp
      · simp
  have h1 := congrArg (MvPolynomial.aeval f) h0
  simp only [quadS, map_sum, map_smul, key, map_zero] at h1
  rw [Finset.sum_eq_single j, Finset.sum_eq_single k, Finset.sum_eq_single i] at h1
  · simp [hX, sgn_ne_zero] at h1
  · intro i' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp

/- English proof (translation)
Introduce and unpack `D a b τ ε ε' X hb ⟨j, k, hjk, h1, h2⟩`. Use `⟨quadS τ ε ε' X, fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X), ?_, quadS_hom τ ε ε' X, mem_nonRaising.1 (rest_mem τ ε ε' X), by abel⟩` and prove the remaining obligations. Distinguish the cases in `h : ε' ⟨0, hb⟩ = ε j`. Conclude with `quadS_ne_zero τ ε ε' X ⟨0, hb⟩ j k h (h ▸ hjk) h1`. Use `quadS_ne_zero τ ε ε' X ⟨0, hb⟩ k j ?_ h h2 revert h hjk` and prove the remaining obligations.

Apply the tactic sequence `cases ε' ⟨0, hb⟩ <;> cases ε j <;> cases ε k <;> simp`.
-/
theorem fockS_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X : Matrix (Fin a) (Fin a) ℂ), 0 < b → (∃ j k, ε j ≠ ε k ∧ X j k ≠ 0 ∧ X k j ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' X = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' X hb ⟨j, k, hjk, h1, h2⟩
  refine ⟨quadS τ ε ε' X, fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X), ?_, quadS_hom τ ε ε' X,
    mem_nonRaising.1 (rest_mem τ ε ε' X), by abel⟩
  by_cases h : ε' ⟨0, hb⟩ = ε j
  · exact quadS_ne_zero τ ε ε' X ⟨0, hb⟩ j k h (h ▸ hjk) h1
  · refine quadS_ne_zero τ ε ε' X ⟨0, hb⟩ k j ?_ h h2
    revert h hjk
    cases ε' ⟨0, hb⟩ <;> cases ε j <;> cases ε k <;> simp

end GlobalTheory.Chain.RealIt.FockSrcDec

end
