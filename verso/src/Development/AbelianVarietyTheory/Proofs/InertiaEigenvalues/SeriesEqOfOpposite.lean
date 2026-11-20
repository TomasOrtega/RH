import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.Opp

open GlobalTheory.GLq.Opp

open MonoidAlgebra in

def reg {G H : Type} [Group G] [Group H] (i : G →* H) : Representation ℂ G (MonoidAlgebra ℂ H) where
  toFun x := LinearMap.mulLeft ℂ (single (i x) (1 : ℂ))
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [← MonoidAlgebra.one_def]
  map_mul' x y := by
    refine LinearMap.ext fun v => ?_
    simp [← mul_assoc, single_mul_single]

open MonoidAlgebra in
/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of m => simp [single_mul_single]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, add_mul, mul_add]`. Consider the case `smul r x hx => simp only [map_smul, hx, smul_mul_assoc, mul_smul_comm]`.
-/
theorem map_conj {G : Type} [Group G] (p : G) (a : MonoidAlgebra ℂ G) :
    mapDomainAlgHom ℂ ℂ (MulAut.conj p).toMonoidHom a = single p 1 * a * single p⁻¹ 1 := by
  induction a using MonoidAlgebra.induction_on with
  | of m => simp [single_mul_single]
  | add x y hx hy => simp only [map_add, hx, hy, add_mul, mul_add]
  | smul r x hx => simp only [map_smul, hx, smul_mul_assoc, mul_smul_comm]

variable {g : ℕ} [Fact g.Prime] {k l n : ℕ}

/- English proof (translation)
Establish `h : (fun i j : Fin (k + l) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (x : Mt g k) i j else if k ≤ (i : ℕ) ∧ k ≤ (j : ℕ) then entN (y : Mt g l) (i - k) (j - k) else 0) = ((par finSumFinEquiv x 0 y : Gn g (k + l)) : Mt g (k + l))`. Use function extensionality and compare the values at `i j`. Take `⟨i, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective j`. Rewrite using `[par_apply]`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify using `[entN]`. Use `i.2` as an intermediate fact. Simplify using `[entN]`. Use `j.2` as an intermediate fact.

Simplify using `[entN]`. Simplify using `[entN]`. Unfold `blk`. Rewrite using `[h, toG, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]`.
-/
theorem blk_eq (x : Gn g k) (y : Gn g l) : blk k l (k + l) x y = par finSumFinEquiv x 0 y := by
  have h : (fun i j : Fin (k + l) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN (x : Mt g k) i j
      else if k ≤ (i : ℕ) ∧ k ≤ (j : ℕ) then entN (y : Mt g l) (i - k) (j - k) else 0) =
      ((par finSumFinEquiv x 0 y : Gn g (k + l)) : Mt g (k + l)) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [entN]
    · have := i.2
      simp [entN]
    · have := j.2
      simp [entN]
    · simp [entN]
  unfold blk
  rw [h, toG, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]

/- English proof (translation)
Establish `e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j))`. Introduce `M i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`. Rewrite using `[tl, entN, dif_pos ⟨by omega, by omega⟩]`.

Both sides reduce to the same expression. Establish `e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))`. Introduce `M i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`.

Rewrite using `[br, entN, dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression. Use `⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)), ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Take `⟨i, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective j`. Rewrite using `[par_apply]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Rewrite using `[← e1 (z : Mt g (k + l)) i j, h1]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[h0 _ _ (by simp) (by simp)]; simp`. Rewrite using `[← e2 (z : Mt g (k + l)) i j, h2]`. Simplify using the standard rewrite rules.
-/
theorem eq_par (z : Gn g (k + l)) (h0 : InPar k (z : Mt g (k + l))) (h1 : tl k (z : Mt g (k + l)) = 1)
    (h2 : br k l (z : Mt g (k + l)) = 1) : ∃ B, z = par finSumFinEquiv 1 B 1 := by
  have e1 : ∀ (M : Mt g (k + l)) (i j : Fin k), tl k M i j = M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [tl, entN, dif_pos ⟨by omega, by omega⟩]
    rfl
  have e2 : ∀ (M : Mt g (k + l)) (i j : Fin l), br k l M i j = M (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) := by
    intro M i j
    have hi := i.2
    have hj := j.2
    rw [br, entN, dif_pos ⟨by omega, by omega⟩]
    rfl
  refine ⟨Matrix.of fun i j => (z : Mt g (k + l)) (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [par_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [← e1 (z : Mt g (k + l)) i j, h1]; simp
  · simp
  · rw [h0 _ _ (by simp) (by simp)]; simp
  · rw [← e2 (z : Mt g (k + l)) i j, h2]; simp

end GlobalTheory.SerSys.Opp
