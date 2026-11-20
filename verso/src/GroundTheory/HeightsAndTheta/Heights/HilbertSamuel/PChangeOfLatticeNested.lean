import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockChainSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.RelIndexNeZeroOfMulMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

set_option linter.unusedSectionVars false

namespace ChangeOfLatticeNested

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

/- English proof (translation)
Take `⟨d, hd0, hdB⟩` from `ChangeOfLattice.exists_clear_den B`. Use `⟨d, Nat.pos_of_ne_zero hd0, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite `hs`, the goal using `[sec_one']`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem s hs`.

Take `⟨i, rfl⟩` from `hs`. Establish `e : (d : Ω) * matAct B x i = matAct ((d : ℚ) • B) x i`. Simplify using `only [matAct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Rewrite using `[e]`. Conclude with `ChangeOfLattice.matAct_mem_span (fun i j => by simpa [Matrix.smul_apply] using hdB i j) x i`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb`. Rewrite using `[mul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul k a _ ha`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ k ha`.
-/
theorem exists_mul_mem_sec_one (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ (matAct B x) 1, (M : Ω) * s ∈ sec ℤ x 1 := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, Nat.pos_of_ne_zero hd0, fun s hs => ?_⟩
  rw [sec_one'] at hs ⊢
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨i, rfl⟩ := hs
    have e : (d : Ω) * matAct B x i = matAct ((d : ℚ) • B) x i := by
      simp only [matAct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact ChangeOfLattice.matAct_mem_span (fun i j => by simpa [Matrix.smul_apply] using hdB i j) x i
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mul_add]
    exact add_mem ha hb
  | smul k a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ k ha

/- English proof (translation)
Establish `h1 : sec ℤ x 1 ≤ sec ℤ (matAct B x) 1`. Rewrite using `[sec_one', sec_one']`. Conclude with `hle`. Establish `one : (sec ℤ (matAct B x) n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup = 1` using `AddSubgroup.relIndex_eq_one.2 fun _ h => ChangeOfLattice.sec_mono hle n h`. Unfold `latLogIndex`.

Rewrite using `[one, Nat.cast_one, Real.log_one, sub_zero, log_relIndex_eq_sum x _ h1 (exists_mul_mem_sec_one x B) n]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.mp hj`. Unfold `twoBlockStep`. Rewrite using `[show n - j - 1 + 1 = n - j by omega]`.
-/
theorem latLogIndex_eq_sum (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ)
    (hle : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x))) (n : ℕ) :
    latLogIndex x (matAct B x) n = ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j := by
  have h1 : sec ℤ x 1 ≤ sec ℤ (matAct B x) 1 := by
    rw [sec_one', sec_one']
    exact hle
  have one : (sec ℤ (matAct B x) n).toAddSubgroup.relIndex (sec ℤ x n).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun _ h => ChangeOfLattice.sec_mono hle n h
  unfold latLogIndex
  rw [one, Nat.cast_one, Real.log_one, sub_zero, log_relIndex_eq_sum x _ h1 (exists_mul_mem_sec_one x B) n]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold twoBlockStep
  rw [show n - j - 1 + 1 = n - j by omega]

end ChangeOfLatticeNested

/- English proof (translation)
Introduce `D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp`. Take `⟨e0, e1⟩` from `hT D Ω κ I x B m m' hI hX hx hB hm hm'`. Establish `h` using `hS D Ω κ I x B m m' hI hX hx hB hm hm' hsp`. Rewrite `h` using `[e0, e1]`. Use `h.congr_left fun n => ?_` and prove the remaining obligations.

Rewrite using `[ChangeOfLatticeNested.latLogIndex_eq_sum x B hsp n]`.
-/
theorem ChangeOfLatticeNested.proof (hS : TwoBlockChainSum.Statement) (hT : TwoBlockTop.Statement) :
    ChangeOfLatticeNested.Statement := by
  intro D Ω _ _ κ _ I x B m m' hI hX hx hB hm hm' hsp
  obtain ⟨e0, e1⟩ := hT D Ω κ I x B m m' hI hX hx hB hm hm'
  have h := hS D Ω κ I x B m m' hI hX hx hB hm hm' hsp
  rw [e0, e1] at h
  refine h.congr_left fun n => ?_
  rw [ChangeOfLatticeNested.latLogIndex_eq_sum x B hsp n]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
