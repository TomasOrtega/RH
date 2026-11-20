import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.GroupTheory.CosetCover

open scoped Pointwise in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pr.commonFree :
    UpperTheory.V.Pr.CommonFree := by
  intro H A ι _ _ _ χ N hN htor hex
  classical
  let K : ι → Subgroup H := fun i => ((powMonoidHom N : A →* A).comp (χ i)).ker
  have hK : ∀ i h, h ∈ K i ↔ χ i h ^ N = 1 := fun i h => by
    simp [K, MonoidHom.mem_ker]
  by_contra hno
  push_neg at hno
  have _ : Fintype ι := Fintype.ofFinite ι
  have hcov : ⋃ i ∈ (Finset.univ : Finset ι), (fun _ => (1 : H)) i • ((K i : Set H)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro h
    obtain ⟨i, m, hm, h1⟩ := hno h
    simp only [one_smul, Set.mem_iUnion, Finset.mem_univ, exists_true_left, SetLike.mem_coe, exists_const]
    exact ⟨i, (hK i h).2 (htor i h m hm h1)⟩
  obtain ⟨i, -, hfin⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  obtain ⟨h, hh⟩ := hex i
  apply hh
  haveI : (K i).Normal := MonoidHom.normal_ker _
  have hmem := (K i).pow_index_mem h
  rw [hK, map_pow, ← pow_mul] at hmem
  exact htor i h _ (Nat.mul_pos (Nat.pos_of_ne_zero hfin.index_ne_zero) hN) hmem
