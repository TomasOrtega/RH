import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.GroupTheory.CosetCover

open scoped Pointwise in
/- English proof (translation)
Introduce `H A ι _ _ _ χ N hN htor hex`. Set `K : ι → Subgroup H` to `fun i => ((powMonoidHom N : A →* A).comp (χ i)).ker`. Establish `hK : ∀ i h, h ∈ K i ↔ χ i h ^ N = 1` using `fun i h => by`. Simplify using `[K, MonoidHom.mem_ker]`. Assume the negation of the conclusion as `hno`.

Use `push_neg at hno`. Establish `_ : Fintype ι` using `Fintype.ofFinite ι`. Establish `hcov : ⋃ i ∈ (Finset.univ : Finset ι), (fun _ => (1 : H)) i • ((K i : Set H)) = Set.univ`. Apply `Set.eq_univ_of_forall` to reduce the goal to its premises. Introduce `h`.

Take `⟨i, m, hm, h1⟩` from `hno h`. Simplify using `only [one_smul, Set.mem_iUnion, Finset.mem_univ, exists_true_left, SetLike.mem_coe, exists_const]`. Conclude with `⟨i, (hK i h).2 (htor i h m hm h1)⟩`. Take `⟨i, -, hfin⟩` from `Subgroup.exists_finiteIndex_of_leftCoset_cover hcov`. Take `⟨h, hh⟩` from `hex i`.

Apply `hh` to reduce the goal to its premises. Use `haveI : (K i).Normal := MonoidHom.normal_ker _`. Establish `hmem` using `(K i).pow_index_mem h`. Rewrite `hmem` using `[hK, map_pow, ← pow_mul]`. Conclude with `htor i h _ (Nat.mul_pos (Nat.pos_of_ne_zero hfin.index_ne_zero) hN) hmem`.
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
