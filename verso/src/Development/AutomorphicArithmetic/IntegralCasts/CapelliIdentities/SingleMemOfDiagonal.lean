import Mathlib

/- English proof (translation)
Introduce `κ _ m d hd W hW v hv i hi`. Establish `key : ∀ s : Finset (Fin m), (fun k => (∏ j ∈ s, (d k - d j)) * v k) ∈ W`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hv`.

Consider the case `insert a s ha ih`. Establish `h` using `W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [Finset.prod_insert ha, Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0`. Use `mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) hi` and prove the remaining obligations. Conclude with `sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm`. Establish `h` using `W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹ (key (Finset.univ.erase i))`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]`.

Conclude with `(inv_mul_cancel₀ hc).symm`. Establish `h0 : (∏ j ∈ Finset.univ.erase i, (d k - d j)) = 0` using `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)`. Simplify using `only [Pi.single_eq_of_ne hk, Pi.smul_apply, smul_eq_mul, h0, zero_mul, mul_zero]`.
-/
theorem UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag :
    ∀ {κ : Type} [inst : Field κ] {m : ℕ} (d : Fin m → κ),
    Function.Injective d →
      ∀ (W : Submodule κ (Fin m → κ)),
        (∀ v ∈ W, (Matrix.diagonal d).mulVec v ∈ W) →
          ∀ v ∈ W, ∀ (i : Fin m), v i ≠ (0 : κ) → Pi.single i (1 : κ) ∈ W := by
  intro κ _ m d hd W hW v hv i hi
  have key : ∀ s : Finset (Fin m), (fun k => (∏ j ∈ s, (d k - d j)) * v k) ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hv
    | insert a s ha ih =>
      have h := W.sub_mem (hW _ ih) (W.smul_mem (d a) ih)
      convert h using 1
      funext k
      simp only [Finset.prod_insert ha, Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
        smul_eq_mul]
      ring
  have hc : (∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j hj => ?_) hi
    exact sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hd h).symm
  have h := W.smul_mem ((∏ j ∈ Finset.univ.erase i, (d i - d j)) * v i)⁻¹
    (key (Finset.univ.erase i))
  convert h using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    exact (inv_mul_cancel₀ hc).symm
  · have h0 : (∏ j ∈ Finset.univ.erase i, (d k - d j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp only [Pi.single_eq_of_ne hk, Pi.smul_apply, smul_eq_mul, h0, zero_mul, mul_zero]
