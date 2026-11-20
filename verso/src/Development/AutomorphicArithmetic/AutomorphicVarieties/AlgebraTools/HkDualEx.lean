import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hw` to reduce the goal to its premises. Establish `hs : ∑ i, (w i).val = ∑ i : Fin n, i.val` using `Equiv.sum_comp w (fun i => i.val)`. Establish `hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (w i).val ≤ i.val` using `fun i _ => h i`.

Establish `heq` using `(Finset.sum_eq_sum_iff_of_le hle).mp hs`. Conclude with `Equiv.ext fun i => Fin.ext (by simpa using heq i (Finset.mem_univ _))`.
-/
private theorem exists_lt_apply {n : ℕ} (w : Perm (Fin n)) (hw : w ≠ 1) : ∃ i, i < w i := by
  by_contra h
  push_neg at h
  apply hw
  have hs : ∑ i, (w i).val = ∑ i : Fin n, i.val := Equiv.sum_comp w (fun i => i.val)
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (w i).val ≤ i.val := fun i _ => h i
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  exact Equiv.ext fun i => Fin.ext (by simpa using heq i (Finset.mem_univ _))

/- English proof (translation)
Introduce `R _ n`. Use `⟨Finset (Fin n × Fin n), inferInstance, fun t => if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0, fun t => ∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R), ?_⟩` and prove the remaining obligations. Introduce `w`. Establish `hsum : ∑ t : Finset (Fin n × Fin n), (if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0) * rename w (∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R)) = ∏ p ∈ pairs n, ((X p.2 : MvPolynomial (Fin n) R) + -X (w p.1))`. Simplify using `only [ite_mul, zero_mul]`.

Rewrite using `[← Finset.sum_filter]`. Establish `hf : Finset.univ.filter (fun t : Finset (Fin n × Fin n) => t ⊆ pairs n) = (pairs n).powerset`. Use extensionality with `t`. Simplify using the standard rewrite rules. Rewrite using `[hf, Finset.prod_add]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `[map_prod, rename_X]`. Use `hsum.trans ?_` and prove the remaining obligations. Use `split_ifs with h1`. Substitute `h1` using the available equality.

Rewrite using `[De]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `[sub_eq_add_neg]`. Take `⟨i, hi⟩` from `exists_lt_apply w h1`. Apply `Finset.prod_eq_zero (i := (i, w i))` to reduce the goal to its premises.

Simplify using `[pairs, hi]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.AlgebraTools.hkDualEx :
    ∀ (R : Type) [CommRing R] (n : ℕ), ∃ (ι : Type) (_ : Fintype ι) (a b : ι → MvPolynomial (Fin n) R), IsDual a b := by
  intro R _ n
  refine ⟨Finset (Fin n × Fin n), inferInstance,
    fun t => if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0,
    fun t => ∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R), ?_⟩
  intro w
  have hsum : ∑ t : Finset (Fin n × Fin n), (if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0) *
      rename w (∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R)) =
      ∏ p ∈ pairs n, ((X p.2 : MvPolynomial (Fin n) R) + -X (w p.1)) := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun t : Finset (Fin n × Fin n) => t ⊆ pairs n) = (pairs n).powerset := by
      ext t
      simp
    rw [hf, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [map_prod, rename_X]
  refine hsum.trans ?_
  split_ifs with h1
  · subst h1
    rw [De]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [sub_eq_add_neg]
  · obtain ⟨i, hi⟩ := exists_lt_apply w h1
    apply Finset.prod_eq_zero (i := (i, w i))
    · simp [pairs, hi]
    · simp
