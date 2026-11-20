import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

/- English proof (translation)
Introduce `l _ ι S c hc h b hb`. Assume the negation of the conclusion as `hlt`. Establish `hlt' : c < ‖ι.symm b‖` using `not_le.mp hlt`. Establish `hroot : Polynomial.eval b (S.map fun t => Polynomial.X - Polynomial.C t).prod = 0`. Rewrite using `[Polynomial.eval_multiset_prod]`.

Apply `Multiset.prod_eq_zero` to reduce the goal to its premises. Rewrite using `[Multiset.mem_map]`. Use `⟨Polynomial.X - Polynomial.C b, Multiset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩` and prove the remaining obligations. Rewrite `hroot` using `[Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finset_sum, Finset.sum_range_succ']`. Establish `hn : 0 < S.card` using `Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩`.

Establish `h0 : S.esymm 0 = 1` using `by simp [Multiset.esymm]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero, h0] at hroot`. Establish `hK` using `congrArg ι.symm hroot`. Simplify using `only [map_add, map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hK`. Establish `heq : ‖ι.symm b‖ ^ S.card = ‖∑ j ∈ Finset.range S.card, (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1)))‖`.

Rewrite using `[eq_neg_of_add_eq_zero_left hK, norm_neg, norm_pow]`. Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne') (fun j => (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1))))`. Establish `hi' : i + 1 ≤ S.card` using `Finset.mem_range.mp hi`. Establish `hj` using `h (i + 1) (by omega) hi'`. Establish `hj' : ‖ι.symm (S.esymm (i + 1))‖ ≤ c ^ (i + 1)` using `hj`.

Establish `hpos : 0 < ‖ι.symm b‖` using `lt_of_le_of_lt hc hlt'`. Establish `hcp : c ^ (i + 1) < ‖ι.symm b‖ ^ (i + 1)` using `pow_lt_pow_left₀ hlt' hc (by omega)`. Establish `hterm : ‖(-1 : PadicAlgCl l) ^ (i + 1) * (ι.symm (S.esymm (i + 1)) * ι.symm b ^ (S.card - (i + 1)))‖ < ‖ι.symm b‖ ^ S.card`. Rewrite using `[norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `absurd (heq.le.trans hle) (not_le.mpr hterm)`.
-/
theorem UpperTheory.V.Z.Int.rootBound :
    UpperTheory.V.Z.Int.RootBound := by
  intro l _ ι S c hc h b hb
  by_contra hlt
  have hlt' : c < ‖ι.symm b‖ := not_le.mp hlt
  have hroot : Polynomial.eval b (S.map fun t => Polynomial.X - Polynomial.C t).prod = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    refine ⟨Polynomial.X - Polynomial.C b, Multiset.mem_map.mpr ⟨b, hb, rfl⟩, by simp⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, Polynomial.eval_finset_sum, Finset.sum_range_succ'] at hroot
  have hn : 0 < S.card := Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
  have h0 : S.esymm 0 = 1 := by simp [Multiset.esymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero, h0] at hroot
  have hK := congrArg ι.symm hroot
  simp only [map_add, map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hK
  have heq : ‖ι.symm b‖ ^ S.card = ‖∑ j ∈ Finset.range S.card, (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1)))‖ := by
    rw [eq_neg_of_add_eq_zero_left hK, norm_neg, norm_pow]
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hn.ne')
    (fun j => (-1 : PadicAlgCl l) ^ (j + 1) * (ι.symm (S.esymm (j + 1)) * ι.symm b ^ (S.card - (j + 1))))
  have hi' : i + 1 ≤ S.card := Finset.mem_range.mp hi
  have hj := h (i + 1) (by omega) hi'
  have hj' : ‖ι.symm (S.esymm (i + 1))‖ ≤ c ^ (i + 1) := hj
  have hpos : 0 < ‖ι.symm b‖ := lt_of_le_of_lt hc hlt'
  have hcp : c ^ (i + 1) < ‖ι.symm b‖ ^ (i + 1) := pow_lt_pow_left₀ hlt' hc (by omega)
  have hterm : ‖(-1 : PadicAlgCl l) ^ (i + 1) * (ι.symm (S.esymm (i + 1)) * ι.symm b ^ (S.card - (i + 1)))‖
      < ‖ι.symm b‖ ^ S.card := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow]
    calc ‖ι.symm (S.esymm (i + 1))‖ * ‖ι.symm b‖ ^ (S.card - (i + 1))
        < ‖ι.symm b‖ ^ (i + 1) * ‖ι.symm b‖ ^ (S.card - (i + 1)) :=
          mul_lt_mul_of_pos_right (lt_of_le_of_lt hj' hcp) (pow_pos hpos _)
      _ = ‖ι.symm b‖ ^ S.card := by rw [← pow_add]; congr 1; omega
  exact absurd (heq.le.trans hle) (not_le.mpr hterm)
