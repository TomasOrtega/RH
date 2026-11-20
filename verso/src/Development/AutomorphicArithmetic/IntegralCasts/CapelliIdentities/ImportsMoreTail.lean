import Mathlib

/- English proof (translation)
Introduce `F _ _ m t ht E hE hdet`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hv`. Use `haveI : Nonempty (Fin m) := ⟨i⟩`. Take `⟨a, ha⟩` from `Finite.exists_max (fun j => ‖v j‖)`.

Establish `hpos : 0 < ‖v a‖` using `lt_of_lt_of_le (norm_pos_iff.mpr hi) (ha i)`. Establish `hrow : t * v a = -∑ b, E a b * v b`. Establish `h` using `congrFun hMv a`. Rewrite `h` using `[Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]`. Conclude with `eq_neg_of_add_eq_zero_left h`.

Take `⟨b, -, hb⟩` from `IsUltrametricDist.exists_norm_finset_sum_le (Finset.univ : Finset (Fin m)) (fun b => E a b * v b)`. Establish `h1 : ‖v a‖ = ‖∑ b, E a b * v b‖`. Rewrite using `[← norm_neg (∑ b, E a b * v b), ← hrow, norm_mul, ht, one_mul]`. Establish `h2 : ‖E a b * v b‖ < ‖v a‖`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd (h1.le.trans hb) (not_le.mpr h2)`.
-/
theorem UpperTheory.Reformulated.B.Qi6.det_ne_zero :
    ∀ {F : Type} [inst : NormedField F] [IsUltrametricDist F] {m : ℕ}
    (t : F),
    ‖t‖ = (1 : ℝ) →
      ∀ (E : Matrix (Fin m) (Fin m) F),
        (∀ (a b : Fin m), ‖E a b‖ < (1 : ℝ)) → (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ (0 : F) := by
  intro F _ _ m t ht E hE hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  haveI : Nonempty (Fin m) := ⟨i⟩
  obtain ⟨a, ha⟩ := Finite.exists_max (fun j => ‖v j‖)
  have hpos : 0 < ‖v a‖ := lt_of_lt_of_le (norm_pos_iff.mpr hi) (ha i)
  have hrow : t * v a = -∑ b, E a b * v b := by
    have h := congrFun hMv a
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact eq_neg_of_add_eq_zero_left h
  obtain ⟨b, -, hb⟩ := IsUltrametricDist.exists_norm_finset_sum_le (Finset.univ : Finset (Fin m))
    (fun b => E a b * v b)
  have h1 : ‖v a‖ = ‖∑ b, E a b * v b‖ := by
    rw [← norm_neg (∑ b, E a b * v b), ← hrow, norm_mul, ht, one_mul]
  have h2 : ‖E a b * v b‖ < ‖v a‖ := by
    rw [norm_mul]
    calc ‖E a b‖ * ‖v b‖ ≤ ‖E a b‖ * ‖v a‖ :=
          mul_le_mul_of_nonneg_left (ha b) (norm_nonneg _)
      _ < 1 * ‖v a‖ := mul_lt_mul_of_pos_right (hE a b) hpos
      _ = ‖v a‖ := one_mul _
  exact absurd (h1.le.trans hb) (not_le.mpr h2)
