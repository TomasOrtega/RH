import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.PowerSeriesRelationList

namespace Formalism.NOK

/- English proof (translation)
Introduce `ℓ _ hℓ χ hχ ell g h a JJ hJJ hbd`. Take `⟨hne, hval⟩` from `Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ`. Use `⟨hne, ?_⟩` and prove the remaining obligations. Establish `hcard : (JJ.erase 0).card ≤ 20 * g`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `t _`. Rewrite using `[Int.card_Ico, add_sub_cancel_left]`. Use linear arithmetic over natural numbers and integers. Use `_ = 20 * g := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsumv : ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤ 5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ)))`. Establish `hle : (∑ i ∈ JJ.erase 0, padicValInt ℓ i) ≤ ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i hi`. Take `⟨t, -, ht⟩` from `Finset.mem_biUnion.mp (hJJ (Finset.mem_of_mem_erase hi))`. Combine the equalities or inequalities in the displayed calculation. Use `_ = ∑ t : Fin 5, ∑ i ∈ JJ.erase 0, (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) := Finset.sum_comm`.

Use `_ = ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i := by`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `t _`. Rewrite using `[Finset.sum_filter]`. Establish `hwin : ∀ t : Fin 5, ((∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) ≤ 4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))`.

Introduce `t`. Establish `hw` using `Formalism.WindowSums.arc_WindowSum ℓ (a t) (4 * g) (2 * h) ((JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)))) ?_ ?_ ?_`. Move the coercions through the operations in `at hw ⊢`. Conclude with `hw`. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_filter]`. Use `push_cast`. Conclude with `hi.2`. Introduce `h0`. Rewrite `h0` using `[Finset.mem_filter]`.

Conclude with `(Finset.mem_erase.mp h0.1).1 rfl`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_filter]`. Use `push_cast`. Conclude with `hbd i (Finset.mem_of_mem_erase hi.1)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hle` after adjusting the coercions. Use `_ = ∑ t : Fin 5, ((∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by`. Rewrite using `[Nat.cast_sum]`. Use `_ ≤ ∑ _t : Fin 5, (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := Finset.sum_le_sum (fun t _ => hwin t)`.

Use `_ = 5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Evaluate the numerical expressions. Establish `hsplit : (∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i)) = (JJ.erase 0).card * (1 + ell) + ∑ i ∈ JJ.erase 0, padicValInt ℓ i`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]`.

Establish `hc : (((JJ.erase 0).card * (1 + ell) : ℕ) : ℝ) ≤ 20 * (g : ℝ) * (1 + (ell : ℝ))`. Establish `h1 : (JJ.erase 0).card * (1 + ell) ≤ 20 * g * (1 + ell)` using `Nat.mul_le_mul_right _ hcard`. Conclude with `h1` after adjusting the coercions. Rewrite using `[hval, hsplit]`. Move the coercions through the operations in `at hc hsumv ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem kapBound_proof : KapBound := by
  intro ℓ _ hℓ χ hχ ell g h a JJ hJJ hbd
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩

  have hcard : (JJ.erase 0).card ≤ 20 * g := by
    calc (JJ.erase 0).card ≤ JJ.card := Finset.card_le_card (Finset.erase_subset _ _)
      _ ≤ (Finset.univ.biUnion (fun t : Fin 5 => Finset.Ico (a t) (a t + 4 * (g : ℤ)))).card :=
          Finset.card_le_card hJJ
      _ ≤ ∑ t : Fin 5, (Finset.Ico (a t) (a t + 4 * (g : ℤ))).card := Finset.card_biUnion_le
      _ = ∑ t : Fin 5, 4 * g := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Int.card_Ico, add_sub_cancel_left]
          omega
      _ = 20 * g := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring

  have hsumv : ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤
      5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
    have hle : (∑ i ∈ JJ.erase 0, padicValInt ℓ i) ≤
        ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
          padicValInt ℓ i := by
      calc (∑ i ∈ JJ.erase 0, padicValInt ℓ i)
          ≤ ∑ i ∈ JJ.erase 0, ∑ t : Fin 5,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (hJJ (Finset.mem_of_mem_erase hi))
            calc padicValInt ℓ i
                = (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  (if_pos ht).symm
              _ ≤ ∑ t' : Fin 5,
                    (if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  Finset.single_le_sum
                    (f := fun t' => if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0)
                    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
        _ = ∑ t : Fin 5, ∑ i ∈ JJ.erase 0,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
            Finset.sum_comm
        _ = ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
              padicValInt ℓ i := by
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_filter]
    have hwin : ∀ t : Fin 5,
        ((∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
            padicValInt ℓ i : ℕ) : ℝ) ≤ 4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ)) := by
      intro t
      have hw := Formalism.WindowSums.arc_WindowSum ℓ (a t) (4 * g) (2 * h)
        ((JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)))) ?_ ?_ ?_
      · push_cast at hw ⊢
        exact hw
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hi.2
      · intro h0
        rw [Finset.mem_filter] at h0
        exact (Finset.mem_erase.mp h0.1).1 rfl
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hbd i (Finset.mem_of_mem_erase hi.1)
    calc ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ t : Fin 5, ((∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ ∑ _t : Fin 5, (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) :=
          Finset.sum_le_sum (fun t _ => hwin t)
      _ = 5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hsplit : (∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i)) =
      (JJ.erase 0).card * (1 + ell) + ∑ i ∈ JJ.erase 0, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hc : (((JJ.erase 0).card * (1 + ell) : ℕ) : ℝ) ≤ 20 * (g : ℝ) * (1 + (ell : ℝ)) := by
    have h1 : (JJ.erase 0).card * (1 + ell) ≤ 20 * g * (1 + ell) := Nat.mul_le_mul_right _ hcard
    exact_mod_cast h1
  rw [hval, hsplit]
  push_cast at hc hsumv ⊢
  linarith

end Formalism.NOK
