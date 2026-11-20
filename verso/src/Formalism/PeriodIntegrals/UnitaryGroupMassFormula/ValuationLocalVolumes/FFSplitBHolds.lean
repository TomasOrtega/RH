import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DcountSplit

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

/- English proof (translation)
Introduce `k _ _ M a haM J hJ hJdet T hT hcor`. Take `⟨i₀, hrow, hcol, hunit⟩` from `hcor`. Consider the cases of `a with`. Consider the case `zero => exact i₀.elim0`. Consider the case `succ a'`.

Establish `hσ : ∀ x : k × k, RingEquiv.prodComm.toRingHom x = x.swap` using `fun x => rfl`. Establish `hsub : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det`. Use `PI.OmVe.det_corOne T i₀ hrow 1` as an intermediate fact. Rewrite `hunit` using `[this, one_mul]`. Conclude with `hunit`.

Establish `hinv : ∀ x : k × k, RingEquiv.prodComm.toRingHom (RingEquiv.prodComm.toRingHom x) = x` using `fun x => by simp [hσ]`. Establish `hJ' : ∀ i j, RingEquiv.prodComm.toRingHom (J j i) = J i j` using `fun i j => by rw [hσ]; exact hJ i j`. Establish `hdiag : ∀ x : Fin M → k × k, ∃ c : k, PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x = (c, c)`. Introduce `x`. Establish `h` using `PI.OmVe.ffH_herm RingEquiv.prodComm.toRingHom J hinv hJ' x x`.

Use `⟨(PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x).1, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hσ]`. Use `ext`. Both sides reduce to the same expression. Conclude with `(congrArg Prod.fst h).symm.trans rfl`.

Establish `hTs : ∀ i j, ((T.submatrix i₀.succAbove i₀.succAbove) j i).swap = (T.submatrix i₀.succAbove i₀.succAbove) i j` using `fun i j => hT _ _`. Establish `hY` using `PI.VolStabSW.fFSplit_holds k M a' (by omega) J hJ hJdet _ hTs hsub`. Establish `hNr : ∀ c : k, c ≠ 0 → (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ (c, c) } : ℝ) = (∏ i : Fin (a' + 1), ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) * (Nat.card k : ℝ) ^ ((a' + 1) * (M - (a …`. Introduce `c hc`. Establish `hdet : IsUnit (T + Matrix.single i₀ i₀ (c, c)).det`.

Rewrite using `[PI.OmVe.det_corOne T i₀ hrow]`. Use `IsUnit.mul ?_ hsub` and prove the remaining obligations. Conclude with `(Prod.isUnit_iff).2 ⟨isUnit_iff_ne_zero.2 hc, isUnit_iff_ne_zero.2 hc⟩`. Establish `hh : ∀ i j, ((T + Matrix.single i₀ i₀ (c, c)) j i).swap = (T + Matrix.single i₀ i₀ (c, c)) i j`. Introduce `i j`.

Rewrite using `[Matrix.add_apply, Matrix.add_apply, ← hT i j, Matrix.single_apply, Matrix.single_apply]`. Apply the tactic sequence `by_cases h1 : i₀ = i <;> by_cases h2 : i₀ = j <;> ext <;> simp [h1, h2] <;> split_ifs <;> rfl`. Conclude with `PI.VolStabSW.fFSplit_holds k M (a' + 1) haM J hJ hJdet _ hh hdet`. Establish `key` using `PI.OmVe.count_gen RingEquiv.prodComm.toRingHom J hinv hJ' T i₀ hrow hcol hunit (by omega) (k := k) (fun c => (c, c)) (fun c d h => by simpa using congrArg Prod.fst h) rfl`. Specialize `key hdiag`.

Use `clear hinv hJ' hdiag hσ`. Establish `hk1 : 1 ≤ Nat.card k` using `Nat.card_pos`. Establish `hk` using `key (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ ((1 : k), (1 : k)) }) (2 * Nat.card k ^ (M - a') - 1) (fun c hc => Nat.cast_injective (R := ℝ) ((hNr c hc).trans (hNr 1 one_ne_zero).symm)) (fun Y hY …`. Use `PI.OmVe.dcount_split J (by omega) _ hsub Y hY'` as an intermediate fact. Establish `: 1 ≤ Nat.card k ^ (M - a')` using `Nat.one_le_pow _ _ hk1`.

Use the proof step `omega)`. Establish `hN1` using `hNr 1 one_ne_zero`. Use `clear key hNr`. Rewrite `hk` using `[Nat.card_prod]`. Establish `hkR` using `congrArg (fun n : ℕ => (n : ℝ)) hk`.

Simplify using `only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk1, Nat.cast_one] at hkR`. Rewrite `hkR` using `[Nat.cast_sub (by have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1; omega)]`. Rewrite `hkR` using `[hY, hN1]`. Move the coercions through the operations in `at hkR`. Establish `hq : (1 : ℝ) ≤ Nat.card k` using `by exact_mod_cast hk1`.

Generalize the expression as in `((Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T ∧ LinearIndependent (k × k) X } : ℕ) : ℝ) = C at hkR ⊢`. Generalize the expression as in `(Nat.card k : ℝ) = q at hkR hq ⊢`. Use `clear hk hY hN1 hTs hsub hunit hrow hcol hT hJdet hJ`. Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_le haM`. Use `clear haM T J i₀`.

Establish `hq0 : q ≠ 0` using `by positivity`. Establish `e1 : a' + 1 + r - a' = r + 1` using `by omega`. Establish `e2 : a' + 1 + r - (a' + 1) = r` using `by omega`. Establish `e3 : 2 * (a' + 1 + r) * (a' + 1) - (a' + 1) ^ 2 = (a' + 1) ^ 2 + 2 * r * (a' + 1)` using `Nat.sub_eq_of_eq_add (by ring)`. Establish `hP` using `PI.OmVe.prodSplit_closed q hq0 (a' + 1 + r) a' (by omega)`.

Rewrite `hP`, `hkR` using `[e1]`. Rewrite `hkR` using `[e2]`. Rewrite using `[e2, e3]`. Simplify using `only [one_pow, one_mul]`. Rewrite using `[← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r ≤ a' + 1 + r), Finset.prod_insert (by simp), ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r + 1 ≤ a' + 1 + r), Finset.prod_insert (by simp)]`.

Rewrite `hkR` using `[Fin.prod_univ_castSucc]`. Simplify using `only [Fin.coe_castSucc, Fin.val_last] at hkR`. Rewrite `hkR` using `[hP]`. Establish `hK` using `PI.OmVe.keySplit q hq0 r`. Establish `e : q ^ (2 * r + 1) * (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = (q ^ (r + 1) - 1) * q ^ r`.

Rewrite using `[_root_.zpow_neg, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Generalize the expression as in `(∏ j ∈ Finset.Icc (r + 1 + 1) (a' + 1 + r), (1 - q ^ (-(j : ℤ)))) = Pi' at hkR ⊢`. Generalize the expression as in `(1 - q ^ (-((r + 1 : ℕ) : ℤ))) = B at hK e ⊢`.

Generalize the expression as in `(1 - q ^ (-(r : ℤ))) = A at hK ⊢`. Take the linear combination `hkR + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1))) * hK + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1)) * (q - 1)) * e`.
-/
theorem fFSplitB_holds : PI.OmVd.FFSplitB := by
  intro k _ _ M a haM J hJ hJdet T hT hcor
  obtain ⟨i₀, hrow, hcol, hunit⟩ := hcor
  cases a with
  | zero => exact i₀.elim0
  | succ a' =>
    have hσ : ∀ x : k × k, RingEquiv.prodComm.toRingHom x = x.swap := fun x => rfl
    have hsub : IsUnit (T.submatrix i₀.succAbove i₀.succAbove).det := by
      have := PI.OmVe.det_corOne T i₀ hrow 1
      rw [this, one_mul] at hunit
      exact hunit
    have hinv : ∀ x : k × k, RingEquiv.prodComm.toRingHom (RingEquiv.prodComm.toRingHom x) = x := fun x => by simp [hσ]
    have hJ' : ∀ i j, RingEquiv.prodComm.toRingHom (J j i) = J i j := fun i j => by rw [hσ]; exact hJ i j
    have hdiag : ∀ x : Fin M → k × k, ∃ c : k, PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x = (c, c) := by
      intro x
      have h := PI.OmVe.ffH_herm RingEquiv.prodComm.toRingHom J hinv hJ' x x
      refine ⟨(PI.VolStabSW.ffH RingEquiv.prodComm.toRingHom J x x).1, ?_⟩
      rw [hσ] at h
      ext
      · rfl
      · exact (congrArg Prod.fst h).symm.trans rfl
    have hTs : ∀ i j, ((T.submatrix i₀.succAbove i₀.succAbove) j i).swap = (T.submatrix i₀.succAbove i₀.succAbove) i j := fun i j => hT _ _
    have hY := PI.VolStabSW.fFSplit_holds k M a' (by omega) J hJ hJdet _ hTs hsub
    have hNr : ∀ c : k, c ≠ 0 → (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ (c, c) } : ℝ) = (∏ i : Fin (a' + 1), ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) * (Nat.card k : ℝ) ^ ((a' + 1) * (M - (a' + 1))) := by
      intro c hc
      have hdet : IsUnit (T + Matrix.single i₀ i₀ (c, c)).det := by
        rw [PI.OmVe.det_corOne T i₀ hrow]
        refine IsUnit.mul ?_ hsub
        exact (Prod.isUnit_iff).2 ⟨isUnit_iff_ne_zero.2 hc, isUnit_iff_ne_zero.2 hc⟩
      have hh : ∀ i j, ((T + Matrix.single i₀ i₀ (c, c)) j i).swap = (T + Matrix.single i₀ i₀ (c, c)) i j := by
        intro i j
        rw [Matrix.add_apply, Matrix.add_apply, ← hT i j, Matrix.single_apply, Matrix.single_apply]
        by_cases h1 : i₀ = i <;> by_cases h2 : i₀ = j <;> ext <;> simp [h1, h2] <;> split_ifs <;> rfl
      exact PI.VolStabSW.fFSplit_holds k M (a' + 1) haM J hJ hJdet _ hh hdet
    have key := PI.OmVe.count_gen RingEquiv.prodComm.toRingHom J hinv hJ' T i₀ hrow hcol hunit (by omega) (k := k) (fun c => (c, c)) (fun c d h => by simpa using congrArg Prod.fst h) rfl
    specialize key hdiag
    clear hinv hJ' hdiag hσ
    have hk1 : 1 ≤ Nat.card k := Nat.card_pos
    have hk := key (Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T + Matrix.single i₀ i₀ ((1 : k), (1 : k)) }) (2 * Nat.card k ^ (M - a') - 1)
      (fun c hc => Nat.cast_injective (R := ℝ) ((hNr c hc).trans (hNr 1 one_ne_zero).symm))
      (fun Y hY' => by
        have := PI.OmVe.dcount_split J (by omega) _ hsub Y hY'
        have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1
        omega)
    have hN1 := hNr 1 one_ne_zero
    clear key hNr
    rw [Nat.card_prod] at hk
    have hkR := congrArg (fun n : ℕ => (n : ℝ)) hk
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk1, Nat.cast_one] at hkR
    rw [Nat.cast_sub (by have : 1 ≤ Nat.card k ^ (M - a') := Nat.one_le_pow _ _ hk1; omega)] at hkR
    rw [hY, hN1] at hkR
    push_cast at hkR
    have hq : (1 : ℝ) ≤ Nat.card k := by exact_mod_cast hk1
    generalize ((Nat.card { X : Fin (a' + 1) → Fin M → k × k // PI.VolStabSW.ffGram RingEquiv.prodComm.toRingHom J X = T ∧ LinearIndependent (k × k) X } : ℕ) : ℝ) = C at hkR ⊢
    generalize (Nat.card k : ℝ) = q at hkR hq ⊢
    clear hk hY hN1 hTs hsub hunit hrow hcol hT hJdet hJ
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le haM
    clear haM T J i₀
    have hq0 : q ≠ 0 := by positivity
    have e1 : a' + 1 + r - a' = r + 1 := by omega
    have e2 : a' + 1 + r - (a' + 1) = r := by omega
    have e3 : 2 * (a' + 1 + r) * (a' + 1) - (a' + 1) ^ 2 = (a' + 1) ^ 2 + 2 * r * (a' + 1) := Nat.sub_eq_of_eq_add (by ring)
    have hP := PI.OmVe.prodSplit_closed q hq0 (a' + 1 + r) a' (by omega)
    rw [e1] at hP hkR
    rw [e2] at hkR
    rw [e2, e3]
    simp only [one_pow, one_mul]
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r ≤ a' + 1 + r), Finset.prod_insert (by simp), ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : r + 1 ≤ a' + 1 + r), Finset.prod_insert (by simp)]
    rw [Fin.prod_univ_castSucc] at hkR
    simp only [Fin.coe_castSucc, Fin.val_last] at hkR
    rw [hP] at hkR
    have hK := PI.OmVe.keySplit q hq0 r
    have e : q ^ (2 * r + 1) * (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = (q ^ (r + 1) - 1) * q ^ r := by
      rw [_root_.zpow_neg, zpow_natCast]
      field_simp
      ring
    generalize (∏ j ∈ Finset.Icc (r + 1 + 1) (a' + 1 + r), (1 - q ^ (-(j : ℤ)))) = Pi' at hkR ⊢
    generalize (1 - q ^ (-((r + 1 : ℕ) : ℤ))) = B at hK e ⊢
    generalize (1 - q ^ (-(r : ℤ))) = A at hK ⊢
    linear_combination hkR + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1))) * hK + (Pi' * q ^ ((a' + 1 + r) * a') * q ^ (a' * (r + 1)) * (q - 1)) * e

end PI.OmVe
