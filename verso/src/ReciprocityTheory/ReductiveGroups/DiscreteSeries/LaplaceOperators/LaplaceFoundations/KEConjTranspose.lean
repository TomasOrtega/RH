import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def kE (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j => if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def fI (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨q.val, by omega⟩

/- English proof (translation)
Introduce `a b h`. Simplify using `[fI, Fin.ext_iff] at h`. Conclude with `Fin.ext h`.
-/
theorem fI_inj : Function.Injective (fI k r) := by
  intro a b h; simp [fI, Fin.ext_iff] at h; exact Fin.ext h

/- English proof (translation)
Use `symm`. Use `Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `p hp`. Apply `hf` to reduce the goal to its premises. Introduce `hlt`.

Conclude with `hp ⟨⟨p.val, hlt⟩, rfl⟩`.
-/
theorem sumF (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p : Fin (2 * r + k + 1), ¬ p.val < k → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (fI k r q) := by
  symm
  refine Fintype.sum_of_injective (fI k r) fI_inj _ _ ?_ (fun _ => rfl)
  intro p hp
  apply hf
  intro hlt
  exact hp ⟨⟨p.val, hlt⟩, rfl⟩

/- English proof (translation)
Simplify using `[kE, fI]`.
-/
theorem kE_ff (h : Matrix (Fin k) (Fin k) ℂ) (q q' : Fin k) : kE k r h (fI k r q) (fI k r q') = h q q' := by
  simp [kE, fI]

/- English proof (translation)
Simplify using `[kE, hi]`.
-/
theorem kE_row (h : Matrix (Fin k) (Fin k) ℂ) {i : Fin (2 * r + k + 1)} (j : Fin (2 * r + k + 1))
    (hi : ¬ i.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  simp [kE, hi]

/- English proof (translation)
Distinguish the cases in `hi : i.val < k`. Establish `hne : i ≠ j` using `by rintro rfl; exact hj hi`. Simplify using `[kE, hi, hj, hne]`. Simplify using `[kE, hi]`.
-/
theorem kE_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ j.val < k) : kE k r h i j = if i = j then 1 else 0 := by
  by_cases hi : i.val < k
  · have hne : i ≠ j := by rintro rfl; exact hj hi
    simp [kE, hi, hj, hne]
  · simp [kE, hi]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨i.val, hi⟩, by ext; simp [fI]⟩`.
-/
theorem ex_fI {i : Fin (2 * r + k + 1)} (hi : i.val < k) : ∃ q, i = fI k r q :=
  ⟨⟨i.val, hi⟩, by ext; simp [fI]⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : i.val < k`. Take `⟨qi, rfl⟩` from `ex_fI hi`. Rewrite using `[sumF _ (fun p hp => by rw [kE_col a _ hp, if_neg (by rintro rfl; exact hp hi), zero_mul])]`.

Distinguish the cases in `hj : j.val < k`. Take `⟨qj, rfl⟩` from `ex_fI hj`. Simplify using `only [kE_ff, Matrix.mul_apply]`. Rewrite using `[kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]`. Use `(Finset.sum_eq_zero fun q _ => ?_).symm` and prove the remaining obligations.

Rewrite using `[kE_col b _ hj, if_neg (by intro h; apply hj; rw [← h]; exact q.2), mul_zero]`. Rewrite using `[kE_row _ j hi]`. Rewrite using `[Finset.sum_eq_single i (fun p _ hp => by rw [kE_row a p hi, if_neg (Ne.symm hp), zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]`. Rewrite using `[kE_row a i hi, if_pos rfl, one_mul, kE_row b j hi]`.
-/
theorem kE_mul (a b : Matrix (Fin k) (Fin k) ℂ) : kE k r (a * b) = kE k r a * kE k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < k
  · obtain ⟨qi, rfl⟩ := ex_fI hi
    rw [sumF _ (fun p hp => by rw [kE_col a _ hp, if_neg (by rintro rfl; exact hp hi), zero_mul])]
    by_cases hj : j.val < k
    · obtain ⟨qj, rfl⟩ := ex_fI hj
      simp only [kE_ff, Matrix.mul_apply]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]
      refine (Finset.sum_eq_zero fun q _ => ?_).symm
      rw [kE_col b _ hj, if_neg (by intro h; apply hj; rw [← h]; exact q.2), mul_zero]
  · rw [kE_row _ j hi]
    rw [Finset.sum_eq_single i (fun p _ hp => by rw [kE_row a p hi, if_neg (Ne.symm hp), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [kE_row a i hi, if_pos rfl, one_mul, kE_row b j hi]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hi : i.val < k`. Distinguish the cases in `hj : j.val < k`. Simplify using `only [kE, dif_pos hi, dif_pos hj, Matrix.one_apply, Fin.ext_iff]`. Rewrite using `[kE_col _ _ hj, Matrix.one_apply]`.

Rewrite using `[kE_row _ _ hi, Matrix.one_apply]`.
-/
theorem kE_one : kE k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dif_pos hi, dif_pos hj, Matrix.one_apply, Fin.ext_iff]
    · rw [kE_col _ _ hj, Matrix.one_apply]
  · rw [kE_row _ _ hi, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply]`. Distinguish the cases in `hi : i.val < k`. Distinguish the cases in `hj : j.val < k`. Simplify using `only [kE, dif_pos hi, dif_pos hj, Matrix.conjTranspose_apply]`.

Rewrite using `[kE_row _ _ hj, kE_col _ _ hj]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm hij), if_neg hij, star_zero]`.

Rewrite using `[kE_col _ _ hi, kE_row _ _ hi]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm hij), if_neg hij, star_zero]`.
-/
theorem kE_conjTranspose (h : Matrix (Fin k) (Fin k) ℂ) : (kE k r h)ᴴ = kE k r hᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dif_pos hi, dif_pos hj, Matrix.conjTranspose_apply]
    · rw [kE_row _ _ hj, kE_col _ _ hj]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]
  · rw [kE_col _ _ hi, kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, star_zero]

variable {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

/- English proof (translation)
Establish `h` using `congrFun (hW q) l`. Establish `e : Formalism.QuantumDeterminants.wI k r q.castSucc = StandardBasisEmbedding.eB k r q` using `rfl`. Rewrite `h` using `[e]`. Simplify using `only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Rewrite using `[h]`.

Both sides reduce to the same expression.
-/
theorem cay_col (hW : WCols k r P) (q : Fin k) (l : Fin (2 * r + k + 1)) :
    P l (StandardBasisEmbedding.eB k r q) = if l = fI k r q then 1 else 0 := by
  have h := congrFun (hW q) l
  have e : Formalism.QuantumDeterminants.wI k r q.castSucc = StandardBasisEmbedding.eB k r q := rfl
  rw [e] at h
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [h]
  rfl

/- English proof (translation)
Rewrite using `[← hP.2, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, cay_col hW, Formalism.REAL.Jm, Matrix.diagonal_apply]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single (fI k r q) (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem cay_entry (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) (j : Fin (2 * r + k + 1)) :
    Hpk k r (StandardBasisEmbedding.eB k r q) j = (if ε (fI k r q) then 1 else -1) * P (fI k r q) j := by
  rw [← hP.2, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cay_col hW, Formalism.REAL.Jm, Matrix.diagonal_apply]
  simp
  rw [Finset.sum_eq_single (fI k r q) (fun b _ hb => by simp [hb]) (by simp)]
  simp

/- English proof (translation)
Apply the tactic sequence `have h := cay_entry hP hW ⟨a.val, ha⟩ (StandardBasisEmbedding.eB k r ⟨a.val, ha⟩)`. Rewrite `h` using `[StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_pos rfl, cay_col hW, if_pos rfl, mul_one]`. Establish `e : fI k r ⟨a.val, ha⟩ = a` using `Fin.ext rfl`. Rewrite `h` using `[e]`. Assume the negation of the conclusion as `hne`.

Rewrite `h` using `[if_neg hne]`. Evaluate the numerical expressions using `at h`.
-/
theorem cay_eps (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (a : Fin (2 * r + k + 1))
    (ha : a.val < k) : ε a = true := by
  have h := cay_entry hP hW ⟨a.val, ha⟩ (StandardBasisEmbedding.eB k r ⟨a.val, ha⟩)
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_pos rfl, cay_col hW, if_pos rfl, mul_one] at h
  have e : fI k r ⟨a.val, ha⟩ = a := Fin.ext rfl
  rw [e] at h
  by_contra hne
  rw [if_neg hne] at h
  norm_num at h

/- English proof (translation)
Apply the tactic sequence `have h := cay_entry hP hW q j`. Rewrite `h` using `[StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_neg (by rintro rfl; exact hj (StandardBasisEmbedding.bl_eB q))]`. Apply the tactic sequence `have hne : (if ε (fI k r q) then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Conclude with `(mul_eq_zero.1 h.symm).resolve_left hne`.
-/
theorem cay_zero (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (q : Fin k) {j : Fin (2 * r + k + 1)}
    (hj : ¬ StandardBasisEmbedding.bl k r j) : P (fI k r q) j = 0 := by
  have h := cay_entry hP hW q j
  rw [StandardBasisEmbedding.H_blrow (StandardBasisEmbedding.bl_eB _), if_neg (by rintro rfl; exact hj (StandardBasisEmbedding.bl_eB q))] at h
  have hne : (if ε (fI k r q) then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
  exact (mul_eq_zero.1 h.symm).resolve_left hne

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Distinguish the cases in `hj : StandardBasisEmbedding.bl k r j`. Take `⟨q', rfl⟩` from `StandardBasisEmbedding.ex_eB hj`. Rewrite using `[StandardBasisEmbedding.sumB _ (fun p hp => by rw [StandardBasisEmbedding.bw_off h hp hj, mul_zero])]`.

Simplify using `only [StandardBasisEmbedding.bw_ee, cay_col hW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Distinguish the cases in `hi : i.val < k`. Take `⟨qi, rfl⟩` from `ex_fI hi`. Simplify using `only [ite_mul, one_mul, zero_mul, kE_ff]`. Rewrite using `[Finset.sum_eq_single qi (fun b _ hb => by rw [if_neg (fun e => hb (fI_inj e).symm)]) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]`.

Rewrite using `[kE_row _ _ hi, if_neg (by intro e; apply hi; rw [e]; exact q'.2)]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (by intro e; apply hi; rw [e]; exact q.2), zero_mul]`. Rewrite using `[Finset.sum_eq_single j (fun b _ hb => by rw [StandardBasisEmbedding.bw_col h b hj, if_neg hb, mul_zero]) (fun h => absurd (Finset.mem_univ _) h), StandardBasisEmbedding.bw_col h j hj, if_pos rfl, mul_one]`. Distinguish the cases in `hi : i.val < k`.

Take `⟨qi, rfl⟩` from `ex_fI hi`. Rewrite using `[cay_zero hP hW qi hj]`. Use `(Finset.sum_eq_zero fun l _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `hl : l.val < k`. Take `⟨ql, rfl⟩` from `ex_fI hl`.

Rewrite using `[cay_zero hP hW ql hj, mul_zero]`. Rewrite using `[kE_col _ _ hl, if_neg (by rintro rfl; exact hl (by simp [fI])), zero_mul]`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => by rw [kE_row h b hi, if_neg (Ne.symm hb), zero_mul]) (fun h => absurd (Finset.mem_univ _) h), kE_row h i hi, if_pos rfl, one_mul]`.
-/
theorem cay_mul (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h = kE k r h * P := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hj : StandardBasisEmbedding.bl k r j
  · obtain ⟨q', rfl⟩ := StandardBasisEmbedding.ex_eB hj
    rw [StandardBasisEmbedding.sumB _ (fun p hp => by rw [StandardBasisEmbedding.bw_off h hp hj, mul_zero])]
    simp only [StandardBasisEmbedding.bw_ee, cay_col hW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      simp only [ite_mul, one_mul, zero_mul, kE_ff]
      rw [Finset.sum_eq_single qi (fun b _ hb => by rw [if_neg (fun e => hb (fI_inj e).symm)])
        (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
    · rw [kE_row _ _ hi, if_neg (by intro e; apply hi; rw [e]; exact q'.2)]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [if_neg (by intro e; apply hi; rw [e]; exact q.2), zero_mul]
  · rw [Finset.sum_eq_single j (fun b _ hb => by rw [StandardBasisEmbedding.bw_col h b hj, if_neg hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), StandardBasisEmbedding.bw_col h j hj, if_pos rfl, mul_one]
    by_cases hi : i.val < k
    · obtain ⟨qi, rfl⟩ := ex_fI hi
      rw [cay_zero hP hW qi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l.val < k
      · obtain ⟨ql, rfl⟩ := ex_fI hl
        rw [cay_zero hP hW ql hj, mul_zero]
      · rw [kE_col _ _ hl, if_neg (by rintro rfl; exact hl (by simp [fI])), zero_mul]
    · rw [Finset.sum_eq_single i (fun b _ hb => by rw [kE_row h b hi, if_neg (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), kE_row h i hi, if_pos rfl, one_mul]

/- English proof (translation)
Establish `hu : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hP.1`. Rewrite using `[cay_mul hP hW, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`.
-/
theorem cay_kE (hP : Formalism.MainNotions.S.IsCayley k r ε P) (hW : WCols k r P) (h : Matrix (Fin k) (Fin k) ℂ) :
    P * Formalism.MainNotions.S.blockW k r h * P⁻¹ = kE k r h := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  rw [cay_mul hP hW, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
