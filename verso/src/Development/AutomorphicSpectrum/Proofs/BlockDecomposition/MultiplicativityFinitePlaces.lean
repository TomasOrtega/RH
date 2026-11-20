import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeMinor

/- English proof (translation)
Establish `h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k`. Use function extensionality and compare the values at `i j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Establish `key : ∀ M : Matrix κ κ K, M.det = (detRowAlternating (R` using `K) (n := κ)).toMultilinearMap M := fun _ => rfl`. Rewrite using `[key, h, MultilinearMap.map_sum]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem det_mul_submatrix_expand {K ι ι' κ : Type} [CommRing K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ((g * A).submatrix t id).det =
      ∑ s : κ → ι, (∏ i, g (t i) (s i)) * (A.submatrix s id).det := by
  have h : ((g * A).submatrix t id : κ → κ → K) = fun i => ∑ k, g (t i) k • A k := by
    funext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have key : ∀ M : Matrix κ κ K,
      M.det = (detRowAlternating (R := K) (n := κ)).toMultilinearMap M := fun _ => rfl
  rw [key, h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => norm_nonneg _`.
-/
theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/- English proof (translation)
The claim follows from `le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)`.
-/
theorem le_sz {K ι κ : Type} [NormedField K] [Finite ι] [Finite κ] (g : Matrix ι κ K)
    (i : ι) (j : κ) : ‖g i j‖ ≤ sz g :=
  le_ciSup (f := fun p : ι × κ => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (i, j)

/- English proof (translation)
The claim follows from `Real.iSup_nonneg fun _ => norm_nonneg _`.
-/
theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/- English proof (translation)
The claim follows from `le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s`.
-/
theorem le_nF {K ι κ : Type} [NormedField K] [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : κ → ι) : ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s

/- English proof (translation)
Rewrite using `[det_mul_submatrix_expand]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Use `mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_minor_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (t : κ → ι') :
    ‖((g * A).submatrix t id).det‖ ≤ sz g ^ Fintype.card κ * nF A := by
  rw [det_mul_submatrix_expand]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A)) fun s _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (le_nF A s) (norm_nonneg _) (pow_nonneg (sz_nonneg g) _)
  calc ∏ i, ‖g (t i) (s i)‖ ≤ ∏ _i : κ, sz g :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => le_sz g _ _
    _ = sz g ^ Fintype.card κ := by simp

/- English proof (translation)
The claim follows from `Real.iSup_le (fun t => norm_minor_mul_le g A t) (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))`.
-/
theorem nF_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A :=
  Real.iSup_le (fun t => norm_minor_mul_le g A t)
    (mul_nonneg (pow_nonneg (sz_nonneg g) _) (nF_nonneg A))

/- English proof (translation)
Unfold `nF`. Rewrite using `[Real.iSup_mul_of_nonneg (norm_nonneg _)]`. Use `iSup_congr fun t => ?_` and prove the remaining obligations. Establish `h : (A * s).submatrix t id = A.submatrix t id * s`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply]`. Rewrite using `[h, det_mul, norm_mul]`.
-/
theorem nF_mul_right {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by
  unfold nF
  rw [Real.iSup_mul_of_nonneg (norm_nonneg _)]
  refine iSup_congr fun t => ?_
  have h : (A * s).submatrix t id = A.submatrix t id * s := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, norm_mul]

/- English proof (translation)
Use `le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_` and prove the remaining obligations. Distinguish the cases in `ht : Function.Injective t`. Establish `hb : Function.Bijective t` using `Finite.injective_iff_bijective.mp ht`. Establish `h` using `Matrix.det_permute (Equiv.ofBijective t hb) s`. Establish `h' : (s.submatrix t id).det = _` using `h`.

Rewrite using `[h', norm_mul]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>`. Simplify using `[h1]`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by`. Simplify `ht` using `[Function.Injective]`.

Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]`. Simplify using the standard rewrite rules. Simplify using `using le_nF s id`.
-/
theorem nF_square {K κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) : nF s = ‖s.det‖ := by
  refine le_antisymm (Real.iSup_le (fun t => ?_) (norm_nonneg _)) ?_
  · by_cases ht : Function.Injective t
    · have hb : Function.Bijective t := Finite.injective_iff_bijective.mp ht
      have h := Matrix.det_permute (Equiv.ofBijective t hb) s
      have h' : (s.submatrix t id).det = _ := h
      rw [h', norm_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective t hb)) with h1 | h1 <;>
        simp [h1]
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, t i = t j ∧ i ≠ j := by
        simpa [Function.Injective] using ht
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij])]
      simp
  · simpa using le_nF s id

/- English proof (translation)
Introduce `K ι ι' κ _ _ _ _ _ _ A`. Conclude with `⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩`.
-/
theorem mulF : MulF := by
  intro K ι ι' κ _ _ _ _ _ _ A
  exact ⟨fun g => nF_mul_le g A, fun s => nF_mul_right A s, fun s => nF_square s⟩

end GlobalTheory.CompanionTheory.WedgeMinor
