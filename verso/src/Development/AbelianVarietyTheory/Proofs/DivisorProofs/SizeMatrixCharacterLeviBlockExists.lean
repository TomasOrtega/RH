import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorOfCharCentral
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.LeviBlockExponentLocal GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.LeviBlockExponentLocal

section CellNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[val_absPow]`. Conclude with `Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k u) z`.
-/
theorem norm_val_absPow (z : ℂ) (u : kˣ) : ‖((absPow k z u : ℂˣ) : ℂ)‖ = nabs k u ^ z.re := by
  rw [val_absPow]; exact Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k u) z

/- English proof (translation)
Simplify using `[nabs]`.
-/
theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [nabs]`. Consider the case `succ n ih => rw [pow_succ, nabs_mul', ih, pow_succ]`.
-/
theorem nabs_pow' (u : kˣ) (n : ℕ) : nabs k (u ^ n) = nabs k u ^ n := by
  induction n with
  | zero => simp [nabs]
  | succ n ih => rw [pow_succ, nabs_mul', ih, pow_succ]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use `ext`. Simplify using `[Matrix.GeneralLinearGroup.scalar]`.
-/
theorem det_scalar' {n : Type} [Fintype n] [DecidableEq n] (s : kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n s) = s ^ Fintype.card n := by
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`.
-/
theorem modExp_two_zero (m : Fin 2 → Type) [∀ a, Fintype (m a)] : modExp m 0 = Fintype.card (m 1) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_two]`.
-/
theorem modExp_two_one (m : Fin 2 → Type) [∀ a, Fintype (m a)] : modExp m 1 = -(Fintype.card (m 0) : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

/- English proof (translation)
Use extensionality with `a a'`. Use `(leviProj_apply k (g j) ⟨blockScalar₂ k N i ϖ j, blockScalar_mem_relParab N i ϖ g j trivial⟩ r a a').trans ?_` and prove the remaining obligations. Use `show ((blockScalar₂ k N i ϖ j : GL (Fin (blockSizes₂ N i j)) k) : Matrix (Fin (blockSizes₂ N i j)) (Fin (blockSizes₂ N i j)) k) _ _ = _`. Rewrite using `[blockScalar_apply]`. Distinguish the cases in `h : a = a'`.

Substitute `h` using the available equality. Simplify using `[Matrix.GeneralLinearGroup.scalar]`. Establish `h' : g j ⟨r, a⟩ ≠ g j ⟨r, a'⟩` using `by simpa using h`. Simplify using `[Matrix.GeneralLinearGroup.scalar, h, h']`.
-/
theorem relProj_blockScalar (N i : ℕ) (ϖ : kˣ) {β : Type} {c : Fin (i + 2) → β → Type} [LinearOrder β] [Fintype β]
    [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (blockSizes₂ N i j)) (j : Fin (i + 2)) (r : β) :
    relProj k g ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ j r =
      Matrix.GeneralLinearGroup.scalar _ (if j = ⟨i, by omega⟩ then ϖ else 1) := by
  ext a a'
  refine (leviProj_apply k (g j) ⟨blockScalar₂ k N i ϖ j, blockScalar_mem_relParab N i ϖ g j trivial⟩ r a a').trans ?_
  show ((blockScalar₂ k N i ϖ j : GL (Fin (blockSizes₂ N i j)) k) : Matrix (Fin (blockSizes₂ N i j)) (Fin (blockSizes₂ N i j)) k) _ _ = _
  rw [blockScalar_apply]
  by_cases h : a = a'
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · have h' : g j ⟨r, a⟩ ≠ g j ⟨r, a'⟩ := by simpa using h
    simp [Matrix.GeneralLinearGroup.scalar, h, h']

end CellNorm

end GlobalTheory.LeviBlockExponentLocal

namespace GlobalTheory.LeviBlockExponentLocal

section CellNormMain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `[pairChar, MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod, hχ]`.
-/
theorem norm_pairChar (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) (hχ : ∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1)
    (z : Levi k (fun j : Fin 2 => Fin (b j))) : ‖((pairChar k b χ z : ℂˣ) : ℂ)‖ = 1 := by
  simp [pairChar, MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod, hχ]

/- English proof (translation)
Use `set i0 : Fin (i + 2) := ⟨i, by omega⟩ with hi0`. Establish `hy` using `relProj_blockScalar (k := k) N i ϖ g`. Use `set y := relProj k g ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ with hydef`. Establish `hp : 0 < nabs k ϖ` using `nabs_pos' k ϖ`. Establish `hfac : ∀ j r (z : ℂ), ‖((absPow k z (Matrix.GeneralLinearGroup.det (y j r)) : ℂˣ) : ℂ)‖ = if j = i0 then nabs k ϖ ^ ((bm.1 r j : ℝ) * z.re) else 1`.

Introduce `j r z`. Rewrite using `[hy, det_scalar', norm_val_absPow, Fintype.card_fin]`. Use `split_ifs with h`. Rewrite using `[nabs_pow', Real.rpow_natCast_mul hp.le]`. Simplify using `[nabs_one']`.

Establish `hcol : bm.1 0 i0 + bm.1 1 i0 = 1`. Use `bm.2.2 i0` as an intermediate fact. Simplify `this` using `[Fin.sum_univ_two, blockSizes₂, hi0]`. Establish `hA : ‖((relDeltaHalf k (fun j r => Fin (bm.1 r j)) y : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[relDeltaHalf_apply, Units.coe_prod, norm_prod]`.

Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations. Rewrite using `[deltaHalf_apply, Units.coe_prod, norm_prod, Fin.prod_univ_two, hfac, hfac, modExp_two_zero, modExp_two_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [Fintype.card_fin]`.

Apply the tactic sequence `rcases (by omega : (bm.1 0 i0 = 0 ∧ bm.1 1 i0 = 1) ∨ (bm.1 0 i0 = 1 ∧ bm.1 1 i0 = 0)) with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]`. Simplify using the standard rewrite rules. Establish `hB : ‖((relDeltaHalf k (fun r j => Fin (bm.1 r j)) (swapBlocks k (fun r j => Fin (bm.1 r j)) y) : ℂˣ) : ℂ)‖ = nabs k ϖ ^ (((bm.1 0 i0 : ℝ) * modExp (fun j => Fin (bm.1 0 j)) i0 + (bm.1 1 i0 : ℝ) * modExp (fun j => Fin (bm.1 1 j)) i0) / 2)`. Rewrite using `[relDeltaHalf_apply, Units.coe_prod, norm_prod, Fin.prod_univ_two]`. Establish `hr : ∀ r, ‖((deltaHalf k (fun j => Fin (bm.1 r j)) (swapBlocks k (fun r j => Fin (bm.1 r j)) y r) : ℂˣ) : ℂ)‖ = nabs k ϖ ^ ((bm.1 r i0 : ℝ) * modExp (fun j => Fin (bm.1 r j)) i0 / 2)`.

Introduce `r`. Rewrite using `[deltaHalf_apply, Units.coe_prod, norm_prod, Finset.prod_eq_single i0]`. Conclude with `(hfac i0 r _).trans (by simp [mul_div_assoc])`. Introduce `j _ hj`. Conclude with `(hfac j r _).trans (if_neg hj)`.

Simplify using the standard rewrite rules. Rewrite using `[hr, hr, ← Real.rpow_add hp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hC` using `norm_pairChar (k := k) b χ hχ (relEmb k f (swapBlocks k (fun r j => Fin (bm.1 r j)) y))`.

Establish `hcs : ‖((cellScalar f g (pairChar k b χ) ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ : ℂˣ) : ℂ)‖ = nabs k ϖ ^ (-(((bm.1 0 i0 : ℝ) * modExp (fun j => Fin (bm.1 0 j)) i0 + (bm.1 1 i0 : ℝ) * modExp (fun j => Fin (bm.1 1 j)) i0) / 2))`. Simplify using `only [cellScalar, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]`. Rewrite using `[← hydef, hA, hB, hC, Real.rpow_neg hp.le]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrow : ∀ r, bm.1 r i0 = 1 → ∃ l : ℕ, l ≤ i ∧ (modExp (fun j => Fin (bm.1 r j)) i0 : ℝ) = b r - 1 - 2 * l`.

Introduce `r hr`. Use `⟨∑ j with j < i0, bm.1 r j, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hj : j < i0` using `(Finset.mem_filter.1 hj).2`. Establish `h1 : bm.1 r j ≤ ∑ r', bm.1 r' j` using `Finset.single_le_sum (f := fun r' => bm.1 r' j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)`.

Establish `h2` using `bm.2.2 j`. Establish `hjv : (j : ℕ) < i` using `by have := Fin.lt_def.1 hj; simpa [hi0] using this`. Establish `h3 : blockSizes₂ N i j = 1` using `if_pos (by omega)`. Simplify using `only [Fintype.card_fin] at h2`. Use linear arithmetic over natural numbers and integers.

Establish `hsum` using `bm.2.1 r`. Simplify using `only [Fintype.card_fin] at hsum`. Establish `hsplit : ∀ h : Fin (i + 2) → ℕ, ∑ j, h j = (∑ j with j < i0, h j) + h i0 + ∑ j with i0 < j, h j`. Introduce `h`. Establish `e : ∀ j, h j = (if j < i0 then h j else 0) + (if j = i0 then h j else 0) + (if i0 < j then h j else 0)`.

Introduce `j`. Break down `lt_trichotomy j i0 with hj | hj | hj` into its components or cases. Simplify using `[hj, hj.ne, not_lt.2 hj.le]`. Simplify using `[hj]`. Simplify using `[hj, hj.ne', not_lt.2 hj.le]`.

Rewrite using `[Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq']`. Simplify using the standard rewrite rules. Establish `hs` using `hsplit (bm.1 r)`. Rewrite `hs` using `[hsum, hr]`. Establish `hs'` using `congrArg (Nat.cast : ℕ → ℝ) hs`.

Move the coercions through the operations in `at hs'`. Simplify using `only [modExp, Fintype.card_fin]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `(by omega : (bm.1 0 i0 = 0 ∧ bm.1 1 i0 = 1) ∨ (bm.1 0 i0 = 1 ∧ bm.1 1 i0 = 0)) with ⟨h0, h1⟩ | ⟨h0, h1⟩` into its components or cases.

Take `⟨l, hl, he⟩` from `hrow 1 h1`. Use `⟨1, l, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[hcs, he, h0, h1]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨l, hl, he⟩` from `hrow 0 h0`. Use `⟨0, l, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[hcs, he, h0, h1]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_cellScalar_positionElt (N i : ℕ) (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ)
    (hχ : ∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) (ϖ : kˣ)
    (bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin (i + 2) => Fin (blockSizes₂ N i j)))
    (f : ∀ r, (Σ j, Fin (bm.1 r j)) ≃ Fin (b r)) (g : ∀ j, (Σ r, Fin (bm.1 r j)) ≃ Fin (blockSizes₂ N i j)) :
    ∃ (r : Fin 2) (l : ℕ), l ≤ i ∧
      ‖((cellScalar f g (pairChar k b χ) ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ : ℂˣ) : ℂ)‖ =
        nabs k ϖ ^ ((1 - (b r : ℝ)) / 2 + l) := by
  set i0 : Fin (i + 2) := ⟨i, by omega⟩ with hi0
  have hy := relProj_blockScalar (k := k) N i ϖ g
  set y := relProj k g ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ with hydef
  have hp : 0 < nabs k ϖ := nabs_pos' k ϖ
  have hfac : ∀ j r (z : ℂ), ‖((absPow k z (Matrix.GeneralLinearGroup.det (y j r)) : ℂˣ) : ℂ)‖ =
      if j = i0 then nabs k ϖ ^ ((bm.1 r j : ℝ) * z.re) else 1 := by
    intro j r z
    rw [hy, det_scalar', norm_val_absPow, Fintype.card_fin]
    split_ifs with h
    · rw [nabs_pow', Real.rpow_natCast_mul hp.le]
    · simp [nabs_one']
  have hcol : bm.1 0 i0 + bm.1 1 i0 = 1 := by
    have := bm.2.2 i0
    simpa [Fin.sum_univ_two, blockSizes₂, hi0] using this
  have hA : ‖((relDeltaHalf k (fun j r => Fin (bm.1 r j)) y : ℂˣ) : ℂ)‖ = 1 := by
    rw [relDeltaHalf_apply, Units.coe_prod, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [deltaHalf_apply, Units.coe_prod, norm_prod, Fin.prod_univ_two, hfac, hfac, modExp_two_zero,
      modExp_two_one]
    split_ifs with h
    · subst h
      simp only [Fintype.card_fin]
      rcases (by omega : (bm.1 0 i0 = 0 ∧ bm.1 1 i0 = 1) ∨ (bm.1 0 i0 = 1 ∧ bm.1 1 i0 = 0)) with
        ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]
    · simp
  have hB : ‖((relDeltaHalf k (fun r j => Fin (bm.1 r j)) (swapBlocks k (fun r j => Fin (bm.1 r j)) y) : ℂˣ) : ℂ)‖ =
      nabs k ϖ ^ (((bm.1 0 i0 : ℝ) * modExp (fun j => Fin (bm.1 0 j)) i0 +
        (bm.1 1 i0 : ℝ) * modExp (fun j => Fin (bm.1 1 j)) i0) / 2) := by
    rw [relDeltaHalf_apply, Units.coe_prod, norm_prod, Fin.prod_univ_two]
    have hr : ∀ r, ‖((deltaHalf k (fun j => Fin (bm.1 r j)) (swapBlocks k (fun r j => Fin (bm.1 r j)) y r) : ℂˣ) : ℂ)‖ =
        nabs k ϖ ^ ((bm.1 r i0 : ℝ) * modExp (fun j => Fin (bm.1 r j)) i0 / 2) := by
      intro r
      rw [deltaHalf_apply, Units.coe_prod, norm_prod, Finset.prod_eq_single i0]
      · exact (hfac i0 r _).trans (by simp [mul_div_assoc])
      · intro j _ hj; exact (hfac j r _).trans (if_neg hj)
      · simp
    rw [hr, hr, ← Real.rpow_add hp]; congr 1; ring
  have hC := norm_pairChar (k := k) b χ hχ (relEmb k f (swapBlocks k (fun r j => Fin (bm.1 r j)) y))
  have hcs : ‖((cellScalar f g (pairChar k b χ) ⟨blockScalar₂ k N i ϖ, blockScalar_mem_relParab N i ϖ g⟩ : ℂˣ) : ℂ)‖ =
      nabs k ϖ ^ (-(((bm.1 0 i0 : ℝ) * modExp (fun j => Fin (bm.1 0 j)) i0 +
        (bm.1 1 i0 : ℝ) * modExp (fun j => Fin (bm.1 1 j)) i0) / 2)) := by
    simp only [cellScalar, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    rw [← hydef, hA, hB, hC, Real.rpow_neg hp.le]; ring
  have hrow : ∀ r, bm.1 r i0 = 1 → ∃ l : ℕ, l ≤ i ∧
      (modExp (fun j => Fin (bm.1 r j)) i0 : ℝ) = b r - 1 - 2 * l := by
    intro r hr
    refine ⟨∑ j with j < i0, bm.1 r j, ?_, ?_⟩
    · calc ∑ j with j < i0, bm.1 r j ≤ ∑ j with j < i0, 1 := Finset.sum_le_sum fun j hj => ?_
        _ = i := by simp [Finset.filter_gt_eq_Iio, Fin.card_Iio, hi0]
      have hj : j < i0 := (Finset.mem_filter.1 hj).2
      have h1 : bm.1 r j ≤ ∑ r', bm.1 r' j :=
        Finset.single_le_sum (f := fun r' => bm.1 r' j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      have h2 := bm.2.2 j
      have hjv : (j : ℕ) < i := by have := Fin.lt_def.1 hj; simpa [hi0] using this
      have h3 : blockSizes₂ N i j = 1 := if_pos (by omega)
      simp only [Fintype.card_fin] at h2
      omega
    · have hsum := bm.2.1 r
      simp only [Fintype.card_fin] at hsum
      have hsplit : ∀ h : Fin (i + 2) → ℕ,
          ∑ j, h j = (∑ j with j < i0, h j) + h i0 + ∑ j with i0 < j, h j := by
        intro h
        have e : ∀ j, h j = (if j < i0 then h j else 0) + (if j = i0 then h j else 0) +
            (if i0 < j then h j else 0) := by
          intro j
          rcases lt_trichotomy j i0 with hj | hj | hj
          · simp [hj, hj.ne, not_lt.2 hj.le]
          · simp [hj]
          · simp [hj, hj.ne', not_lt.2 hj.le]
        rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq']
        simp
      have hs := hsplit (bm.1 r)
      rw [hsum, hr] at hs
      have hs' := congrArg (Nat.cast : ℕ → ℝ) hs
      push_cast at hs'
      simp only [modExp, Fintype.card_fin]
      push_cast
      linarith
  rcases (by omega : (bm.1 0 i0 = 0 ∧ bm.1 1 i0 = 1) ∨ (bm.1 0 i0 = 1 ∧ bm.1 1 i0 = 0)) with
    ⟨h0, h1⟩ | ⟨h0, h1⟩
  · obtain ⟨l, hl, he⟩ := hrow 1 h1
    refine ⟨1, l, hl, ?_⟩
    rw [hcs, he, h0, h1]; congr 1; push_cast; ring
  · obtain ⟨l, hl, he⟩ := hrow 0 h0
    refine ⟨0, l, hl, ?_⟩
    rw [hcs, he, h0, h1]; congr 1; push_cast; ring

end CellNormMain

end GlobalTheory.LeviBlockExponentLocal
