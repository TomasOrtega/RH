import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Introduce `k _ _ _ _ n s s' hs hs' y hy`. Establish `hc : (dg s : GL (Fin n) k) * y = y * dg s'`. Rewrite using `[← hy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]`. Establish `hM` using `congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) hc`. Simplify using `only [Units.val_mul, UpperTheory.V.Z.Sym.Sig.dg, val_diagT] at hM`.

Establish `key : ∀ i j, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 → (s i : k) = s' j`. Introduce `i j hij`. Establish `e` using `congrFun (congrFun hM i) j`. Rewrite `e` using `[Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]`. Conclude with `mul_left_cancel₀ hij e`.

Establish `hdet : (y : Matrix (Fin n) (Fin n) k).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero`. Establish `col : ∀ j, ∃ i, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0`. Introduce `j`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hdet (Matrix.det_eq_zero_of_column_eq_zero j h)`. Use `choose σ hσ using col`. Establish `hσs : ∀ j, (s (σ j) : k) = s' j` using `fun j => key _ _ (hσ j)`. Establish `hmono : StrictMono σ`. Introduce `j j' hjj'`.

Establish `h1` using `hs' j j' hjj'`. Rewrite `h1` using `[← hσs, ← hσs]`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Break down `hle.lt_or_eq with h2 | h2` into its components or cases.

Conclude with `lt_irrefl _ (lt_trans h1 (hs _ _ h2))`. Rewrite `h1` using `[h2]`. Conclude with `lt_irrefl _ h1`. Establish `hid : σ = id` using `hmono.eq_id`. Establish `hss : ∀ j, (s j : k) = s' j`.

Introduce `j`. Use `hσs j` as an intermediate fact. Rewrite `this` using `[hid]`. Then use the resulting hypothesis. Establish `inj : ∀ i j, (s i : k) = s j → i = j`. Introduce `i j h`.

Break down `lt_trichotomy i j with hij | hij | hij` into its components or cases. Use `hs i j hij` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `absurd this (lt_irrefl _)`. Conclude with `hij`.

Use `hs j i hij` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `absurd this (lt_irrefl _)`. Establish `hdiag : ∀ i j, i ≠ j → (y : Matrix (Fin n) (Fin n) k) i j = 0`. Introduce `i j hij`.

Assume the negation of the conclusion as `h`. Conclude with `hij (inj i j ((key i j h).trans (hss j).symm))`. Establish `hne : ∀ i, (y : Matrix (Fin n) (Fin n) k) i i ≠ 0`. Introduce `i`. Use `hσ i` as an intermediate fact.

Rewrite `this` using `[hid]`. Then use the resulting hypothesis. Use `⟨funext fun j => Units.ext (hss j), fun i => Units.mk0 _ (hne i), ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [UpperTheory.V.Z.Sym.Sig.dg, val_diagT, Units.val_mk0]`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hdiag i j hij, Matrix.diagonal_apply_ne _ hij]`.
-/
theorem UpperTheory.V.Z.Sym.Sig.conjDiag : UpperTheory.V.Z.Sym.Sig.ConjDiag := by
  intro k _ _ _ _ n s s' hs hs' y hy
  have hc : (dg s : GL (Fin n) k) * y = y * dg s' := by
    rw [← hy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hM := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) hc
  simp only [Units.val_mul, UpperTheory.V.Z.Sym.Sig.dg, val_diagT] at hM
  have key : ∀ i j, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 → (s i : k) = s' j := by
    intro i j hij
    have e := congrFun (congrFun hM i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at e
    exact mul_left_cancel₀ hij e
  have hdet : (y : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  have col : ∀ j, ∃ i, (y : Matrix (Fin n) (Fin n) k) i j ≠ 0 := by
    intro j
    by_contra h
    push_neg at h
    exact hdet (Matrix.det_eq_zero_of_column_eq_zero j h)
  choose σ hσ using col
  have hσs : ∀ j, (s (σ j) : k) = s' j := fun j => key _ _ (hσ j)
  have hmono : StrictMono σ := by
    intro j j' hjj'
    have h1 := hs' j j' hjj'
    rw [← hσs, ← hσs] at h1
    by_contra hle
    push_neg at hle
    rcases hle.lt_or_eq with h2 | h2
    · exact lt_irrefl _ (lt_trans h1 (hs _ _ h2))
    · rw [h2] at h1
      exact lt_irrefl _ h1
  have hid : σ = id := hmono.eq_id
  have hss : ∀ j, (s j : k) = s' j := by
    intro j
    have := hσs j
    rwa [hid] at this
  have inj : ∀ i j, (s i : k) = s j → i = j := by
    intro i j h
    rcases lt_trichotomy i j with hij | hij | hij
    · have := hs i j hij
      rw [h] at this
      exact absurd this (lt_irrefl _)
    · exact hij
    · have := hs j i hij
      rw [h] at this
      exact absurd this (lt_irrefl _)
  have hdiag : ∀ i j, i ≠ j → (y : Matrix (Fin n) (Fin n) k) i j = 0 := by
    intro i j hij
    by_contra h
    exact hij (inj i j ((key i j h).trans (hss j).symm))
  have hne : ∀ i, (y : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
    intro i
    have := hσ i
    rwa [hid] at this
  refine ⟨funext fun j => Units.ext (hss j), fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  simp only [UpperTheory.V.Z.Sym.Sig.dg, val_diagT, Units.val_mk0]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]

end
