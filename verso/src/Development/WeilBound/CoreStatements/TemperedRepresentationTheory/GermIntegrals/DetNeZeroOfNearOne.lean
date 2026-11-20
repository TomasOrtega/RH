import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3.RkX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hint : ∀ i l, A i l ∈ 𝒪[k]`. Introduce `i l`. Establish `h1 : valuation k ((1 : Matrix (Fin j) (Fin j) k) i l) ≤ 1`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`. Establish `: A i l = (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) + (1 : Matrix (Fin j) (Fin j) k) i l` using `by ring`. Use `show valuation k (A i l) ≤ 1`. Rewrite using `[this]`.

Conclude with `(Valuation.map_add _ _ _).trans (max_le (hA i l).le h1)`. Set `y : Matrix (Fin j) (Fin j) 𝒪[k]` to `Matrix.of fun i l => ⟨A i l, hint i l⟩`. Establish `hy : (algebraMap 𝒪[k] k).mapMatrix y = A`. Use extensionality with `i l`. Both sides reduce to the same expression.

Establish `hres : (IsLocalRing.residue 𝒪[k]).mapMatrix y = 1`. Use extensionality with `i l`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply]`. Rewrite using `[show (1 : Matrix (Fin j) (Fin j) (IsLocalRing.ResidueField 𝒪[k])) i l = IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l) by`. Distinguish the cases in `h : i = l`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]]`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]`. Establish `e : algebraMap 𝒪[k] k (y i l - (1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l) = A i l - (1 : Matrix (Fin j) (Fin j) k) i l`.

Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using `[y]`. Both sides reduce to the same expression. Simplify using `[y, Matrix.one_apply_ne h]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(hA i l).ne`. Establish `hdet : IsLocalRing.residue 𝒪[k] y.det = 1`. Rewrite using `[RingHom.map_det, hres, Matrix.det_one]`.

Introduce `h0`. Establish `: y.det = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun M => M.det) hy` as an intermediate fact. Rewrite `this` using `[← RingHom.map_det]`.

Rewrite `h0` using `[← this]`. Conclude with `h0`. Rewrite `hdet` using `[this, map_zero]`. Conclude with `zero_ne_one hdet`.
-/
theorem det_ne_zero_of_near_one {j : ℕ} (A : Matrix (Fin j) (Fin j) k)
    (hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1) : A.det ≠ 0 := by
  have hint : ∀ i l, A i l ∈ 𝒪[k] := by
    intro i l
    have h1 : valuation k ((1 : Matrix (Fin j) (Fin j) k) i l) ≤ 1 := by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    have : A i l = (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) + (1 : Matrix (Fin j) (Fin j) k) i l := by ring
    show valuation k (A i l) ≤ 1
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hA i l).le h1)
  let y : Matrix (Fin j) (Fin j) 𝒪[k] := Matrix.of fun i l => ⟨A i l, hint i l⟩
  have hy : (algebraMap 𝒪[k] k).mapMatrix y = A := by
    ext i l; rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix y = 1 := by
    ext i l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (1 : Matrix (Fin j) (Fin j) (IsLocalRing.ResidueField 𝒪[k])) i l
        = IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l) by
      by_cases h : i = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    have e : algebraMap 𝒪[k] k (y i l - (1 : Matrix (Fin j) (Fin j) 𝒪[k]) i l)
        = A i l - (1 : Matrix (Fin j) (Fin j) k) i l := by
      by_cases h : i = l
      · subst h; simp [y]; rfl
      · simp [y, Matrix.one_apply_ne h]; rfl
    rw [e]
    exact (hA i l).ne
  have hdet : IsLocalRing.residue 𝒪[k] y.det = 1 := by
    rw [RingHom.map_det, hres, Matrix.det_one]
  intro h0
  have : y.det = 0 := by
    apply Subtype.ext
    have := congrArg (fun M => M.det) hy
    rw [← RingHom.map_det] at this
    rw [← this] at h0
    exact h0
  rw [this, map_zero] at hdet
  exact zero_ne_one hdet

end PositivityTheory.Tls2.Ming3.RkX

namespace PositivityTheory.Tls2.Ming3

/- English proof (translation)
Introduce `k _ _ _ _ n r j hjn hjr c hc x hx`. Set `A : Matrix (Fin j) (Fin j) k` to `x.submatrix (Fin.castLE hjn) (Fin.castLE hjr)`. Establish `hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1`. Introduce `i l`. Establish `h` using `hx (Fin.castLE hjn i) (Fin.castLE hjr l)`.

Establish `e : idem k r n j (Fin.castLE hjn i) (Fin.castLE hjr l) = (1 : Matrix (Fin j) (Fin j) k) i l` using `by show (if (i : ℕ) = l ∧ (l : ℕ) < j then (1 : k) else 0) = _`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : (i : ℕ) ≠ l` using `fun e => h (Fin.ext e)`.

Simplify using `[Matrix.one_apply_ne h, h']`. Rewrite `h` using `[e]`. Conclude with `h.trans_lt hc`. Establish `hdet` using `RkX.det_ne_zero_of_near_one A hA`. Establish `h1 : A.rank = j`.

Rewrite using `[Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet))]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rk : RkSt := by
  intro k _ _ _ _ n r j hjn hjr c hc x hx
  let A : Matrix (Fin j) (Fin j) k := x.submatrix (Fin.castLE hjn) (Fin.castLE hjr)
  have hA : ∀ i l, valuation k (A i l - (1 : Matrix (Fin j) (Fin j) k) i l) < 1 := by
    intro i l
    have h := hx (Fin.castLE hjn i) (Fin.castLE hjr l)
    have e : idem k r n j (Fin.castLE hjn i) (Fin.castLE hjr l) = (1 : Matrix (Fin j) (Fin j) k) i l := by
      show (if (i : ℕ) = l ∧ (l : ℕ) < j then (1 : k) else 0) = _
      by_cases h : i = l
      · subst h; simp
      · have h' : (i : ℕ) ≠ l := fun e => h (Fin.ext e)
        simp [Matrix.one_apply_ne h, h']
    rw [e] at h
    exact h.trans_lt hc
  have hdet := RkX.det_ne_zero_of_near_one A hA
  have h1 : A.rank = j := by
    rw [Matrix.rank_of_isUnit A ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet))]
    simp
  calc j = A.rank := h1.symm
    _ ≤ x.rank := Matrix.rank_submatrix_le x _ _

end PositivityTheory.Tls2.Ming3
