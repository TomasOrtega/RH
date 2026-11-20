import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoBlockNeZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Io

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] (β : GlobalTheory X) (j : Fin (numSeg X.TT))

/- English proof (translation)
Unfold `ioD ioA`. Conclude with `aeval_X _ _`.
-/
theorem ioD_X (v : BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioD ioA
  exact aeval_X _ _

/- English proof (translation)
Rewrite using `[ioD_X]`. Establish `hl : ((Fin.castSucc l : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t` using `l.2`. Simplify using `only [symVar, symLev]`. Rewrite using `[dif_pos hl, dif_pos hl]`. Both sides reduce to the same expression.
-/
theorem ioD_scal (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.castSucc l, bb))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !bb), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  rw [ioD_X]
  have hl : ((Fin.castSucc l : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t := l.2
  simp only [symVar, symLev]
  rw [dif_pos hl, dif_pos hl]
  rfl

/- English proof (translation)
Rewrite using `[ioD_X]`. Establish `hl : ¬ ((Fin.last (BDk C0 CE1 CE2 mu X β j).T.t : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) < (X.seg C0 CE1 CE2 j).t` using `lt_irrefl _`. Simplify using `only [symVar, symLev]`. Rewrite using `[dif_neg hl, dif_neg hl, pow_one]`.
-/
theorem ioD_scalLast (bb : Bool) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inr (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t, bb))) =
      MvPolynomial.X ((topEnd X j, !bb), 0) := by
  rw [ioD_X]
  have hl : ¬ ((Fin.last (BDk C0 CE1 CE2 mu X β j).T.t : Fin ((BDk C0 CE1 CE2 mu X β j).T.t + 1)) : ℕ) <
      (X.seg C0 CE1 CE2 j).t := lt_irrefl _
  simp only [symVar, symLev]
  rw [dif_neg hl, dif_neg hl, pow_one]

/- English proof (translation)
Rewrite using `[ioD_X]`. Establish `hi` using `i.2`. Establish `hl : (a : ℕ) < 2 * segS X.TT j` using `by omega`. Simplify using `only [symVar, symLev]`. Rewrite using `[dif_pos hl, dif_pos hl]`.

Establish `e1 : (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) = i` using `Fin.ext (by simp only; omega)`. Establish `e2 : decide ((a : ℕ) % 2 = 0) = decide (e = 0)`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1, e2]`.
-/
theorem ioD_odd (i : Fin (segS X.TT j)) (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * i + e)
    (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topOdd X j i, decide (e = 0)), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i := by
  rw [ioD_X]
  have hi := i.2
  have hl : (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dif_pos hl, dif_pos hl]
  have e1 : (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by simp only; omega)
  have e2 : decide ((a : ℕ) % 2 = 0) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e1, e2]

/- English proof (translation)
Rewrite using `[ioD_X]`. Establish `hl : ¬ (a : ℕ) < 2 * segS X.TT j` using `by omega`. Simplify using `only [symVar, symLev]`. Rewrite using `[dif_neg hl, dif_neg hl, pow_one]`. Establish `e2 : decide ((a : ℕ) = 2 * segS X.TT j) = decide (e = 0)`.

Use `congr 1`. Apply `propext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Rewrite using `[e2]`.
-/
theorem ioD_end (e : ℕ) (he : e < 2) (a : Fin (2 * segS X.TT j + 1 + 1)) (ha : (a : ℕ) = 2 * segS X.TT j + e) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (Sum.inl (a, c))) =
      MvPolynomial.X ((topEnd X j, decide (e = 0)), c.succ) := by
  rw [ioD_X]
  have hl : ¬ (a : ℕ) < 2 * segS X.TT j := by omega
  simp only [symVar, symLev]
  rw [dif_neg hl, dif_neg hl, pow_one]
  have e2 : decide ((a : ℕ) = 2 * segS X.TT j) = decide (e = 0) := by
    congr 1
    apply propext
    omega
  rw [e2]

/- English proof (translation)
Unfold `BlockData.Ehat EhatT scalZ scalS`. Rewrite using `[map_add, map_mul, map_sum, ioD_scal, ioD_scal]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hu` using `(uTop (X.seg C0 CE1 CE2 j) l).2`.

Rewrite using `[map_mul, ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 0 (by omega) _ (by show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ)) (2 * segS X.TT j + 1) = _ omega), ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 1 (by omega) _ (by show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l …`. Both sides reduce to the same expression.
-/
theorem ioD_Ehat (l : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) l) =
      EhatT O X (topOdd X j (uTop (X.seg C0 CE1 CE2 j) l)) ((X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l)) := by
  unfold BlockData.Ehat EhatT scalZ scalS
  rw [map_add, map_mul, map_sum, ioD_scal, ioD_scal]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hu := (uTop (X.seg C0 CE1 CE2 j) l).2
  rw [map_mul, ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 0 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ)) (2 * segS X.TT j + 1) = _
      omega),
    ioD_odd β j (uTop (X.seg C0 CE1 CE2 j) l) 1 (by omega) _ (by
      show min (2 * ((uTop (X.seg C0 CE1 CE2 j) l : Fin (segS X.TT j)) : ℕ) + 1) (2 * segS X.TT j + 1) = _
      omega)]
  rfl

/- English proof (translation)
Unfold `hTop hKey`. Rewrite using `[Fin.sum_univ_succ]`. Unfold `BlockData.Eplus scalZ scalS xiVar`. Rewrite using `[map_add, map_mul, map_sum, ioD_scalLast, ioD_scalLast]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ioD_end β j 0 (by omega) _ (by rfl), ioD_end β j 1 (by omega) _ (by rfl)]`. Both sides reduce to the same expression.
-/
theorem ioD_Eplus :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) = hTop O X (topEnd X j) := by
  unfold hTop hKey
  rw [Fin.sum_univ_succ]
  unfold BlockData.Eplus scalZ scalS xiVar
  rw [map_add, map_mul, map_sum, ioD_scalLast, ioD_scalLast]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, ioD_end β j 0 (by omega) _ (by rfl), ioD_end β j 1 (by omega) _ (by rfl)]
  rfl

end Io

/- English proof (translation)
Establish `h1 : ∑ i : Fin s, (if (i : ℕ) < S.sigma then 0 else F i) = ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ (i : ℕ) < S.sigma), F i`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : (i : ℕ) < S.sigma <;> simp [h]`. Rewrite using `[h1]`.

Use `Finset.sum_bij (fun l _ => uTop S l) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `l _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, uTop]`. Use linear arithmetic over natural numbers and integers. Introduce `l _ l' _ h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [uTop] at this`. Conclude with `Fin.ext (by omega)`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi`.

Use `⟨⟨(i : ℕ) - S.sigma, ?_⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use `i.2` as an intermediate fact. Unfold `SegData.t`. Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [uTop]`. Use linear arithmetic over natural numbers and integers. Introduce `l _`. Both sides reduce to the same expression.
-/
theorem uTop_sum {s : ℕ} {M : Type} [AddCommMonoid M] (S : SegData s) (F : Fin s → M) :
    ∑ l : Fin S.t, F (uTop S l) = ∑ i : Fin s, if (i : ℕ) < S.sigma then 0 else F i := by
  classical
  have h1 : ∑ i : Fin s, (if (i : ℕ) < S.sigma then 0 else F i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin s => ¬ (i : ℕ) < S.sigma), F i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < S.sigma <;> simp [h]
  rw [h1]
  refine Finset.sum_bij (fun l _ => uTop S l) ?_ ?_ ?_ ?_
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uTop]
    omega
  · intro l _ l' _ h
    have := congrArg Fin.val h
    simp only [uTop] at this
    exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨(i : ℕ) - S.sigma, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := i.2
      unfold SegData.t
      omega
    · apply Fin.ext
      simp only [uTop]
      omega
  · intro l _
    rfl

end Formalism.MainNotions.ColumnSystems.Pf
