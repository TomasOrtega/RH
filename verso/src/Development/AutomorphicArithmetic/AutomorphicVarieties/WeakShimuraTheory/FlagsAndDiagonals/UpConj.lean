import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k < i`. Rewrite using `[hX i k hk, zero_mul]`.

Rewrite using `[hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]`.
-/
private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hX i k h, zero_mul]`.

Rewrite using `[hY k i h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y : M4 R) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hX i k h, zero_mul]
    · rw [hY k i h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Introduce `i j h`. Rewrite using `[adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]`.
-/
private theorem up_adj {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := by
  intro i j h
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

/- English proof (translation)
Introduce `R _ b T hb hbu hT`. Establish `hadj` using `up_adj hbu`. Use `⟨up_mul (up_mul hbu hT) hadj, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : b i i * adj b i i = 1`. Use `congrFun (congrFun (sp_mul_adj hb) i) i` as an intermediate fact.

Rewrite `this` using `[up_mul_diag hbu hadj]`. Simplify using `using this`. Rewrite using `[up_mul_diag (up_mul hbu hT) hadj, up_mul_diag hbu hT]`. Take the linear combination `(T i i) * h1`.
-/
theorem UpperTheory.V.Ws.Lab.upConj :
    ∀ (R : Type) [CommRing R] (b T : M4 R), IsGSp 1 b → IsUp b → IsUp T → IsUp (b * T * adj b) ∧ ∀ i, (b * T * adj b : M4 R) i i = T i i := by
  intro R _ b T hb hbu hT
  have hadj := up_adj hbu
  refine ⟨up_mul (up_mul hbu hT) hadj, fun i => ?_⟩
  have h1 : b i i * adj b i i = 1 := by
    have := congrFun (congrFun (sp_mul_adj hb) i) i
    rw [up_mul_diag hbu hadj] at this
    simpa using this
  rw [up_mul_diag (up_mul hbu hT) hadj, up_mul_diag hbu hT]
  linear_combination (T i i) * h1
