import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `t10 : T 1 0 = 0` using `hT _ _ (by decide)`. Establish `t20 : T 2 0 = 0` using `hT _ _ (by decide)`. Establish `t30 : T 3 0 = 0` using `hT _ _ (by decide)`. Establish `t21 : T 2 1 = 0` using `hT _ _ (by decide)`. Establish `t31 : T 3 1 = 0` using `hT _ _ (by decide)`.

Establish `c0 : ∀ i, (d i - T 0 0) * u i 0 = 0` using `fun i => by`. Use `congrFun (congrFun e i) 0` as an intermediate fact. Rewrite `this` using `[Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t10, t20, t30]`. Take the linear combination `this`. Establish `c1 : ∀ i, (d i - T 1 1) * u i 1 = u i 0 * T 0 1` using `fun i => by`.

Use `congrFun (congrFun e i) 1` as an intermediate fact. Rewrite `this` using `[Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t21, t31]`. Take the linear combination `this`. Establish `h10 : u 1 0 = 0` using `(mul_eq_zero.1 (c0 1)).resolve_left (hd _ _ (by decide))`. Establish `h30 : u 3 0 = 0` using `(mul_eq_zero.1 (c0 3)).resolve_left (hd _ _ (by decide))`.

Establish `s` using `sp_adj_mul hu`. Establish `s00` using `congrFun (congrFun s 0) 0`. Establish `s10` using `congrFun (congrFun s 1) 0`. Establish `s11` using `congrFun (congrFun s 1) 1`. Establish `s31` using `congrFun (congrFun s 3) 1`.

Rewrite `s00`, `s10`, `s11`, `s31` using `[Matrix.mul_apply, Fin.sum_univ_four]`. Rewrite `s00`, `s11` using `[Matrix.one_apply_eq]`. Rewrite `s10`, `s31` using `[Matrix.one_apply_ne (by decide)]`. Establish `a30 : adj u 3 0 = - u 3 0` using `by simp [adj_apply, sgn, Fin.rev]`. Establish `a31 : adj u 3 1 = - u 2 0` using `by simp [adj_apply, sgn, Fin.rev]`.

Establish `a32 : adj u 3 2 = u 1 0` using `by simp [adj_apply, sgn, Fin.rev]`. Establish `a33 : adj u 3 3 = u 0 0` using `by simp [adj_apply, sgn, Fin.rev]`. Rewrite `s31` using `[a30, a31, a32, a33]`. Use `⟨h10, h30, ?_, fun h00 => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn push Not at hn`.

Rewrite `s00` using `[hn.1, hn.2, h10, h30]`. Simplify using `at s00`. Establish `hA : d 0 - T 1 1 ≠ 0` using `hd _ _ (by decide)`. Establish `hB : d 2 - T 1 1 ≠ 0` using `hd _ _ (by decide)`. Establish `key : u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0`.

Apply `mul_left_cancel₀ (mul_ne_zero hA hB)` to reduce the goal to its premises. Take the linear combination `(d 0 - T 1 1) * u 0 0 * c1 2 - (d 2 - T 1 1) * u 2 0 * c1 0 + u 2 0 * T 0 1 * c0 0 - u 0 0 * T 0 1 * c0 2`. Use `⟨fun hn => ?_, key⟩` and prove the remaining obligations. Rewrite `hn` using `[h10, mul_zero, sub_zero]`. Establish `h11 : u 1 1 = 0` using `(mul_eq_zero.1 hn).resolve_left h00`.

Rewrite `s31` using `[h10, h30, h11]`. Establish `h31 : u 3 1 = 0`. Apply `mul_left_cancel₀ h00` to reduce the goal to its premises. Take the linear combination `s31`. Rewrite `s10` using `[h10, h30]`.

Rewrite `s11` using `[h11, h31]`. Apply `h00` to reduce the goal to its premises. Take the linear combination `u 0 1 * s10 - u 0 0 * s11 + adj u 1 2 * key`.
-/
private theorem resFlag_field {k : Type} [Field k] (u T : M4 k) (d : Fin 4 → k) (hu : IsGSp 1 u)
    (hT : IsUp T) (e : Matrix.diagonal d * u = u * T) (hd : ∀ i j, lamW i ≠ lamW j → d i - T j j ≠ 0) :
    u 1 0 = 0 ∧ u 3 0 = 0 ∧ (u 0 0 ≠ 0 ∨ u 2 0 ≠ 0) ∧
      (u 0 0 ≠ 0 → u 0 0 * u 1 1 - u 0 1 * u 1 0 ≠ 0 ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0) := by
  have t10 : T 1 0 = 0 := hT _ _ (by decide)
  have t20 : T 2 0 = 0 := hT _ _ (by decide)
  have t30 : T 3 0 = 0 := hT _ _ (by decide)
  have t21 : T 2 1 = 0 := hT _ _ (by decide)
  have t31 : T 3 1 = 0 := hT _ _ (by decide)
  have c0 : ∀ i, (d i - T 0 0) * u i 0 = 0 := fun i => by
    have := congrFun (congrFun e i) 0
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t10, t20, t30] at this
    linear_combination this
  have c1 : ∀ i, (d i - T 1 1) * u i 1 = u i 0 * T 0 1 := fun i => by
    have := congrFun (congrFun e i) 1
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t21, t31] at this
    linear_combination this
  have h10 : u 1 0 = 0 := (mul_eq_zero.1 (c0 1)).resolve_left (hd _ _ (by decide))
  have h30 : u 3 0 = 0 := (mul_eq_zero.1 (c0 3)).resolve_left (hd _ _ (by decide))
  have s := sp_adj_mul hu
  have s00 := congrFun (congrFun s 0) 0
  have s10 := congrFun (congrFun s 1) 0
  have s11 := congrFun (congrFun s 1) 1
  have s31 := congrFun (congrFun s 3) 1
  rw [Matrix.mul_apply, Fin.sum_univ_four] at s00 s10 s11 s31
  rw [Matrix.one_apply_eq] at s00 s11
  rw [Matrix.one_apply_ne (by decide)] at s10 s31
  have a30 : adj u 3 0 = - u 3 0 := by simp [adj_apply, sgn, Fin.rev]
  have a31 : adj u 3 1 = - u 2 0 := by simp [adj_apply, sgn, Fin.rev]
  have a32 : adj u 3 2 = u 1 0 := by simp [adj_apply, sgn, Fin.rev]
  have a33 : adj u 3 3 = u 0 0 := by simp [adj_apply, sgn, Fin.rev]
  rw [a30, a31, a32, a33] at s31
  refine ⟨h10, h30, ?_, fun h00 => ?_⟩
  · by_contra hn
    push Not at hn
    rw [hn.1, hn.2, h10, h30] at s00
    simp at s00
  · have hA : d 0 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have hB : d 2 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have key : u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hB)
      linear_combination (d 0 - T 1 1) * u 0 0 * c1 2 - (d 2 - T 1 1) * u 2 0 * c1 0
        + u 2 0 * T 0 1 * c0 0 - u 0 0 * T 0 1 * c0 2
    refine ⟨fun hn => ?_, key⟩
    rw [h10, mul_zero, sub_zero] at hn
    have h11 : u 1 1 = 0 := (mul_eq_zero.1 hn).resolve_left h00
    rw [h10, h30, h11] at s31
    have h31 : u 3 1 = 0 := by
      apply mul_left_cancel₀ h00
      linear_combination s31
    rw [h10, h30] at s10
    rw [h11, h31] at s11
    apply h00
    linear_combination u 0 1 * s10 - u 0 0 * s11 + adj u 1 2 * key

/- English proof (translation)
Introduce `R _ _ X u d d' hX hu hUp hdi hsep`. Establish `hX' : X.map (residue R) = Matrix.diagonal fun i => residue R (d i)`. Use extensionality with `i j`. Use `(residue_eq_zero_iff _).2 (hX i j)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`.

Rewrite using `[Matrix.map_apply, this]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ e]`.

Establish `hu' : IsGSp 1 (u.map (residue R))` using `by simpa using gsp_map (residue R) hu`. Establish `e : X * u = u * (adj u * X * u)`. Rewrite using `[← mul_assoc, ← mul_assoc, sp_mul_adj hu, one_mul]`. Establish `e'` using `congrArg (fun M : M4 R => M.map (residue R)) e`. Use `beta_reduce at e'`.

Rewrite `e'` using `[Matrix.map_mul, Matrix.map_mul (L := u), hX']`. Establish `H` using `resFlag_field (u.map (residue R)) ((adj u * X * u).map (residue R)) _ hu' (fun i j h => by rw [Matrix.map_apply, hUp i j h, map_zero]) e' (fun i j h => by`. Establish `h1` using `(residue_eq_zero_iff _).2 (hdi j)`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, h1, ← map_sub]`.

Conclude with `((hsep i j h).map _).ne_zero)`. Simplify using `only [Matrix.map_apply, ← map_mul, ← map_sub, residue_eq_zero_iff, Ne] at H`. Simplify `H` using `only [notMem_maximalIdeal]`.
-/
theorem UpperTheory.V.Ws.Lab.resFlag :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R) (d d' : Fin 4 → R), Cg (maximalIdeal R) X (Matrix.diagonal d) → IsGSp 1 u →
      IsUp (adj u * X * u) → (∀ i, (adj u * X * u : M4 R) i i - d' i ∈ maximalIdeal R) → (∀ i j, lamW i ≠ lamW j → IsUnit (d i - d' j)) →
      u 1 0 ∈ maximalIdeal R ∧ u 3 0 ∈ maximalIdeal R ∧ (IsUnit (u 0 0) ∨ IsUnit (u 2 0)) ∧
        (IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 ∈ maximalIdeal R) := by
  intro R _ _ X u d d' hX hu hUp hdi hsep
  have hX' : X.map (residue R) = Matrix.diagonal fun i => residue R (d i) := by
    ext i j
    have := (residue_eq_zero_iff _).2 (hX i j)
    rw [map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.diagonal_apply_ne _ e]
  have hu' : IsGSp 1 (u.map (residue R)) := by simpa using gsp_map (residue R) hu
  have e : X * u = u * (adj u * X * u) := by
    rw [← mul_assoc, ← mul_assoc, sp_mul_adj hu, one_mul]
  have e' := congrArg (fun M : M4 R => M.map (residue R)) e
  beta_reduce at e'
  rw [Matrix.map_mul, Matrix.map_mul (L := u), hX'] at e'
  have H := resFlag_field (u.map (residue R)) ((adj u * X * u).map (residue R)) _ hu'
    (fun i j h => by rw [Matrix.map_apply, hUp i j h, map_zero]) e' (fun i j h => by
      have h1 := (residue_eq_zero_iff _).2 (hdi j)
      rw [map_sub, sub_eq_zero] at h1
      rw [Matrix.map_apply, h1, ← map_sub]
      exact ((hsep i j h).map _).ne_zero)
  simp only [Matrix.map_apply, ← map_mul, ← map_sub, residue_eq_zero_iff, Ne] at H
  simpa only [notMem_maximalIdeal] using H
