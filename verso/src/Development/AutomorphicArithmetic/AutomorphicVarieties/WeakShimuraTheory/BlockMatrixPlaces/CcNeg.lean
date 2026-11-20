import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Establish `hunit : ∀ u : R, u - 2 * s ∈ maximalIdeal R → IsUnit u`. Introduce `u hu`. Establish `h2s : IsUnit (2 * s)` using `h2.mul ⟨⟨s, s, hs, hs⟩, rfl⟩`. Assume the negation of the conclusion as `hnu`. Establish `hum : u ∈ maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).mpr hnu`.

Establish `h2m : 2 * s ∈ maximalIdeal R`. Use `(maximalIdeal R).sub_mem hum hu` as an intermediate fact. Simplify using `using this`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp h2m h2s`. Establish `hsum : IsUnit (a + d)` using `hunit _ (by`.

Establish `e : a + d - 2 * s = (a - s) + (d - s)` using `by ring`. Rewrite using `[e]`. Conclude with `(maximalIdeal R).add_mem ha hd)`. Establish `hb : b = 0` using `(hsum.mul_left_eq_zero).mp (by linear_combination e2)`. Establish `hc : c = 0` using `(hsum.mul_left_eq_zero).mp (by linear_combination e3)`.

Substitute `hb hc` using the available equality. Establish `hpa : IsUnit (a + s)` using `hunit _ (by`. Establish `e : a + s - 2 * s = a - s` using `by ring`. Rewrite using `[e]`. Conclude with `ha)`.

Establish `hpd : IsUnit (d + s)` using `hunit _ (by`. Establish `e : d + s - 2 * s = d - s` using `by ring`. Rewrite using `[e]`. Conclude with `hd)`. Use `⟨?_, rfl, rfl, ?_⟩` and prove the remaining obligations.

Establish `h : (a - s) * (a + s) = 0` using `by linear_combination e1 - hs`. Conclude with `sub_eq_zero.mp ((hpa.mul_left_eq_zero).mp h)`. Establish `h : (d - s) * (d + s) = 0` using `by linear_combination e4 - hs`. Conclude with `sub_eq_zero.mp ((hpd.mul_left_eq_zero).mp h)`.
-/
private theorem eq_diag_of_square_eq_one_of_near_sign {R : Type} [CommRing R] [IsLocalRing R] (s a b c d : R)
    (hs : s * s = 1) (h2 : IsUnit (2 : R)) (ha : a - s ∈ maximalIdeal R)
    (hd : d - s ∈ maximalIdeal R) (e1 : a * a + b * c = 1) (e2 : a * b + b * d = 0)
    (e3 : c * a + d * c = 0) (e4 : c * b + d * d = 1) : a = s ∧ b = 0 ∧ c = 0 ∧ d = s := by
  have hunit : ∀ u : R, u - 2 * s ∈ maximalIdeal R → IsUnit u := by
    intro u hu
    have h2s : IsUnit (2 * s) := h2.mul ⟨⟨s, s, hs, hs⟩, rfl⟩
    by_contra hnu
    have hum : u ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2m : 2 * s ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem hum hu
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).mp h2m h2s
  have hsum : IsUnit (a + d) := hunit _ (by
    have e : a + d - 2 * s = (a - s) + (d - s) := by ring
    rw [e]
    exact (maximalIdeal R).add_mem ha hd)
  have hb : b = 0 := (hsum.mul_left_eq_zero).mp (by linear_combination e2)
  have hc : c = 0 := (hsum.mul_left_eq_zero).mp (by linear_combination e3)
  subst hb hc
  have hpa : IsUnit (a + s) := hunit _ (by
    have e : a + s - 2 * s = a - s := by ring
    rw [e]
    exact ha)
  have hpd : IsUnit (d + s) := hunit _ (by
    have e : d + s - 2 * s = d - s := by ring
    rw [e]
    exact hd)
  refine ⟨?_, rfl, rfl, ?_⟩
  · have h : (a - s) * (a + s) = 0 := by linear_combination e1 - hs
    exact sub_eq_zero.mp ((hpa.mul_left_eq_zero).mp h)
  · have h : (d - s) * (d + s) = 0 := by linear_combination e4 - hs
    exact sub_eq_zero.mp ((hpd.mul_left_eq_zero).mp h)

/- English proof (translation)
Introduce `R _ _ X h2 hB hX hm`. Establish `sq : ∀ i j, ∑ k, X i k * X k j = (1 : M4 R) i j` using `fun i j => by`. Rewrite using `[← Matrix.mul_apply, hX]`. Establish `hm' : ∀ i, X i i - ![-1, 1, -1, 1] i ∈ maximalIdeal R` using `fun i => by`. Simplify `hm i i` using `[eAB]`.

Establish `z01 : X 0 1 = 0` using `hB 0 1 (by simp [lamW])`. Establish `z03 : X 0 3 = 0` using `hB 0 3 (by simp [lamW])`. Establish `z10 : X 1 0 = 0` using `hB 1 0 (by simp [lamW])`. Establish `z12 : X 1 2 = 0` using `hB 1 2 (by simp [lamW])`. Establish `z21 : X 2 1 = 0` using `hB 2 1 (by simp [lamW])`.

Establish `z23 : X 2 3 = 0` using `hB 2 3 (by simp [lamW])`. Establish `z30 : X 3 0 = 0` using `hB 3 0 (by simp [lamW])`. Establish `z32 : X 3 2 = 0` using `hB 3 2 (by simp [lamW])`. Establish `q : ∀ i j, (∑ k, X i k * X k j) = X i 0 * X 0 j + X i 1 * X 1 j + X i 2 * X 2 j + X i 3 * X 3 j` using `fun i j => Fin.sum_univ_four _`. Take `⟨a0, b0, c0, d0⟩` from `eq_diag_of_square_eq_one_of_near_sign (-1) (X 0 0) (X 0 2) (X 2 0) (X 2 2) (by ring) h2 (by simpa using hm' 0) (by simpa using hm' 2) (by have h := sq 0 0; rw [q] at h; simp [z01, z03, z10, z30] at h; linear_combination h) (by have h := sq 0 2; rw [q] at h; simp [z01, z03, z12, z …`.

Take `⟨a1, b1, c1, d1⟩` from `eq_diag_of_square_eq_one_of_near_sign 1 (X 1 1) (X 1 3) (X 3 1) (X 3 3) (by ring) h2 (by simpa using hm' 1) (by simpa using hm' 3) (by have h := sq 1 1; rw [q] at h; simp [z10, z12, z01, z21] at h; linear_combination h) (by have h := sq 1 3; rw [q] at h; simp [z10, z12, z03, z23] …`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[eAB, z01, z03, z10, z12, z21, z23, z30, z32, a0, b0, c0, d0, a1, b1, c1, d1]`.
-/
theorem UpperTheory.V.Ws.Bl.ccNeg :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : M4 R), IsUnit (2 : R) → IsBlock X → X * X = 1 → (∀ i j, X i j - eAB R i j ∈ maximalIdeal R) → X = eAB R := by
  intro R _ _ X h2 hB hX hm
  have sq : ∀ i j, ∑ k, X i k * X k j = (1 : M4 R) i j := fun i j => by
    rw [← Matrix.mul_apply, hX]
  have hm' : ∀ i, X i i - ![-1, 1, -1, 1] i ∈ maximalIdeal R := fun i => by
    simpa [eAB] using hm i i
  have z01 : X 0 1 = 0 := hB 0 1 (by simp [lamW])
  have z03 : X 0 3 = 0 := hB 0 3 (by simp [lamW])
  have z10 : X 1 0 = 0 := hB 1 0 (by simp [lamW])
  have z12 : X 1 2 = 0 := hB 1 2 (by simp [lamW])
  have z21 : X 2 1 = 0 := hB 2 1 (by simp [lamW])
  have z23 : X 2 3 = 0 := hB 2 3 (by simp [lamW])
  have z30 : X 3 0 = 0 := hB 3 0 (by simp [lamW])
  have z32 : X 3 2 = 0 := hB 3 2 (by simp [lamW])
  have q : ∀ i j, (∑ k, X i k * X k j) = X i 0 * X 0 j + X i 1 * X 1 j + X i 2 * X 2 j + X i 3 * X 3 j :=
    fun i j => Fin.sum_univ_four _
  obtain ⟨a0, b0, c0, d0⟩ := eq_diag_of_square_eq_one_of_near_sign (-1) (X 0 0) (X 0 2) (X 2 0) (X 2 2) (by ring) h2
    (by simpa using hm' 0) (by simpa using hm' 2)
    (by have h := sq 0 0; rw [q] at h; simp [z01, z03, z10, z30] at h; linear_combination h)
    (by have h := sq 0 2; rw [q] at h; simp [z01, z03, z12, z32] at h; linear_combination h)
    (by have h := sq 2 0; rw [q] at h; simp [z21, z23, z10, z30] at h; linear_combination h)
    (by have h := sq 2 2; rw [q] at h; simp [z21, z23, z12, z32] at h; linear_combination h)
  obtain ⟨a1, b1, c1, d1⟩ := eq_diag_of_square_eq_one_of_near_sign 1 (X 1 1) (X 1 3) (X 3 1) (X 3 3) (by ring) h2
    (by simpa using hm' 1) (by simpa using hm' 3)
    (by have h := sq 1 1; rw [q] at h; simp [z10, z12, z01, z21] at h; linear_combination h)
    (by have h := sq 1 3; rw [q] at h; simp [z10, z12, z03, z23] at h; linear_combination h)
    (by have h := sq 3 1; rw [q] at h; simp [z30, z32, z01, z21] at h; linear_combination h)
    (by have h := sq 3 3; rw [q] at h; simp [z30, z32, z03, z23] at h; linear_combination h)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eAB, z01, z03, z10, z12, z21, z23, z30, z32, a0, b0, c0, d0, a1, b1, c1, d1]
