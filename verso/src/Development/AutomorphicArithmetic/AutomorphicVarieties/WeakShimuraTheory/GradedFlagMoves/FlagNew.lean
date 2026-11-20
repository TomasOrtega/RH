import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring`. Apply the tactic sequence `intro i fin_cases i <;> simp`. Apply the tactic sequence `intro i j h fin_cases i <;> fin_cases j <;> simp at h ⊢`.
-/
private theorem lowMk {R : Type} [CommRing R] (x y z t : R) :
    IsLow (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · intro i
    fin_cases i <;> simp
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev] <;> ring`.
-/
private theorem adjMk {R : Type} [CommRing R] (x y z t : R) :
    adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 R) =
      !![1, 0, 0, 0; x, 1, 0, 0; y + t * x, t, 1, 0; z, y, -x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev] <;> ring

/- English proof (translation)
Establish `e1` using `congrFun (congrFun h 3) 1`. Establish `e2` using `congrFun (congrFun h 3) 2`. Simplify using `[adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, h1, h2, h3] at e1 e2`. Establish `h31 : w 3 1 = 0`. Break down `e1 with e1 | e1` into its components or cases.

Conclude with `absurd e1 h0`. Conclude with `e1`. Establish `h32 : w 3 2 = 0`. Break down `e2 with e2 | e2` into its components or cases. Conclude with `absurd e2 h0`.

Conclude with `e2`. Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all <;> omega`.
-/
private theorem upOf {k : Type} [Field k] {ν : k} {w : M4 k} (h : IsGSp ν w) (h0 : w 0 0 ≠ 0)
    (h1 : w 1 0 = 0) (h2 : w 2 0 = 0) (h3 : w 3 0 = 0) (h4 : w 2 1 = 0) : IsUp w := by
  have e1 := congrFun (congrFun h 3) 1
  have e2 := congrFun (congrFun h 3) 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, h1, h2, h3] at e1 e2
  have h31 : w 3 1 = 0 := by
    rcases e1 with e1 | e1
    · exact absurd e1 h0
    · exact e1
  have h32 : w 3 2 = 0 := by
    rcases e2 with e2 | e2
    · exact absurd e2 h0
    · exact e2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

/- English proof (translation)
Take `⟨x, hx⟩ : ∃ x : k, x * u 0 0 + u 1 0 = 0` from `⟨-u 1 0 / u 0 0, by field_simp; ring⟩`. Take `⟨t, ht⟩ : ∃ t : k, t * u 1 1 + u 2 1 = 0` from `⟨-u 2 1 / u 1 1, by field_simp; ring⟩`. Take `⟨y, hy⟩ : ∃ y : k, (y + t * x) * u 0 0 + t * u 1 0 + u 2 0 = 0` from `⟨-(t * u 1 0 + u 2 0) / u 0 0 - t * x, by field_simp; ring⟩`. Take `⟨z, hz⟩ : ∃ z : k, z * u 0 0 + y * u 1 0 - x * u 2 0 + u 3 0 = 0` from `⟨(x * u 2 0 - y * u 1 0 - u 3 0) / u 0 0, by field_simp; ring⟩`. Establish `hl` using `lowMk x y z t`.

Use `⟨_, hl, ?_, ?_⟩` and prove the remaining obligations. Establish `hinv : adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k) * !![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] = 1`. Simplify `hl.1` using `[IsGSp]`. Establish `hinv'` using `mul_eq_one_comm.mp hinv`. Establish `hG : IsGSp 1 (adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k))`.

Unfold `IsGSp`. Rewrite using `[(grp k).2.1]`. Simplify using `using hinv'`. Establish `hP` using `(grp k).2.2.2.2.2.2.2.1 1 ν _ _ hG hu`. Rewrite `hP` using `[one_mul]`.

Rewrite `hP`, the goal using `[adjMk]`. Apply `upOf hP` to reduce the goal to its premises. Simplify `h0` using `[Matrix.mul_apply, Fin.sum_univ_four]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four]`. Take the linear combination `hx`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_four]`. Take the linear combination `hy`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four]`. Take the linear combination `hz`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, h01]`.

Take the linear combination `ht`. Introduce `h21`. Establish `: t = 0`. Rewrite `ht` using `[h21, add_zero]`. Break down `mul_eq_zero.mp ht with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h h1`. Simplify using `[this]`.
-/
private theorem core {k : Type} [Field k] {ν : k} {u : M4 k} (hu : IsGSp ν u) (h0 : u 0 0 ≠ 0) (h1 : u 1 1 ≠ 0)
    (h01 : u 0 1 = 0) : ∃ n' : M4 k, IsLow n' ∧ IsUp (adj n' * u) ∧ (u 2 1 = 0 → n' 2 1 = 0) := by
  obtain ⟨x, hx⟩ : ∃ x : k, x * u 0 0 + u 1 0 = 0 :=
    ⟨-u 1 0 / u 0 0, by field_simp; ring⟩
  obtain ⟨t, ht⟩ : ∃ t : k, t * u 1 1 + u 2 1 = 0 :=
    ⟨-u 2 1 / u 1 1, by field_simp; ring⟩
  obtain ⟨y, hy⟩ : ∃ y : k, (y + t * x) * u 0 0 + t * u 1 0 + u 2 0 = 0 :=
    ⟨-(t * u 1 0 + u 2 0) / u 0 0 - t * x, by field_simp; ring⟩
  obtain ⟨z, hz⟩ : ∃ z : k, z * u 0 0 + y * u 1 0 - x * u 2 0 + u 3 0 = 0 :=
    ⟨(x * u 2 0 - y * u 1 0 - u 3 0) / u 0 0, by field_simp; ring⟩
  have hl := lowMk x y z t
  refine ⟨_, hl, ?_, ?_⟩
  · have hinv : adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k) *
        !![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] = 1 := by
      simpa [IsGSp] using hl.1
    have hinv' := mul_eq_one_comm.mp hinv
    have hG : IsGSp 1 (adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k)) := by
      unfold IsGSp
      rw [(grp k).2.1]
      simpa using hinv'
    have hP := (grp k).2.2.2.2.2.2.2.1 1 ν _ _ hG hu
    rw [one_mul] at hP
    rw [adjMk] at hP ⊢
    apply upOf hP
    · simpa [Matrix.mul_apply, Fin.sum_univ_four] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hx
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hy
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hz
    · simp [Matrix.mul_apply, Fin.sum_univ_four, h01]
      linear_combination ht
  · intro h21
    have : t = 0 := by
      rw [h21, add_zero] at ht
      rcases mul_eq_zero.mp ht with h | h
      · exact h
      · exact absurd h h1
    simp [this]

/- English proof (translation)
Introduce `k _ ν X n hν hX hn hS`. Take `⟨hn1, hnd, hnu⟩` from `hn`. Establish `hu : IsGSp ν (X * n)`. Use `(grp k).2.2.2.2.2.2.2.1 ν 1 X n hX hn1` as an intermediate fact. Simplify using `using this`.

Establish `key : X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 0 3 = 0 ∧ X 1 3 = 0 ∧ X 2 3 = 0 ∧ X 1 2 * X 2 1 = 0 ∧ X 1 2 * n 2 1 = 0`. Break down `hS with ⟨hA, hB⟩ | hA` into its components or cases. Use `⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide), hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide), hA 2 3 (by decide) (by decide), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA 2 1 (by decide) (by decide), mul_zero]`. Rewrite using `[hB 2 1 (by decide) (by decide), mul_zero]`.

Use `⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide), hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide), hA 2 3 (by decide) (by decide), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA 1 2 (by decide) (by decide), zero_mul]`. Rewrite using `[hA 1 2 (by decide) (by decide), zero_mul]`. Take `⟨z01, z02, z03, z13, z23, c1, c2⟩` from `key`. Establish `n01 : n 0 1 = 0` using `hnu 0 1 (by decide)`.

Establish `n11 : n 1 1 = 1` using `hnd 1`. Establish `n00 : n 0 0 = 1` using `hnd 0`. Establish `d0` using `congrFun (congrFun hX 0) 0`. Establish `d1` using `congrFun (congrFun hX 1) 1`. Simplify using `[adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, z01, z02, z03, z13, z23] at d0 d1`.

Establish `x00 : X 0 0 ≠ 0`. Introduce `h`. Rewrite `d0` using `[h]`. Simplify using `at d0`. Conclude with `hν d0.symm`.

Establish `x11 : X 1 1 ≠ 0`. Introduce `h`. Apply `hν` to reduce the goal to its premises. Rewrite using `[← d1, h]`. Take the linear combination `-c1`.

Establish `h00 : (X * n) 0 0 ≠ 0`. Simplify `x00` using `[Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n00]`. Establish `h11 : (X * n) 1 1 ≠ 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, z13, n01, n11]`. Rewrite using `[c2, add_zero]`.

Conclude with `x11`. Establish `h01 : (X * n) 0 1 = 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n01]`. Take `⟨n', hl, hup, h21⟩` from `core hu h00 h11 h01`. Use `⟨n', hl, by rwa [← mul_assoc] at hup, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨hA, hB⟩`. Establish `e21 : (X * n) 2 1 = 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, z23, n01, n11, hA 2 1 (by decide) (by decide), hB 2 1 (by decide) (by decide)]`. Establish `m21` using `h21 e21`. Introduce `i j hij hw`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first`. Consider the case `exact absurd rfl hij`. Consider the case `exact hl.2.2 _ _ (by decide)`. Consider the case `exact m21`. Consider the case `exact absurd (by decide) hw`.
-/
theorem UpperTheory.V.Ws.Rt.flagNew :
    ∀ (k : Type) [Field k] (ν : k) (X n : M4 k), ν ≠ 0 → IsGSp ν X → IsLow n → ((SuppM nP X ∧ SuppM qQ n) ∨ SuppM nM X) →
      ∃ n' : M4 k, IsLow n' ∧ IsUp (adj n' * X * n) ∧ (SuppM nP X ∧ SuppM qQ n → SuppM qQ n') := by
  intro k _ ν X n hν hX hn hS
  obtain ⟨hn1, hnd, hnu⟩ := hn
  have hu : IsGSp ν (X * n) := by
    have := (grp k).2.2.2.2.2.2.2.1 ν 1 X n hX hn1
    simpa using this
  have key : X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 0 3 = 0 ∧ X 1 3 = 0 ∧ X 2 3 = 0 ∧
      X 1 2 * X 2 1 = 0 ∧ X 1 2 * n 2 1 = 0 := by
    rcases hS with ⟨hA, hB⟩ | hA
    · refine ⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide),
        hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide),
        hA 2 3 (by decide) (by decide), ?_, ?_⟩
      · rw [hA 2 1 (by decide) (by decide), mul_zero]
      · rw [hB 2 1 (by decide) (by decide), mul_zero]
    · refine ⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide),
        hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide),
        hA 2 3 (by decide) (by decide), ?_, ?_⟩
      · rw [hA 1 2 (by decide) (by decide), zero_mul]
      · rw [hA 1 2 (by decide) (by decide), zero_mul]
  obtain ⟨z01, z02, z03, z13, z23, c1, c2⟩ := key
  have n01 : n 0 1 = 0 := hnu 0 1 (by decide)
  have n11 : n 1 1 = 1 := hnd 1
  have n00 : n 0 0 = 1 := hnd 0
  have d0 := congrFun (congrFun hX 0) 0
  have d1 := congrFun (congrFun hX 1) 1
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, z01, z02, z03, z13, z23] at d0 d1
  have x00 : X 0 0 ≠ 0 := by
    intro h
    rw [h] at d0
    simp at d0
    exact hν d0.symm
  have x11 : X 1 1 ≠ 0 := by
    intro h
    apply hν
    rw [← d1, h]
    linear_combination -c1
  have h00 : (X * n) 0 0 ≠ 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n00] using x00
  have h11 : (X * n) 1 1 ≠ 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z13, n01, n11]
    rw [c2, add_zero]
    exact x11
  have h01 : (X * n) 0 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n01]
  obtain ⟨n', hl, hup, h21⟩ := core hu h00 h11 h01
  refine ⟨n', hl, by rwa [← mul_assoc] at hup, ?_⟩
  rintro ⟨hA, hB⟩
  have e21 : (X * n) 2 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z23, n01, n11, hA 2 1 (by decide) (by decide),
      hB 2 1 (by decide) (by decide)]
  have m21 := h21 e21
  intro i j hij hw
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact hl.2.2 _ _ (by decide)
    | exact m21
    | exact absurd (by decide) hw
