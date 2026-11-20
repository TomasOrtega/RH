import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.HeckeMult

variable {R : Type} [CommRing R]

def CongOne {n : ℕ} (I : Ideal R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I

/- English proof (translation)
Introduce `i j`. Establish `h : (X * Y) i j - (1 : Matrix (Fin n) (Fin n) R) i j = ((X - 1) * Y) i j + (Y i j - (1 : Matrix (Fin n) (Fin n) R) i j)`. Establish `h0 : X * Y - 1 = (X - 1) * Y + (Y - 1)` using `by noncomm_ring`. Establish `h1` using `congrFun (congrFun h0 i) j`. Simplify using `using h1`.

Rewrite using `[h]`. Use `I.add_mem ?_ (hY i j)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `I.sum_mem fun k _ => I.mul_mem_right _ (by simpa using hX i k)`.
-/
theorem CongOne.mul {n : ℕ} {I : Ideal R} {X Y : Matrix (Fin n) (Fin n) R}
    (hX : CongOne I X) (hY : CongOne I Y) : CongOne I (X * Y) := by
  intro i j
  have h : (X * Y) i j - (1 : Matrix (Fin n) (Fin n) R) i j
      = ((X - 1) * Y) i j + (Y i j - (1 : Matrix (Fin n) (Fin n) R) i j) := by
    have h0 : X * Y - 1 = (X - 1) * Y + (Y - 1) := by noncomm_ring
    have h1 := congrFun (congrFun h0 i) j
    simpa using h1
  rw [h]
  refine I.add_mem ?_ (hY i j)
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (by simpa using hX i k)

def bordered {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
  Fin.lastCases (motive := fun _ => R)
    (Fin.lastCases (motive := fun _ => R) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => R) (c i') (M i') j) i

section bordered
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)

/- English proof (translation)
Simplify using `[bordered]`.
-/
@[simp] theorem bordered_cc (i j : Fin n) :
    bordered M c r d i.castSucc j.castSucc = M i j := by simp [bordered]
/- English proof (translation)
Simplify using `[bordered]`.
-/
@[simp] theorem bordered_cl (i : Fin n) :
    bordered M c r d i.castSucc (Fin.last n) = c i := by simp [bordered]
/- English proof (translation)
Simplify using `[bordered]`.
-/
@[simp] theorem bordered_lc (j : Fin n) :
    bordered M c r d (Fin.last n) j.castSucc = r j := by simp [bordered]
/- English proof (translation)
Simplify using `[bordered]`.
-/
@[simp] theorem bordered_ll :
    bordered M c r d (Fin.last n) (Fin.last n) = d := by simp [bordered]
end bordered

/- English proof (translation)
Simplify using `[Matrix.one_apply]`.
-/
theorem one_cc {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc j.castSucc
      = (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [Matrix.one_apply]

/- English proof (translation)
The claim follows from `Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne`.
-/
theorem one_cl {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc (Fin.last n) = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne

/- English proof (translation)
The claim follows from `Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne'`.
-/
theorem one_lc {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) i.castSucc = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne'

/- English proof (translation)
Introduce `i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa using hd`.

Consider the case `cast j => simpa [one_lc] using hr j`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa [one_cl] using hc i`. Consider the case `cast j => simpa [one_cc] using hM i j`.
-/
theorem CongOne.bordered {n : ℕ} {I : Ideal R} {M : Matrix (Fin n) (Fin n) R}
    {c r : Fin n → R} {d : R} (hM : CongOne I M) (hc : ∀ i, c i ∈ I) (hr : ∀ i, r i ∈ I)
    (hd : d - 1 ∈ I) : CongOne I (bordered M c r d) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa using hd
    | cast j => simpa [one_lc] using hr j
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [one_cl] using hc i
    | cast j => simpa [one_cc] using hM i j

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _`. Conclude with `⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩`. Consider the case `succ n ih`.

Introduce `A hA`. Establish `hs1 : A (Fin.last n) (Fin.last n) - 1 ∈ I`. Simplify using `using hA (Fin.last n) (Fin.last n)`. Take `⟨t, hst⟩` from `(hI _ hs1).exists_right_inv`. Establish `hq : ∀ i : Fin n, A i.castSucc (Fin.last n) ∈ I` using `fun i => by`.

Simplify `hA i.castSucc (Fin.last n)` using `[one_cl]`. Establish `hr : ∀ j : Fin n, A (Fin.last n) j.castSucc ∈ I` using `fun j => by`. Simplify `hA (Fin.last n) j.castSucc` using `[one_lc]`. Set `P : Matrix (Fin n) (Fin n) R` to `fun i j => A i.castSucc j.castSucc - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc`. Establish `hP : CongOne I P`.

Introduce `i j`. Establish `h1` using `hA i.castSucc j.castSucc`. Rewrite `h1` using `[one_cc]`. Establish `h2 : A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc ∈ I` using `I.mul_mem_left _ (hr j)`. Establish `: P i j - (1 : Matrix (Fin n) (Fin n) R) i j = (A i.castSucc j.castSucc - (1 : Matrix (Fin n) (Fin n) R) i j) - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc`.

Simplify using `only [P]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `I.sub_mem h1 h2`. Take `⟨U', L', hU', hL', hUt, hLt, hUL⟩` from `ih P hP`.

Use `⟨bordered U' (fun i => A i.castSucc (Fin.last n) * t) 0 1, bordered L' 0 (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)), hU'.bordered (fun i => I.mul_mem_right _ (hq i)) (fun _ => I.zero_mem) (by simp), hL'.bordered (fun _ => I.zero_mem) hr hs1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => exact absurd hij (lt_irrefl _)`. Consider the case `cast j => simp`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)`.

Consider the case `cast j => simpa using hUt i j (by simpa using hij)`. Introduce `i j hij`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => exact absurd hij (lt_irrefl _)`. Consider the case `cast j => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last j).le)`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp`.

Consider the case `cast j => simpa using hLt i j (by simpa using hij)`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_castSucc]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp`. Consider the case `cast j => simp`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last`. Simplify using `only [bordered_cc, bordered_cl, bordered_ll, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]`. Rewrite using `[mul_assoc, mul_comm t, hst, mul_one]`. Consider the case `cast j`. Simplify using `only [bordered_cc, bordered_cl, bordered_lc]`.

Establish `h` using `congrFun (congrFun hUL i) j`. Rewrite `h` using `[Matrix.mul_apply]`. Rewrite using `[← h]`. Simplify using `only [P]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_upper_lower (I : Ideal R) (hI : ∀ s : R, s - 1 ∈ I → IsUnit s) (n : ℕ) :
    ∀ A : Matrix (Fin n) (Fin n) R, CongOne I A →
      ∃ U L : Matrix (Fin n) (Fin n) R, CongOne I U ∧ CongOne I L ∧
        (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → L i j = 0) ∧ A = U * L := by
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    have hs1 : A (Fin.last n) (Fin.last n) - 1 ∈ I := by
      simpa using hA (Fin.last n) (Fin.last n)
    obtain ⟨t, hst⟩ := (hI _ hs1).exists_right_inv
    have hq : ∀ i : Fin n, A i.castSucc (Fin.last n) ∈ I := fun i => by
      simpa [one_cl] using hA i.castSucc (Fin.last n)
    have hr : ∀ j : Fin n, A (Fin.last n) j.castSucc ∈ I := fun j => by
      simpa [one_lc] using hA (Fin.last n) j.castSucc
    let P : Matrix (Fin n) (Fin n) R := fun i j =>
      A i.castSucc j.castSucc - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc
    have hP : CongOne I P := by
      intro i j
      have h1 := hA i.castSucc j.castSucc
      rw [one_cc] at h1
      have h2 : A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc ∈ I :=
        I.mul_mem_left _ (hr j)
      have : P i j - (1 : Matrix (Fin n) (Fin n) R) i j
          = (A i.castSucc j.castSucc - (1 : Matrix (Fin n) (Fin n) R) i j)
            - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc := by
        simp only [P]; ring
      rw [this]
      exact I.sub_mem h1 h2
    obtain ⟨U', L', hU', hL', hUt, hLt, hUL⟩ := ih P hP
    refine ⟨bordered U' (fun i => A i.castSucc (Fin.last n) * t) 0 1,
      bordered L' 0 (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)),
      hU'.bordered (fun i => I.mul_mem_right _ (hq i)) (fun _ => I.zero_mem) (by simp),
      hL'.bordered (fun _ => I.zero_mem) hr hs1, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
        | cast j => simpa using hUt i j (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last j).le)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hLt i j (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [bordered_cc, bordered_cl, bordered_ll, Pi.zero_apply, mul_zero,
            Finset.sum_const_zero, zero_add]
          rw [mul_assoc, mul_comm t, hst, mul_one]
        | cast j =>
          simp only [bordered_cc, bordered_cl, bordered_lc]
          have h := congrFun (congrFun hUL i) j
          rw [Matrix.mul_apply] at h
          rw [← h]
          simp only [P]; ring

section conj
variable {K : Type} [Field K] [Algebra R K]

/- English proof (translation)
Use `⟨Matrix.of fun i j => U i j * ϖ ^ (a i - a j).toNat, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Matrix.of_apply]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[Matrix.one_apply_ne h.ne, sub_zero]`.

Use `hU i j` as an intermediate fact. Rewrite `this` using `[Matrix.one_apply_ne h.ne, sub_zero]`. Conclude with `I.mul_mem_right _ this`. Substitute `h` using the available equality. Simplify using `using hU i i`.

Rewrite using `[Matrix.one_apply_ne h.ne', sub_zero, hUt i j h, zero_mul]`. Conclude with `I.zero_mem`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]`.

Break down `lt_or_ge j i with h | h` into its components or cases. Simplify using `[hUt i j h]`. Establish `hnn : 0 ≤ a i - a j` using `sub_nonneg.mpr (ha h)`. Establish `: (algebraMap R K ϖ) ^ (a i) = (algebraMap R K ϖ) ^ (a i - a j).toNat * (algebraMap R K ϖ) ^ (a j)`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_upper {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (a : Fin n → ℤ)
    (ha : Antitone a) (U : Matrix (Fin n) (Fin n) R) (hU : CongOne I U)
    (hUt : ∀ i j, j < i → U i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) * U.map (algebraMap R K)
        = V.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) := by
  refine ⟨Matrix.of fun i j => U i j * ϖ ^ (a i - a j).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero]
      have := hU i j
      rw [Matrix.one_apply_ne h.ne, sub_zero] at this
      exact I.mul_mem_right _ this
    · subst h
      simpa using hU i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero, hUt i j h, zero_mul]
      exact I.zero_mem
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge j i with h | h
    · simp [hUt i j h]
    · have hnn : 0 ≤ a i - a j := sub_nonneg.mpr (ha h)
      have : (algebraMap R K ϖ) ^ (a i) = (algebraMap R K ϖ) ^ (a i - a j).toNat * (algebraMap R K ϖ) ^ (a j) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring

/- English proof (translation)
Use `⟨Matrix.of fun i j => L i j * ϖ ^ (b j - b i).toNat, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Matrix.of_apply]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[Matrix.one_apply_ne h.ne, sub_zero, hLt i j h, zero_mul]`.

Conclude with `I.zero_mem`. Substitute `h` using the available equality. Simplify using `using hL i i`. Rewrite using `[Matrix.one_apply_ne h.ne', sub_zero]`. Use `hL i j` as an intermediate fact.

Rewrite `this` using `[Matrix.one_apply_ne h.ne', sub_zero]`. Conclude with `I.mul_mem_right _ this`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]`.

Break down `lt_or_ge i j with h | h` into its components or cases. Simplify using `[hLt i j h]`. Establish `hnn : 0 ≤ b j - b i` using `sub_nonneg.mpr (hb h)`. Establish `: (algebraMap R K ϖ) ^ (b j) = (algebraMap R K ϖ) ^ (b j - b i).toNat * (algebraMap R K ϖ) ^ (b i)`. Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_lower {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (b : Fin n → ℤ)
    (hb : Antitone b) (L : Matrix (Fin n) (Fin n) R) (hL : CongOne I L)
    (hLt : ∀ i j, i < j → L i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      L.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i))
        = Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i)) * V.map (algebraMap R K) := by
  refine ⟨Matrix.of fun i j => L i j * ϖ ^ (b j - b i).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero, hLt i j h, zero_mul]
      exact I.zero_mem
    · subst h
      simpa using hL i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      have := hL i j
      rw [Matrix.one_apply_ne h.ne', sub_zero] at this
      exact I.mul_mem_right _ this
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge i j with h | h
    · simp [hLt i j h]
    · have hnn : 0 ≤ b j - b i := sub_nonneg.mpr (hb h)
      have : (algebraMap R K ϖ) ^ (b j) = (algebraMap R K ϖ) ^ (b j - b i).toNat * (algebraMap R K ϖ) ^ (b i) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring

end conj

end GlobalTheory.CompanionTheory.HeckeMult
