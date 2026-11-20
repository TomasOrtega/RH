import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame.SignWord

variable {n : ℕ}

def sg (b : Bool) : ℤ := cond b 1 (-1)

/- English proof (translation)
Apply the tactic sequence `cases b <;> simp [sg]`.
-/
theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

/- English proof (translation)
Apply the tactic sequence `cases a <;> cases b <;> cases c <;> cases e <;> simp_all [Xor', sg, pow_succ]`.
-/
theorem step_sign (a b c e : Bool) (k : ℕ) (h : Xor' (a = b) (c = e)) :
    sg c * sg a * (-1 : ℤ) ^ k = sg e * sg b * (-1 : ℤ) ^ (k + 1) := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all [Xor', sg, pow_succ]

/- English proof (translation)
Break down `Nat.even_or_odd k with hk | hk` into its components or cases. Apply the tactic sequence `cases b <;> simp_all [sg, hk.neg_one_pow]`. Establish `hk' : ¬ Even k` using `Nat.not_even_iff_odd.2 hk`. Apply the tactic sequence `cases b <;> simp_all [sg, hk.neg_one_pow]`.
-/
theorem sign_left (b : Bool) (k : ℕ) (h : sg b * sg true * (-1 : ℤ) ^ k = 1) :
    b = true ↔ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

/- English proof (translation)
Break down `Nat.even_or_odd k with hk | hk` into its components or cases. Apply the tactic sequence `cases b <;> simp_all [sg, hk.neg_one_pow]`. Establish `hk' : ¬ Even k` using `Nat.not_even_iff_odd.2 hk`. Apply the tactic sequence `cases b <;> simp_all [sg, hk.neg_one_pow]`.
-/
theorem sign_right (b : Bool) (k : ℕ) (h : sg b * sg false * (-1 : ℤ) ^ k = 1) :
    b = true ↔ ¬ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]`. Establish `h : (-1 : ℤ) ^ (2 * k + 1) = -1` using `(odd_two_mul_add_one k).neg_one_pow`.

Establish `h' : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1` using `by rw [pow_succ, h]; norm_num`. Rewrite using `[h, h']`. Evaluate the numerical expressions.
-/
theorem sum_neg_one_pow (n : ℕ) : ∑ p ∈ range (2 * n + 1), (-1 : ℤ) ^ p = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h : (-1 : ℤ) ^ (2 * k + 1) = -1 := (odd_two_mul_add_one k).neg_one_pow
    have h' : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by rw [pow_succ, h]; norm_num
    rw [h, h']; norm_num

/- English proof (translation)
Unfold `above`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Use `(Finset.ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [mem_filter, mem_univ, true_and] at hz ⊢`.

Conclude with `h.trans hz`. Simplify using `using h`. Simplify using the standard rewrite rules.
-/
theorem above_lt_of_lt (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) {r : ℝ}
    (x : Fin (n + 1) ⊕ Fin n) (h : r < Sum.elim d d' x) :
    above d d' (Sum.elim d d' x) < above d d' r := by
  unfold above
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact h.trans hz
  · simpa using h
  · simp

/- English proof (translation)
Establish `h : above d d' (Sum.elim d d' x) < (univ : Finset (Fin (n + 1) ⊕ Fin n)).card`. Unfold `above`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Conclude with `Finset.filter_ssubset.2 ⟨x, mem_univ _, by simp⟩`. Establish `h2 : (univ : Finset (Fin (n + 1) ⊕ Fin n)).card = 2 * n + 1`.

Simplify using `[Finset.card_univ, Fintype.card_sum]`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.
-/
theorem above_lt_card (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (x : Fin (n + 1) ⊕ Fin n) :
    above d d' (Sum.elim d d' x) < 2 * n + 1 := by
  have h : above d d' (Sum.elim d d' x) < (univ : Finset (Fin (n + 1) ⊕ Fin n)).card := by
    unfold above
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.2 ⟨x, mem_univ _, by simp⟩
  have h2 : (univ : Finset (Fin (n + 1) ⊕ Fin n)).card = 2 * n + 1 := by
    simp [Finset.card_univ, Fintype.card_sum]; ring
  omega

/- English proof (translation)
Introduce `x y hxy`. Simplify using `only at hxy`. Break down `lt_trichotomy (Sum.elim d d' x) (Sum.elim d d' y) with h | h | h` into its components or cases. Use `above_lt_of_lt d d' y h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `hv h`. Use `above_lt_of_lt d d' x h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem above_injective (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    Function.Injective fun x => above d d' (Sum.elim d d' x) := by
  intro x y hxy
  simp only at hxy
  rcases lt_trichotomy (Sum.elim d d' x) (Sum.elim d d' y) with h | h | h
  · have := above_lt_of_lt d d' y h
    omega
  · exact hv h
  · have := above_lt_of_lt d d' x h
    omega

/- English proof (translation)
Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `p hp`. Take `⟨x, -, rfl⟩` from `mem_image.1 hp`. Conclude with `mem_range.2 (above_lt_card d d' x)`. Rewrite using `[Finset.card_image_of_injective _ (above_injective d d' hv)]`.

Simplify using `[Finset.card_univ, Fintype.card_sum]`. Use linear arithmetic over natural numbers and integers.
-/
theorem above_image (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    (univ : Finset (Fin (n + 1) ⊕ Fin n)).image (fun x => above d d' (Sum.elim d d' x)) =
      range (2 * n + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.1 hp
    exact mem_range.2 (above_lt_card d d' x)
  · rw [Finset.card_image_of_injective _ (above_injective d d' hv)]
    simp [Finset.card_univ, Fintype.card_sum]
    omega

/- English proof (translation)
Establish `h` using `sum_neg_one_pow n`. Rewrite `h` using `[← above_image d d' hv, Finset.sum_image (fun x _ y _ h => above_injective d d' hv h)]`. Conclude with `h`.
-/
theorem sum_above (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    ∑ x : Fin (n + 1) ⊕ Fin n, (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = 1 := by
  have h := sum_neg_one_pow n
  rw [← above_image d d' hv,
    Finset.sum_image (fun x _ y _ h => above_injective d d' hv h)] at h
  exact h

/- English proof (translation)
Rewrite using `[Fintype.sum_sum_type]`. Establish `h1 : ∑ i, sg (ε i) = ∑ a, sg (ε' a) + 1`. Rewrite using `[← Equiv.sum_comp e, Fintype.sum_sum_type]`. Establish `h0 : sg (ε (e (Sum.inr ()))) = 1`. Establish `: ε (e (Sum.inr ())) = true` using `hf.1`.

Simplify using `[this, sg]`. Simplify using `[hf.2, h0]`. Establish `hl : sg true = 1` using `rfl`. Establish `hr : sg false = -1` using `rfl`. Simplify using `[hl, hr, h1]`.
-/
theorem sum_signs (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e) :
    ∑ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft = 1 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i, sg (ε i) = ∑ a, sg (ε' a) + 1 := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    have h0 : sg (ε (e (Sum.inr ()))) = 1 := by
      have : ε (e (Sum.inr ())) = true := hf.1
      simp [this, sg]
    simp [hf.2, h0]
  have hl : sg true = 1 := rfl
  have hr : sg false = -1 := rfl
  simp [hl, hr, h1]

/- English proof (translation)
Establish `hlt : Sum.elim d d' y < Sum.elim d d' x`. Break down `lt_trichotomy (Sum.elim d d' y) (Sum.elim d d' x) with h | h | h` into its components or cases. Conclude with `h`. Rewrite `hxy` using `[h]`. Use linear arithmetic over natural numbers and integers.

Use `above_lt_of_lt d d' y h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hno : ∀ z, ¬ (Sum.elim d d' y < Sum.elim d d' z ∧ Sum.elim d d' z < Sum.elim d d' x)`. Introduce and unpack `z ⟨h1, h2⟩`. Establish `a1` using `above_lt_of_lt d d' z h1`.

Establish `a2` using `above_lt_of_lt d d' x h2`. Use linear arithmetic over natural numbers and integers. Use `hw x y hlt hno` as an intermediate fact. Rewrite using `[hxy]`. Conclude with `step_sign _ _ _ _ _ (by`.

Break down `this with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Conclude with `Or.inl ⟨h1, h2⟩`. Conclude with `Or.inr ⟨h1, h2⟩)`.
-/
theorem step_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') (x y : Fin (n + 1) ⊕ Fin n)
    (hxy : above d d' (Sum.elim d d' y) = above d d' (Sum.elim d d' x) + 1) :
    sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
      sg (Sum.elim ε ε' y) * sg y.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' y) := by
  have hlt : Sum.elim d d' y < Sum.elim d d' x := by
    rcases lt_trichotomy (Sum.elim d d' y) (Sum.elim d d' x) with h | h | h
    · exact h
    · rw [h] at hxy; omega
    · have := above_lt_of_lt d d' y h
      omega
  have hno : ∀ z, ¬ (Sum.elim d d' y < Sum.elim d d' z ∧ Sum.elim d d' z < Sum.elim d d' x) := by
    rintro z ⟨h1, h2⟩
    have a1 := above_lt_of_lt d d' z h1
    have a2 := above_lt_of_lt d d' x h2
    omega
  have := hw x y hlt hno
  rw [hxy]
  exact step_sign _ _ _ _ _ (by
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩)

/- English proof (translation)
Establish `him` using `above_image d d' hv`. Establish `hsurj : ∀ p < 2 * n + 1, ∃ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p`. Introduce `p hp`. Establish `: p ∈ (univ : Finset (Fin (n + 1) ⊕ Fin n)).image (fun x => above d d' (Sum.elim d d' x))`. Rewrite using `[him]`.

Conclude with `mem_range.2 hp`. Take `⟨x, -, hx⟩` from `mem_image.1 this`. Conclude with `⟨x, hx⟩`. Take `⟨x0, hx0⟩` from `hsurj 0 (by omega)`. Use `⟨sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0), ?_⟩` and prove the remaining obligations.

Establish `key : ∀ p : ℕ, ∀ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p → sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0)`. Introduce `p`. Proceed by induction on `p with`. Consider the case `zero`. Introduce `x hx`.

Establish `: x = x0` using `above_injective d d' hv (by simp only [hx, hx0])`. Rewrite using `[this]`. Consider the case `succ k ih`. Introduce `x hx`. Establish `hk : k < 2 * n + 1`.

Use `above_lt_card d d' x` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨y, hy⟩` from `hsurj k hk`. Rewrite using `[← ih y hy]`. Conclude with `(step_letters ε d ε' d' hv hw y x (by rw [hx, hy])).symm`.

Conclude with `fun x => key _ x rfl`.
-/
theorem const_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    ∃ T : ℤ, ∀ x : Fin (n + 1) ⊕ Fin n,
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = T := by
  have him := above_image d d' hv
  have hsurj : ∀ p < 2 * n + 1, ∃ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p := by
    intro p hp
    have : p ∈ (univ : Finset (Fin (n + 1) ⊕ Fin n)).image
        (fun x => above d d' (Sum.elim d d' x)) := by
      rw [him]; exact mem_range.2 hp
    obtain ⟨x, -, hx⟩ := mem_image.1 this
    exact ⟨x, hx⟩
  obtain ⟨x0, hx0⟩ := hsurj 0 (by omega)
  refine ⟨sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0), ?_⟩
  have key : ∀ p : ℕ, ∀ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p →
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
        sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0) := by
    intro p
    induction p with
    | zero =>
      intro x hx
      have : x = x0 := above_injective d d' hv (by simp only [hx, hx0])
      rw [this]
    | succ k ih =>
      intro x hx
      have hk : k < 2 * n + 1 := by
        have := above_lt_card d d' x
        omega
      obtain ⟨y, hy⟩ := hsurj k hk
      rw [← ih y hy]
      exact (step_letters ε d ε' d' hv hw y x (by rw [hx, hy])).symm
  exact fun x => key _ x rfl

/- English proof (translation)
Take `⟨T, hT⟩` from `const_letters ε d ε' d' hv hw`. Establish `hsum : T = 1`. Establish `h1 : ∀ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft = T * (-1 : ℤ) ^ above d d' (Sum.elim d d' x)`. Introduce `x`. Rewrite using `[← hT x]`.

Establish `hp : ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) * ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Rewrite using `[mul_assoc, hp, mul_one]`. Establish `h2` using `sum_signs ε ε' e hf`.

Rewrite `h2` using `[h1]`. Rewrite `h2` using `[← Finset.mul_sum, sum_above d d' hv]`. Simplify using `using h2`. Substitute `hsum` using the available equality. Use `⟨fun i => sign_left _ _ (by simpa using hT (Sum.inl i)), fun j => sign_right _ _ (by simpa using hT (Sum.inr j))⟩` and prove the remaining obligations.
-/
theorem heSign (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e)
    (hv : Function.Injective (Sum.elim d d')) (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧
      ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  obtain ⟨T, hT⟩ := const_letters ε d ε' d' hv hw
  have hsum : T = 1 := by
    have h1 : ∀ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft =
        T * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) := by
      intro x
      rw [← hT x]
      have hp : ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) *
          ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) = 1 := by
        rw [← mul_pow]; simp
      rw [mul_assoc, hp, mul_one]
    have h2 := sum_signs ε ε' e hf
    simp_rw [h1] at h2
    rw [← Finset.mul_sum, sum_above d d' hv] at h2
    simpa using h2
  subst hsum
  refine ⟨fun i => sign_left _ _ (by simpa using hT (Sum.inl i)),
    fun j => sign_right _ _ (by simpa using hT (Sum.inr j))⟩

end GlobalTheory.CompanionTheory.RgHeFrame.SignWord
