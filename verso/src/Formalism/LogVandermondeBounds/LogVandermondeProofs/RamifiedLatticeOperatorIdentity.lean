import Formalism.LogVandermondeBounds.FinrankFiberSumZero

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section SlopeTestRemainingChoices

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]

/- English proof (translation)
Unfold `pair`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.
-/
lemma pair_comm (f x : Fin r → k) : pair f x = pair x f := by
  unfold pair; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/- English proof (translation)
Unfold `pair`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun i _ => by simp [mul_assoc])`.
-/
lemma pair_smul_left (c : k) (f x : Fin r → k) : pair (c • f) x = c * pair f x := by
  unfold pair; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [mul_assoc])

/- English proof (translation)
Rewrite using `[pair_comm, pair_smul_left, pair_comm]`.
-/
lemma pair_smul_right (c : k) (f x : Fin r → k) : pair f (c • x) = c * pair f x := by
  rw [pair_comm, pair_smul_left, pair_comm]

/- English proof (translation)
Simplify using `[pair]`.
-/
lemma pair_zero_right (f : Fin r → k) : pair f 0 = 0 := by simp [pair]

/- English proof (translation)
Simplify using `[pair, add_mul, Finset.sum_add_distrib]`.
-/
lemma pair_add_left (f g x : Fin r → k) : pair (f + g) x = pair f x + pair g x := by
  simp [pair, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `pair`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_apply, hj]`.

Simplify using the standard rewrite rules.
-/
lemma pair_single_left (i : Fin r) (t : k) (x : Fin r → k) :
    pair (Pi.single i t) x = t * x i := by
  unfold pair
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

/- English proof (translation)
Introduce and unpack `rfl`. Rewrite `h` using `[pair_zero_right]`. Conclude with `zero_ne_one h`.
-/
lemma ne_zero_of_pair_eq_one {f x : Fin r → k} (h : pair f x = 1) : x ≠ 0 := by
  rintro rfl; rw [pair_zero_right] at h; exact zero_ne_one h

/- English proof (translation)
Use function extensionality and compare the values at `f`. Unfold `opU opD`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Rewrite using `[pair_comm]`.
-/
lemma opU_eq_opD (ψ : (Fin r → k) → R) : opU ψ = opD ψ := by
  funext f
  unfold opU opD
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pair_comm]

/- English proof (translation)
Use function extensionality and compare the values at `f`. Unfold `nmP nmV diaP diaV`. Conclude with `(Fintype.sum_equiv (Equiv.inv kˣ) (fun c => φ (((c⁻¹ : kˣ) : k) • f)) (fun c => φ ((c : k) • f)) (fun c => rfl)).symm`.
-/
lemma nmP_eq_nmV (φ : (Fin r → k) → R) : nmP φ = nmV φ := by
  funext f
  unfold nmP nmV diaP diaV
  exact (Fintype.sum_equiv (Equiv.inv kˣ) (fun c => φ (((c⁻¹ : kˣ) : k) • f))
    (fun c => φ ((c : k) • f)) (fun c => rfl)).symm

/- English proof (translation)
Use function extensionality and compare the values at `f`. Unfold `opU diaV diaP`. Use `Finset.sum_nbij' (fun x => ((c⁻¹ : kˣ) : k) • x) (fun y => (c : k) • y) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢`.

Rewrite using `[pair_smul_left, pair_smul_right, hx, mul_one]`. Conclude with `c.mul_inv`. Introduce `y hy`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢`. Rewrite using `[pair_smul_right, ← pair_smul_left]`.

Conclude with `hy`. Introduce `x _`. Simplify using `only [smul_smul, c.mul_inv, one_smul]`. Introduce `y _`. Simplify using `only [smul_smul, c.inv_mul, one_smul]`.

Introduce `x _`. Both sides reduce to the same expression.
-/
lemma comm_U (c : kˣ) (ψ : (Fin r → k) → R) : opU (diaV c ψ) = diaP c (opU ψ) := by
  funext f
  unfold opU diaV diaP
  refine Finset.sum_nbij' (fun x => ((c⁻¹ : kˣ) : k) • x) (fun y => (c : k) • y) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [pair_smul_left, pair_smul_right, hx, mul_one]; exact c.mul_inv
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [pair_smul_right, ← pair_smul_left]; exact hy
  · intro x _; simp only [smul_smul, c.mul_inv, one_smul]
  · intro y _; simp only [smul_smul, c.inv_mul, one_smul]
  · intro x _; rfl

/- English proof (translation)
The claim follows from `congrFun (comm_U c ψ) f`.
-/
lemma comm_U_apply (c : kˣ) (ψ : (Fin r → k) → R) (f : Fin r → k) :
    opU (diaV c ψ) f = diaP c (opU ψ) f := congrFun (comm_U c ψ) f

/- English proof (translation)
Unfold `nmP`. Simplify using `only [← comm_U_apply]`. Unfold `opU nmV`. Conclude with `Finset.sum_comm`.
-/
lemma nmP_opU (ψ : (Fin r → k) → R) (f : Fin r → k) :
    nmP (opU ψ) f = ∑ x ∈ univ.filter (fun x => pair f x = 1), nmV ψ x := by
  unfold nmP
  simp only [← comm_U_apply]
  unfold opU nmV
  exact Finset.sum_comm

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`.
-/
lemma exists_coord_ne_zero {x : Fin r → k} (hx : x ≠ 0) : ∃ i, x i ≠ 0 := by
  by_contra h
  push_neg at h
  exact hx (funext h)

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_coord_ne_zero hx`. Unfold `nmV diaV`. Rewrite using `[Finset.sum_image]`. Introduce `c _ d _ h`. Establish `h'` using `congrFun h i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul] at h'`. Establish `h'' : ((c⁻¹ : kˣ) : k) = ((d⁻¹ : kˣ) : k)` using `mul_right_cancel₀ hi h'`. Conclude with `inv_inj.1 (Units.ext h'')`.
-/
lemma nmV_eq_image (ψ : (Fin r → k) → R) {x : Fin r → k} (hx : x ≠ 0) :
    nmV ψ x = ∑ y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x), ψ y := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
  unfold nmV diaV
  rw [Finset.sum_image]
  intro c _ d _ h
  have h' := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at h'
  have h'' : ((c⁻¹ : kˣ) : k) = ((d⁻¹ : kˣ) : k) := mul_right_cancel₀ hi h'
  exact inv_inj.1 (Units.ext h'')

/- English proof (translation)
Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩; exact ⟨c⁻¹, by rw [Units.smul_def]⟩`. Introduce and unpack `⟨u, rfl⟩; exact ⟨u⁻¹, by rw [inv_inv, Units.smul_def]⟩`.
-/
lemma mem_image_orbit {x : Fin r → k} (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ ∃ u : kˣ, u • x = y := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c⁻¹, by rw [Units.smul_def]⟩
  · rintro ⟨u, rfl⟩; exact ⟨u⁻¹, by rw [inv_inv, Units.smul_def]⟩

/- English proof (translation)
Rewrite using `[mem_image_orbit]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Use `⟨?_, ⟨(u : k), Units.smul_def u x⟩⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Establish `h1` using `congrArg (fun z => ((u⁻¹ : kˣ) : k) • z) h0`. Simplify using `only [smul_zero] at h1`. Rewrite `h1` using `[Units.smul_def, smul_smul, u.inv_mul, one_smul]`. Conclude with `h1`.

Introduce and unpack `⟨hy, c, rfl⟩`. Establish `hc : c ≠ 0` using `by rintro rfl; exact hy (zero_smul _ _)`. Conclude with `⟨Units.mk0 c hc, by rw [Units.smul_def, Units.val_mk0]⟩`.
-/
lemma mem_image_line {x : Fin r → k} (hx : x ≠ 0) (y : Fin r → k) :
    y ∈ univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x) ↔ y ≠ 0 ∧ ∃ c : k, y = c • x := by
  rw [mem_image_orbit]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ⟨(u : k), Units.smul_def u x⟩⟩
    intro h0
    apply hx
    have h1 := congrArg (fun z => ((u⁻¹ : kˣ) : k) • z) h0
    simp only [smul_zero] at h1
    rw [Units.smul_def, smul_smul, u.inv_mul, one_smul] at h1
    exact h1
  · rintro ⟨hy, c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; exact hy (zero_smul _ _)
    exact ⟨Units.mk0 c hc, by rw [Units.smul_def, Units.val_mk0]⟩

/- English proof (translation)
Set `π : (Fin r → k) → Quotient (MulAction.orbitRel kˣ (Fin r → k))` to `Quotient.mk _`. Unfold `trV`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := π) (t := (univ.filter (fun x : Fin r → k => x ≠ 0)).image π) (fun x hx => Finset.mem_image_of_mem π hx)]`. Use `Finset.sum_eq_zero (fun j hj => ?_)` and prove the remaining obligations. Take `⟨x0, hx0, rfl⟩` from `Finset.mem_image.1 hj`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0`. Establish `hfib : (univ.filter (fun x : Fin r → k => x ≠ 0)).filter (fun x => π x = π x0) = univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x0)`. Use extensionality with `y`. Rewrite using `[mem_image_orbit]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, π, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, hu⟩`. Conclude with `hu`. Introduce and unpack `⟨u, rfl⟩`. Use `⟨?_, ⟨u, rfl⟩⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hx0` to reduce the goal to its premises. Establish `h1` using `congrArg (fun z => u⁻¹ • z) h0`. Simplify using `only [smul_zero, smul_smul, inv_mul_cancel, one_smul] at h1`. Conclude with `h1`.

Rewrite using `[hfib, ← nmV_eq_image ψ hx0]`. Conclude with `h x0 hx0`.
-/
lemma trV_eq_zero (ψ : (Fin r → k) → R) (h : ∀ y, y ≠ 0 → nmV ψ y = 0) : trV ψ = 0 := by
  classical
  let π : (Fin r → k) → Quotient (MulAction.orbitRel kˣ (Fin r → k)) := Quotient.mk _
  unfold trV
  rw [← Finset.sum_fiberwise_of_maps_to (g := π)
    (t := (univ.filter (fun x : Fin r → k => x ≠ 0)).image π)
    (fun x hx => Finset.mem_image_of_mem π hx)]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0
  have hfib : (univ.filter (fun x : Fin r → k => x ≠ 0)).filter (fun x => π x = π x0) =
      univ.image (fun c : kˣ => ((c⁻¹ : kˣ) : k) • x0) := by
    ext y
    rw [mem_image_orbit]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, π, Quotient.eq,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨_, hu⟩
      exact hu
    · rintro ⟨u, rfl⟩
      refine ⟨?_, ⟨u, rfl⟩⟩
      intro h0
      apply hx0
      have h1 := congrArg (fun z => u⁻¹ • z) h0
      simp only [smul_zero, smul_smul, inv_mul_cancel, one_smul] at h1
      exact h1
  rw [hfib, ← nmV_eq_image ψ hx0]
  exact h x0 hx0

/- English proof (translation)
Establish `hfib : ∀ w, (univ.filter (fun f => L f = w)).card = (univ.filter (fun f => L f = 0)).card`. Introduce `w`. Take `⟨f0, hf0⟩` from `hL w`. Use `Finset.card_nbij' (fun f => f - f0) (fun f => f + f0) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `f hf`.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢`. Rewrite using `[map_sub, hf, hf0, sub_self]`. Introduce `f hf`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢`. Rewrite using `[map_add, hf, hf0, zero_add]`.

Introduce `f _`. Simplify using the standard rewrite rules. Introduce `f _`. Simplify using the standard rewrite rules. Establish `htot` using `Finset.card_eq_sum_card_fiberwise (f := L) (s := (univ : Finset (Fin r → k))) (t := univ) (fun _ _ => Finset.mem_univ _)`.

Rewrite `htot` using `[Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, smul_eq_mul]`. Establish `hcard : Fintype.card (Fin r → k) = Fintype.card k ^ r` using `by simp`. Rewrite `htot` using `[Finset.card_univ, Finset.card_univ]`. Rewrite using `[hfib w, ← hcard, htot, Nat.mul_comm]`.
-/
lemma card_fiber_mul (W : Type*) [AddCommGroup W] [Fintype W] [DecidableEq W]
    (L : (Fin r → k) →+ W) (hL : Function.Surjective L) (w : W) :
    (univ.filter (fun f => L f = w)).card * Fintype.card W = Fintype.card k ^ r := by
  have hfib : ∀ w, (univ.filter (fun f => L f = w)).card =
      (univ.filter (fun f => L f = 0)).card := by
    intro w
    obtain ⟨f0, hf0⟩ := hL w
    refine Finset.card_nbij' (fun f => f - f0) (fun f => f + f0) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
      rw [map_sub, hf, hf0, sub_self]
    · intro f hf
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
      rw [map_add, hf, hf0, zero_add]
    · intro f _; simp
    · intro f _; simp
  have htot := Finset.card_eq_sum_card_fiberwise (f := L) (s := (univ : Finset (Fin r → k)))
    (t := univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, smul_eq_mul] at htot
  have hcard : Fintype.card (Fin r → k) = Fintype.card k ^ r := by simp
  rw [Finset.card_univ, Finset.card_univ] at htot
  rw [hfib w, ← hcard, htot, Nat.mul_comm]

def pairL (x : Fin r → k) : (Fin r → k) →+ k where
  toFun f := pair f x
  map_zero' := by simp [pair]
  map_add' f g := pair_add_left f g x

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pairL_apply (x f : Fin r → k) : pairL x f = pair f x := rfl

def pairTwoLinear (x y : Fin r → k) : (Fin r → k) →+ k × k where
  toFun f := (pair f x, pair f y)
  map_zero' := by simp [pair]
  map_add' f g := by simp [pair_add_left]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pairTwoLinear_apply (x y f : Fin r → k) : pairTwoLinear x y f = (pair f x, pair f y) := rfl

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_coord_ne_zero hx`. Establish `hL : Function.Surjective (pairL x)` using `fun a => ⟨Pi.single i (a / x i), by rw [pairL_apply, pair_single_left, div_mul_cancel₀ _ hi]⟩`. Establish `h` using `card_fiber_mul k (pairL x) hL a`. Establish `hq : 0 < Fintype.card k` using `Fintype.card_pos`. Establish `hr : r - 1 + 1 = r` using `by have := i.pos; omega`.

Apply `Nat.eq_of_mul_eq_mul_right hq` to reduce the goal to its premises. Rewrite using `[← pow_succ, hr]`. Conclude with `h`.
-/
lemma count1 {x : Fin r → k} (hx : x ≠ 0) (a : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a)).card = Fintype.card k ^ (r - 1) := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
  have hL : Function.Surjective (pairL x) := fun a =>
    ⟨Pi.single i (a / x i), by rw [pairL_apply, pair_single_left, div_mul_cancel₀ _ hi]⟩
  have h := card_fiber_mul k (pairL x) hL a
  have hq : 0 < Fintype.card k := Fintype.card_pos
  have hr : r - 1 + 1 = r := by have := i.pos; omega
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← pow_succ, hr]
  exact h

/- English proof (translation)
Establish `hminor : ∃ i j, x i * y j - x j * y i ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨i, hi⟩` from `exists_coord_ne_zero hx`. Apply `hy (y i / x i)` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Use `hcon i j` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hi]`. Take the linear combination `this`.

Take `⟨i, j, hD⟩` from `hminor`. Establish `hL : Function.Surjective (pairTwoLinear x y)`. Introduce and unpack `⟨a, b⟩`. Use `⟨Pi.single i ((a * y j - b * x j) / (x i * y j - x j * y i)) + Pi.single j ((b * x i - a * y i) / (x i * y j - x j * y i)), ?_⟩` and prove the remaining obligations. Rewrite using `[pairTwoLinear_apply, pair_add_left, pair_add_left, pair_single_left, pair_single_left, pair_single_left, pair_single_left]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only`.

Rewrite using `[div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `card_fiber_mul (k × k) (pairTwoLinear x y) hL (a, b)`. Establish `hfil : univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b) = univ.filter (fun f => pairTwoLinear x y f = (a, b))`. Use extensionality with `f`.

Simplify using `[pairTwoLinear_apply]`. Rewrite using `[hfil]`. Establish `hq : 0 < Fintype.card k * Fintype.card k` using `Nat.mul_pos Fintype.card_pos Fintype.card_pos`. Apply `Nat.eq_of_mul_eq_mul_right hq` to reduce the goal to its premises. Rewrite `h` using `[Fintype.card_prod]`.

Rewrite using `[h, ← mul_assoc, ← pow_succ, ← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
lemma count2 (hr : 2 ≤ r) {x y : Fin r → k} (hx : x ≠ 0) (hy : ∀ c : k, y ≠ c • x) (a b : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b)).card =
      Fintype.card k ^ (r - 2) := by
  have hminor : ∃ i j, x i * y j - x j * y i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
    apply hy (y i / x i)
    funext j
    have := hcon i j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi]
    linear_combination this
  obtain ⟨i, j, hD⟩ := hminor
  have hL : Function.Surjective (pairTwoLinear x y) := by
    rintro ⟨a, b⟩
    refine ⟨Pi.single i ((a * y j - b * x j) / (x i * y j - x j * y i)) +
      Pi.single j ((b * x i - a * y i) / (x i * y j - x j * y i)), ?_⟩
    rw [pairTwoLinear_apply, pair_add_left, pair_add_left, pair_single_left, pair_single_left,
      pair_single_left, pair_single_left]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
    · dsimp only
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
  have h := card_fiber_mul (k × k) (pairTwoLinear x y) hL (a, b)
  have hfil : univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b) =
      univ.filter (fun f => pairTwoLinear x y f = (a, b)) := by
    ext f; simp [pairTwoLinear_apply]
  rw [hfil]
  have hq : 0 < Fintype.card k * Fintype.card k := Nat.mul_pos Fintype.card_pos Fintype.card_pos
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [Fintype.card_prod] at h
  rw [h, ← mul_assoc, ← pow_succ, ← pow_succ]
  congr 1; omega

/- English proof (translation)
Establish `h1 : opD (opU ψ) x = ∑ y, ((univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y`. Unfold `opD opU`. Rewrite using `[Finset.sum_comm' (t' := univ) (s' := fun y => univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1))]`. Use `Finset.sum_congr rfl (fun y _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`.

Introduce `f y`. Simplify using the standard rewrite rules. Establish `h2 : ∀ y, ((univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y = (if y = x then ((Fintype.card k : R)) ^ (r - 1) * ψ y else 0) + (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0)`. Introduce `y`. Distinguish the cases in `hyx : y = x`.

Rewrite using `[hyx]`. Establish `hne : ¬ ∀ c : k, x ≠ c • x` using `fun h => h 1 (one_smul _ _).symm`. Rewrite using `[if_pos rfl, if_neg hne, add_zero]`. Establish `: univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f x = 1) = univ.filter (fun f => pair f x = 1)`. Use extensionality with `f`.

Simplify using the standard rewrite rules. Rewrite using `[this, count1 hx 1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hyx]`.

Distinguish the cases in `hl : ∀ c : k, y ≠ c • x`. Rewrite using `[if_pos hl, zero_add, count2 hr hx hl 1 1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hl` using `[if_neg hl] push_neg`.

Take `⟨c, rfl⟩` from `hl`. Establish `hc : c ≠ 1` using `by rintro rfl; exact hyx (one_smul _ _)`. Rewrite using `[Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun f _ h => hc (by rw [← h.2, pair_smul_right, h.1, mul_one])))]`. Simplify using the standard rewrite rules. Establish `htr : trV ψ = nmV ψ x + ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y`.

Unfold `trV`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not (univ.filter (fun y : Fin r → k => y ≠ 0)) (fun y => ∃ c : k, y = c • x)]`. Use `congr 1`. Rewrite using `[nmV_eq_image ψ hx]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations.

Use extensionality with `y`. Rewrite using `[mem_image_line hx]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `y`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, ne_eq]`. Conclude with `⟨fun h => h.2, fun h => ⟨fun h0 => h 0 (by simp [h0]), h⟩⟩`. Rewrite using `[h1, Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), htr]`. Establish `h3 : ∑ y, (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) = ((Fintype.card k : R)) ^ (r - 2) * ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y`. Rewrite using `[Finset.mul_sum, Finset.sum_filter]`.

Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma DU_formula (hr : 2 ≤ r) (ψ : (Fin r → k) → R) (x : Fin r → k) (hx : x ≠ 0) :
    opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x
      - ((Fintype.card k : R)) ^ (r - 2) * nmV ψ x + ((Fintype.card k : R)) ^ (r - 2) * trV ψ := by
  have h1 : opD (opU ψ) x = ∑ y, ((univ.filter (fun f : Fin r → k =>
      pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y := by
    unfold opD opU
    rw [Finset.sum_comm' (t' := univ)
      (s' := fun y => univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1))]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro f y; simp
  have h2 : ∀ y, ((univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f y = 1)).card : R) * ψ y =
      (if y = x then ((Fintype.card k : R)) ^ (r - 1) * ψ y else 0) +
      (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) := by
    intro y
    by_cases hyx : y = x
    · rw [hyx]
      have hne : ¬ ∀ c : k, x ≠ c • x := fun h => h 1 (one_smul _ _).symm
      rw [if_pos rfl, if_neg hne, add_zero]
      have : univ.filter (fun f : Fin r → k => pair f x = 1 ∧ pair f x = 1) =
          univ.filter (fun f => pair f x = 1) := by
        ext f; simp
      rw [this, count1 hx 1]; push_cast; ring
    · rw [if_neg hyx]
      by_cases hl : ∀ c : k, y ≠ c • x
      · rw [if_pos hl, zero_add, count2 hr hx hl 1 1]; push_cast; ring
      · rw [if_neg hl]
        push_neg at hl
        obtain ⟨c, rfl⟩ := hl
        have hc : c ≠ 1 := by rintro rfl; exact hyx (one_smul _ _)
        rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun f _ h =>
          hc (by rw [← h.2, pair_smul_right, h.1, mul_one])))]
        simp
  have htr : trV ψ = nmV ψ x + ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y := by
    unfold trV
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun y : Fin r → k => y ≠ 0))
      (fun y => ∃ c : k, y = c • x)]
    congr 1
    · rw [nmV_eq_image ψ hx]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      rw [mem_image_line hx]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, ne_eq]
      exact ⟨fun h => h.2, fun h => ⟨fun h0 => h 0 (by simp [h0]), h⟩⟩
  rw [h1, Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), htr]
  have h3 : ∑ y, (if ∀ c : k, y ≠ c • x then ((Fintype.card k : R)) ^ (r - 2) * ψ y else 0) =
      ((Fintype.card k : R)) ^ (r - 2) * ∑ y ∈ univ.filter (fun y => ∀ c : k, y ≠ c • x), ψ y := by
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [h3]; ring

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `k _ _ _ r R _ ψ φ`. Unfold `opU opD`. Simplify using `only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun f _ => ?_))` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem up_down_operators_adjoint : AdjointReformulated := by
  intro k _ _ _ r R _ ψ φ
  unfold opU opD
  simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun f _ => ?_))
  split_ifs <;> ring

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ hr ψ x hx` and use `DU_formula hr ψ x hx`.
-/
theorem down_up_composition_formula : DualCompositionReformulated :=
  fun _ _ _ _ _ _ _ hr ψ x hx => DU_formula hr ψ x hx

/- English proof (translation)
Introduce `k _ _ _ r R _ hr φ f hf`. Rewrite using `[← opU_eq_opD φ, opU_eq_opD (opU φ), nmP_eq_nmV]`. Conclude with `DU_formula hr φ f hf`.
-/
theorem up_down_composition_formula : CompositionWithDual := by
  intro k _ _ _ r R _ hr φ f hf
  rw [← opU_eq_opD φ, opU_eq_opD (opU φ), nmP_eq_nmV]
  exact DU_formula hr φ f hf

/- English proof (translation)
Establish `htr` using `trV_eq_zero ψ h`. Use `⟨fun f => ?_, htr, fun hr x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[nmP_opU]`. Conclude with `Finset.sum_eq_zero (fun x hx => h x (ne_zero_of_pair_eq_one (by simpa using hx)))`. Rewrite using `[DU_formula hr ψ x hx, h x hx, htr]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma ram_V {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
    (ψ : (Fin r → k) → R) (h : ∀ y, y ≠ 0 → nmV ψ y = 0) :
    (∀ f, nmP (opU ψ) f = 0) ∧ trV ψ = 0 ∧
      (2 ≤ r → ∀ x, x ≠ 0 → opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x) := by
  have htr := trV_eq_zero ψ h
  refine ⟨fun f => ?_, htr, fun hr x hx => ?_⟩
  · rw [nmP_opU]
    exact Finset.sum_eq_zero (fun x hx =>
      h x (ne_zero_of_pair_eq_one (by simpa using hx)))
  · rw [DU_formula hr ψ x hx, h x hx, htr]; ring

/- English proof (translation)
Introduce `k _ _ _ r R _`. Use `⟨fun ψ h => ram_V ψ h, fun φ h => ?_⟩` and prove the remaining obligations. Establish `h' : ∀ y, y ≠ 0 → nmV φ y = 0` using `fun y hy => by rw [← nmP_eq_nmV]; exact h y hy`. Take `⟨h1, h2, h3⟩` from `ram_V φ h'`. Use `⟨fun x => ?_, h2, fun hr f hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[← nmP_eq_nmV, ← opU_eq_opD]`. Conclude with `h1 x`. Rewrite using `[← opU_eq_opD φ, opU_eq_opD (opU φ)]`. Conclude with `h3 hr f hf`.
-/
theorem ramified_lattice_operator_identity : UnitsSumZero := by
  intro k _ _ _ r R _
  refine ⟨fun ψ h => ram_V ψ h, fun φ h => ?_⟩
  have h' : ∀ y, y ≠ 0 → nmV φ y = 0 := fun y hy => by rw [← nmP_eq_nmV]; exact h y hy
  obtain ⟨h1, h2, h3⟩ := ram_V φ h'
  refine ⟨fun x => ?_, h2, fun hr f hf => ?_⟩
  · rw [← nmP_eq_nmV, ← opU_eq_opD]; exact h1 x
  · rw [← opU_eq_opD φ, opU_eq_opD (opU φ)]; exact h3 hr f hf

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
