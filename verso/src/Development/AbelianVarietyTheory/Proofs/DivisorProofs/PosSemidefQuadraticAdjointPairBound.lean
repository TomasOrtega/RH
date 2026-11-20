import Mathlib

namespace GlobalTheory.PosFormAdjoint

/- English proof (translation)
Establish `key : ∀ a b : ℤ, 0 ≤ a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v`. Introduce `a b`. Establish `h1` using `hpos (a • u + b • v)`. Establish `e : F (a • u + b • v) (a • u + b • v) = a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v`. Simplify using `only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]`.

Rewrite using `[hsym v u]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e]`. Conclude with `h1`. Break down `(hpos u).lt_or_eq with ht | ht` into its components or cases.

Establish `h2` using `key (-(F u v)) (F u u)`. Establish `h3 : 0 ≤ F u u * (F u u * F v v - F u v ^ 2)` using `by nlinarith [h2]`. Establish `h4 : 0 ≤ F u u * F v v - F u v ^ 2`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Use polynomial arithmetic with `[mul_neg_of_pos_of_neg ht hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← ht]`. Simplify using `only [zero_mul]`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `hs : (1 : ℤ) ≤ F u v ^ 2` using `hc`. Establish `h2` using `key (-(F v v + 1) * F u v) 1`. Rewrite `h2` using `[← ht]`. Establish `hv` using `hpos v`.

Use polynomial arithmetic with `[h2, hs, hv]`.
-/
theorem int_cauchy_schwarz {X : Type} [AddCommGroup X] (F : X →+ X →+ ℤ)
    (hsym : ∀ u v, F u v = F v u) (hpos : ∀ u, 0 ≤ F u u) (u v : X) :
    F u v ^ 2 ≤ F u u * F v v := by
  have key : ∀ a b : ℤ, 0 ≤ a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
    intro a b
    have h1 := hpos (a • u + b • v)
    have e : F (a • u + b • v) (a • u + b • v)
        = a ^ 2 * F u u + 2 * a * b * F u v + b ^ 2 * F v v := by
      simp only [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, smul_eq_mul]
      rw [hsym v u]
      ring
    rw [e] at h1
    exact h1
  rcases (hpos u).lt_or_eq with ht | ht
  · have h2 := key (-(F u v)) (F u u)
    have h3 : 0 ≤ F u u * (F u u * F v v - F u v ^ 2) := by nlinarith [h2]
    have h4 : 0 ≤ F u u * F v v - F u v ^ 2 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_neg_of_pos_of_neg ht hc]
    linarith
  · rw [← ht]
    simp only [zero_mul]
    by_contra hc
    push_neg at hc
    have hs : (1 : ℤ) ≤ F u v ^ 2 := hc
    have h2 := key (-(F v v + 1) * F u v) 1
    rw [← ht] at h2
    have hv := hpos v
    nlinarith [h2, hs, hv]

/- English proof (translation)
Use `set S : ℤ := ∑ i ∈ Finset.range n, |c i| with hS`. Establish `hcast : (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) = S + 1`. Use `push_cast`. Simplify using `[hS, Int.natCast_natAbs]`. Rewrite using `[hcast]`.

Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg (fun i _ => abs_nonneg _)`. Assume the negation of the conclusion as `H`. Use `push_neg at H`. Establish `ha0 : 0 < a 0`. Break down `(hpos 0).lt_or_eq with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Establish `h1` using `hlc 0`. Rewrite `h1`, `H` using `[← h]`. Simplify using `at h1 H`.

Use polynomial arithmetic with `[sq_nonneg (a 1)]`. Establish `h01 : a 0 < a 1` using `by nlinarith`. Establish `hind : ∀ k, 0 < a k ∧ a 1 * a k ≤ a (k + 1) * a 0`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact ⟨ha0, by simp [mul_comm]⟩`. Consider the case `succ k ih`. Take `⟨hk, hk'⟩` from `ih`. Establish `hk1 : 0 < a (k + 1)`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Use polynomial arithmetic with `[mul_pos (by linarith : (0:ℤ) < a 1) hk]`. Use `⟨hk1, ?_⟩` and prove the remaining obligations. Establish `h2` using `hlc k`. Establish `h3 : a k * (a 1 * a (k + 1)) ≤ a k * (a (k + 2) * a 0)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hk' hk1.le]`. Conclude with `le_of_mul_le_mul_left h3 hk`. Establish `hmono : ∀ k, a k ≤ a (k + 1)`. Introduce `k`. Take `⟨hk, hk'⟩` from `hind k`.

Establish `: a 0 * a k ≤ a 0 * a (k + 1)` using `by nlinarith [mul_le_mul_of_nonneg_right h01.le hk.le]`. Conclude with `le_of_mul_le_mul_left this ha0`. Establish `hmono' : Monotone a` using `monotone_nat_of_le_succ hmono`. Break down `n with _ | m` into its components or cases. Simplify using `at hrec`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hrec` using `[Finset.sum_range_succ]`. Take `⟨hm, hm'⟩` from `hind m`. Establish `hle : -(∑ i ∈ Finset.range (m + 1), c i * a i) ≤ S * a m`. Rewrite using `[hS, Finset.sum_mul, ← Finset.sum_neg_distrib]`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i hi`. Establish `hi' : i ≤ m` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `h1 : -(c i * a i) ≤ |c i| * a i`. Use `neg_abs_le (c i)` as an intermediate fact.

Use polynomial arithmetic with `[hpos i]`. Establish `h2 : |c i| * a i ≤ |c i| * a m` using `mul_le_mul_of_nonneg_left (hmono' hi') (abs_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrec' : a (m + 1) = -(∑ i ∈ Finset.range (m + 1), c i * a i)`. Rewrite using `[Finset.sum_range_succ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : (S + 1) * a 0 * a m < a 1 * a m` using `by nlinarith`. Establish `h6 : (S + 1) * a m * a 0 < a (m + 1) * a 0` using `by nlinarith`. Establish `h7 : (S + 1) * a m < a (m + 1)` using `lt_of_mul_lt_mul_right h6 ha0.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem seq_bound (a c : ℕ → ℤ) (n : ℕ) (hpos : ∀ k, 0 ≤ a k)
    (hlc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2))
    (hrec : a n + ∑ i ∈ Finset.range n, c i * a i = 0) :
    a 1 ≤ (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) * a 0 := by
  set S : ℤ := ∑ i ∈ Finset.range n, |c i| with hS
  have hcast : (((∑ i ∈ Finset.range n, (c i).natAbs : ℕ) + 1 : ℕ) : ℤ) = S + 1 := by
    push_cast
    simp [hS, Int.natCast_natAbs]
  rw [hcast]
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  by_contra H
  push_neg at H
  have ha0 : 0 < a 0 := by
    rcases (hpos 0).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hlc 0
      rw [← h] at h1 H
      simp at h1 H
      nlinarith [sq_nonneg (a 1)]
  have h01 : a 0 < a 1 := by nlinarith
  have hind : ∀ k, 0 < a k ∧ a 1 * a k ≤ a (k + 1) * a 0 := by
    intro k
    induction k with
    | zero => exact ⟨ha0, by simp [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hk1 : 0 < a (k + 1) := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos (by linarith : (0:ℤ) < a 1) hk]
      refine ⟨hk1, ?_⟩
      have h2 := hlc k
      have h3 : a k * (a 1 * a (k + 1)) ≤ a k * (a (k + 2) * a 0) := by
        nlinarith [mul_le_mul_of_nonneg_left hk' hk1.le]
      exact le_of_mul_le_mul_left h3 hk
  have hmono : ∀ k, a k ≤ a (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := hind k
    have : a 0 * a k ≤ a 0 * a (k + 1) := by nlinarith [mul_le_mul_of_nonneg_right h01.le hk.le]
    exact le_of_mul_le_mul_left this ha0
  have hmono' : Monotone a := monotone_nat_of_le_succ hmono
  rcases n with _ | m
  · simp at hrec
    linarith
  · rw [Finset.sum_range_succ] at hrec
    obtain ⟨hm, hm'⟩ := hind m
    have hle : -(∑ i ∈ Finset.range (m + 1), c i * a i) ≤ S * a m := by
      rw [hS, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : -(c i * a i) ≤ |c i| * a i := by
        have := neg_abs_le (c i)
        nlinarith [hpos i]
      have h2 : |c i| * a i ≤ |c i| * a m :=
        mul_le_mul_of_nonneg_left (hmono' hi') (abs_nonneg _)
      linarith
    have hrec' : a (m + 1) = -(∑ i ∈ Finset.range (m + 1), c i * a i) := by
      rw [Finset.sum_range_succ]; linarith
    have h5 : (S + 1) * a 0 * a m < a 1 * a m := by nlinarith
    have h6 : (S + 1) * a m * a 0 < a (m + 1) * a 0 := by nlinarith
    have h7 : (S + 1) * a m < a (m + 1) := lt_of_mul_lt_mul_right h6 ha0.le
    nlinarith

end GlobalTheory.PosFormAdjoint

namespace GlobalTheory.PosFormAdjoint

/- English proof (translation)
Introduce `X _ _ _ h h'`. Set `T : Module.End ℤ X` to `h'.toIntLinearMap * h.toIntLinearMap`. Establish `hT : ∀ u, T u = h' (h u)` using `fun u => rfl`. Set `p` to `T.charpoly`. Use `⟨(∑ i ∈ Finset.range p.natDegree, (-(p.coeff i)).natAbs) + 1, ?_⟩` and prove the remaining obligations.

Introduce `q hq hq0 hqneg hcube hadj y`. Set `B : X →+ X →+ ℤ` to `AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => q (u + v) - q u - q v) (fun a b => by`. Use `hcube u a b` as an intermediate fact. Rewrite using `[← add_assoc]`. Use the proof step `linarith))`.

Use the proof step `(fun a b => by`. Use extensionality with `v`. Simplify using `only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]`. Use `hcube a b v` as an intermediate fact. Use the proof step `linarith)`.

Establish `hB : ∀ u v, B u v = q (u + v) - q u - q v` using `fun u v => rfl`. Establish `Bsym : ∀ u v, B u v = B v u`. Introduce `u v`. Rewrite using `[hB, hB, add_comm]`. Expand and normalize the polynomial expressions, which then agree.

Establish `Bdiag : ∀ u, B u u = 2 * q u`. Introduce `u`. Use `hcube u u (-u)` as an intermediate fact. Simplify using `only [add_neg_cancel_right, add_neg_cancel, hq0, hqneg] at this`. Rewrite using `[hB]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `Badj : ∀ u v, B (h u) v = B u (h' v)`. Introduce `u v`. Rewrite using `[hB, hB]`. Use `hadj u v` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `BT : ∀ u v, B (T u) v = B u (T v)`. Introduce `u v`. Rewrite using `[hT, hT, Bsym, ← Badj, Bsym, Badj]`. Establish `BTpow : ∀ k u v, B ((T ^ k) u) v = B u ((T ^ k) v)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro u v`. Both sides reduce to the same expression. Consider the case `succ k ih`.

Introduce `u v`. Rewrite using `[pow_succ', Module.End.mul_apply, BT, ih]`. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← pow_succ, ← pow_succ']`. Set `G : X →+ X →+ ℤ` to `B.comp (T : X →+ X)`.

Establish `hG : ∀ u v, G u v = B (T u) v` using `fun u v => rfl`. Establish `Gsym : ∀ u v, G u v = G v u`. Introduce `u v`. Rewrite using `[hG, hG, BT, Bsym]`. Establish `Gdiag : ∀ u, G u u = 2 * q (h u)`.

Introduce `u`. Rewrite using `[hG, hT, Bsym, ← Badj, Bdiag]`. Establish `Bpos : ∀ u, 0 ≤ B u u` using `fun u => by rw [Bdiag]; linarith [hq u]`. Establish `Gpos : ∀ u, 0 ≤ G u u` using `fun u => by rw [Gdiag]; linarith [hq (h u)]`. Set `a : ℕ → ℤ` to `fun k => B ((T ^ k) y) y`.

Establish `aB : ∀ i j, a (i + j) = B ((T ^ i) y) ((T ^ j) y)`. Introduce `i j`. Use `show B ((T ^ (i + j)) y) y = _`. Rewrite using `[pow_add, Module.End.mul_apply, BTpow]`. Conclude with `Bsym _ _`.

Establish `aG : ∀ i j, a (i + j + 1) = G ((T ^ i) y) ((T ^ j) y)`. Introduce `i j`. Rewrite using `[hG, ← Module.End.mul_apply, ← pow_succ', add_right_comm, aB]`. Establish `apos : ∀ k, 0 ≤ a k`. Introduce `k`.

Break down `Nat.even_or_odd' k with ⟨m, rfl | rfl⟩` into its components or cases. Rewrite using `[two_mul, aB]`. Conclude with `Bpos _`. Rewrite using `[two_mul, aG]`. Conclude with `Gpos _`.

Establish `alc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2)`. Introduce `k`. Break down `Nat.even_or_odd' k with ⟨m, rfl | rfl⟩` into its components or cases. Establish `e1 : a (2 * m + 1) = B ((T ^ m) y) ((T ^ (m + 1)) y)`. Rewrite using `[← aB]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : a (2 * m + 2) = B ((T ^ (m + 1)) y) ((T ^ (m + 1)) y)`. Rewrite using `[← aB]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, two_mul, aB]`. Conclude with `int_cauchy_schwarz B Bsym Bpos _ _`. Establish `e1 : a (2 * m + 1 + 1) = G ((T ^ m) y) ((T ^ (m + 1)) y)`. Rewrite using `[← aG]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : a (2 * m + 1 + 2) = G ((T ^ (m + 1)) y) ((T ^ (m + 1)) y)`. Rewrite using `[← aG]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, two_mul, aG]`. Conclude with `int_cauchy_schwarz G Gsym Gpos _ _`. Establish `hmonic : p.Monic` using `LinearMap.charpoly_monic T`. Establish `hrec : a p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * a i = 0`.

Establish `hCH : (Polynomial.aeval T p) y = 0`. Rewrite using `[LinearMap.aeval_self_charpoly]`. Both sides reduce to the same expression. Rewrite `hCH` using `[Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul]`. Establish `h2` using `congrArg (fun x => B x y) hCH`.

Simplify using `only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, smul_eq_mul, map_zero, AddMonoidHom.zero_apply] at h2`. Rewrite using `[add_comm]`. Conclude with `h2`. Establish `hb` using `seq_bound a (fun i => p.coeff i) p.natDegree apos alc hrec`. Establish `a0 : a 0 = 2 * q y` using `by show B ((T ^ 0) y) y = _; rw [pow_zero]; exact Bdiag y`.

Establish `a1 : a 1 = 2 * q (h y)`. Use `aG 0 0` as an intermediate fact. Simplify using `only [zero_add, pow_zero] at this`. Rewrite using `[this]`. Conclude with `Gdiag y`.

Rewrite `hb` using `[a0, a1]`. Establish `habs : ∀ i, (-(p.coeff i)).natAbs = (p.coeff i).natAbs` using `fun i => Int.natAbs_neg _`. Simplify using `only [habs]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem pos_form_adjoint_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y := by
  intro X _ _ _ h h'
  let T : Module.End ℤ X := h'.toIntLinearMap * h.toIntLinearMap
  have hT : ∀ u, T u = h' (h u) := fun u => rfl
  let p := T.charpoly
  refine ⟨(∑ i ∈ Finset.range p.natDegree, (-(p.coeff i)).natAbs) + 1, ?_⟩
  intro q hq hq0 hqneg hcube hadj y
  let B : X →+ X →+ ℤ := AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => q (u + v) - q u - q v)
      (fun a b => by
        have := hcube u a b
        rw [← add_assoc]
        linarith))
    (fun a b => by
      ext v
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      have := hcube a b v
      linarith)
  have hB : ∀ u v, B u v = q (u + v) - q u - q v := fun u v => rfl
  have Bsym : ∀ u v, B u v = B v u := by
    intro u v; rw [hB, hB, add_comm]; ring
  have Bdiag : ∀ u, B u u = 2 * q u := by
    intro u
    have := hcube u u (-u)
    simp only [add_neg_cancel_right, add_neg_cancel, hq0, hqneg] at this
    rw [hB]; linarith
  have Badj : ∀ u v, B (h u) v = B u (h' v) := by
    intro u v; rw [hB, hB]; have := hadj u v; linarith
  have BT : ∀ u v, B (T u) v = B u (T v) := by
    intro u v
    rw [hT, hT, Bsym, ← Badj, Bsym, Badj]
  have BTpow : ∀ k u v, B ((T ^ k) u) v = B u ((T ^ k) v) := by
    intro k
    induction k with
    | zero => intro u v; rfl
    | succ k ih =>
      intro u v
      rw [pow_succ', Module.End.mul_apply, BT, ih]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  let G : X →+ X →+ ℤ := B.comp (T : X →+ X)
  have hG : ∀ u v, G u v = B (T u) v := fun u v => rfl
  have Gsym : ∀ u v, G u v = G v u := by
    intro u v; rw [hG, hG, BT, Bsym]
  have Gdiag : ∀ u, G u u = 2 * q (h u) := by
    intro u; rw [hG, hT, Bsym, ← Badj, Bdiag]
  have Bpos : ∀ u, 0 ≤ B u u := fun u => by rw [Bdiag]; linarith [hq u]
  have Gpos : ∀ u, 0 ≤ G u u := fun u => by rw [Gdiag]; linarith [hq (h u)]
  let a : ℕ → ℤ := fun k => B ((T ^ k) y) y
  have aB : ∀ i j, a (i + j) = B ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    show B ((T ^ (i + j)) y) y = _
    rw [pow_add, Module.End.mul_apply, BTpow]
    exact Bsym _ _
  have aG : ∀ i j, a (i + j + 1) = G ((T ^ i) y) ((T ^ j) y) := by
    intro i j
    rw [hG, ← Module.End.mul_apply, ← pow_succ', add_right_comm, aB]
  have apos : ∀ k, 0 ≤ a k := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [two_mul, aB]; exact Bpos _
    · rw [two_mul, aG]; exact Gpos _
  have alc : ∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2) := by
    intro k
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have e1 : a (2 * m + 1) = B ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      have e2 : a (2 * m + 2) = B ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aB]; congr 1; ring
      rw [e1, e2, two_mul, aB]
      exact int_cauchy_schwarz B Bsym Bpos _ _
    · have e1 : a (2 * m + 1 + 1) = G ((T ^ m) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      have e2 : a (2 * m + 1 + 2) = G ((T ^ (m + 1)) y) ((T ^ (m + 1)) y) := by
        rw [← aG]; congr 1; ring
      rw [e1, e2, two_mul, aG]
      exact int_cauchy_schwarz G Gsym Gpos _ _
  have hmonic : p.Monic := LinearMap.charpoly_monic T
  have hrec : a p.natDegree + ∑ i ∈ Finset.range p.natDegree, p.coeff i * a i = 0 := by
    have hCH : (Polynomial.aeval T p) y = 0 := by
      rw [LinearMap.aeval_self_charpoly]; rfl
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hCH
    have h2 := congrArg (fun x => B x y) hCH
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add,
      map_sum, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.finset_sum_apply,
      AddMonoidHom.smul_apply, smul_eq_mul, map_zero, AddMonoidHom.zero_apply] at h2
    rw [add_comm]; exact h2
  have hb := seq_bound a (fun i => p.coeff i) p.natDegree apos alc hrec
  have a0 : a 0 = 2 * q y := by show B ((T ^ 0) y) y = _; rw [pow_zero]; exact Bdiag y
  have a1 : a 1 = 2 * q (h y) := by
    have := aG 0 0
    simp only [zero_add, pow_zero] at this
    rw [this]; exact Gdiag y
  rw [a0, a1] at hb
  have habs : ∀ i, (-(p.coeff i)).natAbs = (p.coeff i).natAbs := fun i => Int.natAbs_neg _
  simp only [habs]
  linarith

end GlobalTheory.PosFormAdjoint
