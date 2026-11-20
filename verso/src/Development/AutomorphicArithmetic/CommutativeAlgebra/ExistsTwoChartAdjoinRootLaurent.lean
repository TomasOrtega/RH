import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
noncomputable section
open IsLocalRing UpperTheory.Et

section SlopeTestRemainingChoices

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [e0]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih, ← ea]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
private theorem e_pow {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) (n : ℕ) :
    e 1 ^ n = e n := by
  induction n with
  | zero => simp [e0]
  | succ n ih =>
    rw [pow_succ, ih, ← ea]
    push_cast
    rfl

/- English proof (translation)
Establish `h0 : ((a - k * i).toNat : ℤ) = a - k * i` using `Int.toNat_of_nonneg (sub_nonneg.2 h)`. Rewrite using `[mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, e_pow e0 ea]`. Use `congr 2`. Use `push_cast`. Rewrite using `[h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gen_eq {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) (r : D)
    (k i : ℕ) (a : ℤ) (h : (k : ℤ) * i ≤ a) :
    e a * r ^ i = e 1 ^ (a - k * i).toNat * (e 1 ^ k * r) ^ i := by
  have h0 : ((a - k * i).toNat : ℤ) = a - k * i := Int.toNat_of_nonneg (sub_nonneg.2 h)
  rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, e_pow e0 ea]
  congr 2
  push_cast
  rw [h0]
  ring

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => rw [mul_zero]`. Conclude with `M.zero_mem`.

Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `M.add_mem hx hy`. Consider the case `smul a x _ hx => rw [mul_smul_comm]`. Conclude with `M.smul_mem a hx`.
-/
private theorem span_mul_mem {S : Set D} {M : Submodule A D} {c : D}
    (h : ∀ x ∈ S, c * x ∈ M) : ∀ w ∈ Submodule.span A S, c * w ∈ M := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [mul_zero]; exact M.zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact M.add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact M.smul_mem a hx

/- English proof (translation)
Use `set M := Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧ x = e a * r ^ i} with hM`. Establish `h1 : (1 : D) ∈ M`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Establish `h10 : (1 : D) = 0` using `by simpa using hrel`. Rewrite using `[h10]`.

Conclude with `M.zero_mem`. Conclude with `Submodule.subset_span ⟨0, 0, hN, by simp, by simp [e0]⟩`. Establish `ht : ∀ m ∈ M, e 1 * m ∈ M`. Use `span_mul_mem ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, i, hi, ha, rfl⟩`.

Use `Submodule.subset_span ⟨a + 1, i, hi, by linarith, ?_⟩` and prove the remaining obligations. Rewrite using `[ea]`. Expand and normalize the polynomial expressions, which then agree. Establish `hy : ∀ m ∈ M, (e 1 ^ k * r) * m ∈ M`. Use `span_mul_mem ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, i, hi, ha, rfl⟩`. Establish `hk : e 1 ^ k * r * (e a * r ^ i) = e (a + k) * r ^ (i + 1)`. Rewrite using `[e_pow e0 ea, ea]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hk]`.

Distinguish the cases in `hiN : i + 1 < N`. Use `Submodule.subset_span ⟨a + k, i + 1, hiN, ?_, rfl⟩` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN : i + 1 = N` using `by omega`.

Rewrite using `[hN]`. Use `span_mul_mem ?_ _ hrel` and prove the remaining obligations. Introduce and unpack `_ ⟨b, j, hj, hb, rfl⟩`. Use `Submodule.subset_span ⟨a + k + b, j, hj, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : (k : ℤ) * j ≤ k * i` using `mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : j ≤ i)) (by positivity)`.

Establish `h3 : -(k : ℤ) ≤ b` using `by omega`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[ea (a + k) b]`. Expand and normalize the polynomial expressions, which then agree. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Establish `key : ∀ x ∈ Algebra.adjoin A {e 1, e 1 ^ k * r}, ∀ m ∈ M, x * m ∈ M`. Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Break down `hx with rfl | hx` into its components or cases. Conclude with `ht`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Conclude with `hy`. Consider the case `algebraMap c`.

Introduce `m hm`. Rewrite using `[← Algebra.smul_def]`. Conclude with `M.smul_mem c hm`. Consider the case `add x y _ _ hx hy`. Introduce `m hm`.

Rewrite using `[add_mul]`. Conclude with `M.add_mem (hx m hm) (hy m hm)`. Consider the case `mul x y _ _ hx hy`. Introduce `m hm`. Rewrite using `[mul_assoc]`.

Conclude with `hx _ (hy m hm)`. Simplify using `using key x hx 1 h1`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, i, hi, ha, rfl⟩`. Rewrite using `[gen_eq e0 ea r k i a ha]`.

Use `Subalgebra.mem_toSubmodule _ |>.2 ?_` and prove the remaining obligations. Conclude with `mul_mem (pow_mem (Algebra.subset_adjoin (by simp)) _) (pow_mem (Algebra.subset_adjoin (by simp)) _)`.
-/
private theorem chart_eq {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) {r : D}
    {k N : ℕ}
    (hrel : r ^ N ∈ Submodule.span A
      {x : D | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧ x = e b * r ^ i}) :
    Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r}) =
      Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧ x = e a * r ^ i} := by
  set M := Submodule.span A
    {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧ x = e a * r ^ i} with hM
  have h1 : (1 : D) ∈ M := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have h10 : (1 : D) = 0 := by simpa using hrel
      rw [h10]
      exact M.zero_mem
    · exact Submodule.subset_span ⟨0, 0, hN, by simp, by simp [e0]⟩
  have ht : ∀ m ∈ M, e 1 * m ∈ M := by
    refine span_mul_mem ?_
    rintro _ ⟨a, i, hi, ha, rfl⟩
    refine Submodule.subset_span ⟨a + 1, i, hi, by linarith, ?_⟩
    rw [ea]
    ring
  have hy : ∀ m ∈ M, (e 1 ^ k * r) * m ∈ M := by
    refine span_mul_mem ?_
    rintro _ ⟨a, i, hi, ha, rfl⟩
    have hk : e 1 ^ k * r * (e a * r ^ i) = e (a + k) * r ^ (i + 1) := by
      rw [e_pow e0 ea, ea]
      ring
    rw [hk]
    by_cases hiN : i + 1 < N
    · refine Submodule.subset_span ⟨a + k, i + 1, hiN, ?_, rfl⟩
      push_cast
      linarith
    · have hN : i + 1 = N := by omega
      rw [hN]
      refine span_mul_mem ?_ _ hrel
      rintro _ ⟨b, j, hj, hb, rfl⟩
      refine Submodule.subset_span ⟨a + k + b, j, hj, ?_, ?_⟩
      · have h2 : (k : ℤ) * j ≤ k * i :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : j ≤ i)) (by positivity)
        have h3 : -(k : ℤ) ≤ b := by omega
        linarith
      · rw [ea (a + k) b]
        ring
  apply le_antisymm
  · intro x hx
    have key : ∀ x ∈ Algebra.adjoin A {e 1, e 1 ^ k * r}, ∀ m ∈ M, x * m ∈ M := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact ht
        · rw [Set.mem_singleton_iff.1 hx]
          exact hy
      | algebraMap c =>
        intro m hm
        rw [← Algebra.smul_def]
        exact M.smul_mem c hm
      | add x y _ _ hx hy =>
        intro m hm
        rw [add_mul]
        exact M.add_mem (hx m hm) (hy m hm)
      | mul x y _ _ hx hy =>
        intro m hm
        rw [mul_assoc]
        exact hx _ (hy m hm)
    simpa using key x hx 1 h1
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, i, hi, ha, rfl⟩
    rw [gen_eq e0 ea r k i a ha]
    refine Subalgebra.mem_toSubmodule _ |>.2 ?_
    exact mul_mem (pow_mem (Algebra.subset_adjoin (by simp)) _)
      (pow_mem (Algebra.subset_adjoin (by simp)) _)

/- English proof (translation)
Establish `hx : x ∈ Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i}`. Rewrite using `[hall]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, i, hi, rfl⟩` from `hx`. Use `⟨((k : ℤ) * i - a).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, e_pow e0 ea, ← ea]`. Conclude with `hg _ _ hi (by have := Int.self_le_toNat ((k : ℤ) * i - a); linarith)`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `h : e 1 ^ (n + m) * (x + y) = e 1 ^ m * (e 1 ^ n * x) + e 1 ^ n * (e 1 ^ m * y)`.

Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `add_mem (mul_mem (pow_mem ht _) hn) (mul_mem (pow_mem ht _) hm)`. Consider the case `smul c x _ hx`.

Take `⟨n, hn⟩` from `hx`. Conclude with `⟨n, by rw [mul_smul_comm]; exact S.smul_mem hn c⟩`.
-/
private theorem chart_loc {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) {r : D}
    {k N : ℕ}
    (hall : Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} = ⊤)
    (S : Subalgebra A D) (ht : e 1 ∈ S)
    (hg : ∀ (a : ℤ) (i : ℕ), i < N → (k : ℤ) * i ≤ a → e a * r ^ i ∈ S) (x : D) :
    ∃ n : ℕ, e 1 ^ n * x ∈ S := by
  have hx : x ∈ Submodule.span A {x : D | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} := by
    rw [hall]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, i, hi, rfl⟩ := hx
    refine ⟨((k : ℤ) * i - a).toNat, ?_⟩
    rw [← mul_assoc, e_pow e0 ea, ← ea]
    exact hg _ _ hi (by have := Int.self_le_toNat ((k : ℤ) * i - a); linarith)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have h : e 1 ^ (n + m) * (x + y) = e 1 ^ m * (e 1 ^ n * x) + e 1 ^ n * (e 1 ^ m * y) := by
      rw [pow_add]
      ring
    rw [h]
    exact add_mem (mul_mem (pow_mem ht _) hn) (mul_mem (pow_mem ht _) hm)
  | smul c x _ hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rw [mul_smul_comm]; exact S.smul_mem hn c⟩

/- English proof (translation)
Use `LaurentPolynomial.induction_on' p ?_ ?_` and prove the remaining obligations. Introduce and unpack `p q ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨max a b, fun m hm => add_mem (ha m (le_of_max_le_left hm)) (hb m (le_of_max_le_right hm))⟩`. Introduce `n a`. Use `⟨n.natAbs, fun m hm => ?_⟩` and prove the remaining obligations.

Establish `h : LaurentPolynomial.C a * LaurentPolynomial.T n = a • LaurentPolynomial.T n`. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hm, rfl⟩)`.
-/
private theorem exp_bound {A : Type} [CommRing A] (p : LaurentPolynomial A) :
    ∃ n : ℕ, ∀ m ≥ n, p ∈ Submodule.span A
      {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ m ∧ x = LaurentPolynomial.T b} := by
  refine LaurentPolynomial.induction_on' p ?_ ?_
  · rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, fun m hm => add_mem (ha m (le_of_max_le_left hm)) (hb m (le_of_max_le_right hm))⟩
  · intro n a
    refine ⟨n.natAbs, fun m hm => ?_⟩
    have h : LaurentPolynomial.C a * LaurentPolynomial.T n = a • LaurentPolynomial.T n := by
      rw [Algebra.smul_def]
      rfl
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hm, rfl⟩)

/- English proof (translation)
Establish `e0' : (fun a => e (-a)) 0 = 1` using `by simpa using e0`. Establish `ea' : ∀ a b, (fun a => e (-a)) (a + b) = (fun a => e (-a)) a * (fun a => e (-a)) b` using `fun a b => by simp only [neg_add, ea]`. Establish `himg : ∀ Q : ℤ → ℕ → Prop, β '' {p | Q p.1 p.2} = {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ Q a i ∧ x = e a * r ^ i}`. Introduce `Q`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩`. Conclude with `⟨p.1, p.2, p.2.2, hp, hβ p⟩`. Introduce and unpack `⟨a, i, hi, hq, rfl⟩`. Conclude with `⟨(a, ⟨i, hi⟩), hq, hβ _⟩`.

Establish `hall : Submodule.span A {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} = ⊤`. Rewrite using `[eq_top_iff, ← β.span_eq]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `⟨p.1, p.2, p.2.2, hβ p⟩`.

Establish `hall' : Submodule.span A {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = (fun a => e (-a)) a * r ^ i} = ⊤`. Rewrite using `[eq_top_iff, ← hall]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, i, hi, rfl⟩`. Conclude with `⟨-a, i, hi, by simp⟩`.

Establish `hrel' : r ^ N ∈ Submodule.span A {x | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧ x = (fun a => e (-a)) b * r ^ i}`. Use `Submodule.span_mono ?_ hrel` and prove the remaining obligations. Introduce and unpack `_ ⟨b, i, hi, hb, rfl⟩`. Conclude with `⟨-b, i, hi, by simpa using hb, by simp⟩`. Establish `hB` using `chart_eq (A := A) e0 ea hrel`.

Establish `hC` using `chart_eq (A := A) (e := fun a => e (-a)) e0' ea' hrel'`. Establish `hsum : e 1 * e (-1) = 1` using `by rw [← ea]; simpa using e0`. Set `T : TC A (D)` to `{ B := Algebra.adjoin A {e 1, e 1 ^ k * r} C := Algebra.adjoin A {e (-1), e (-1) ^ k * r} t := e 1 s := e (-1) ts := hsum tB := Algebra.subset_adjoin (by simp) sC := Algebra.subset_adjoin (by simp) locB := chart_loc (k := k) e0 ea hall _ (Algebra.subset_adjoin (by simp)) (fun a i …`. Establish `h : e a * r ^ i ∈ Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r})`. Rewrite using `[hB]`.

Conclude with `Submodule.subset_span ⟨a, i, hi, ha, rfl⟩`. Conclude with `h)`. Use `locC := chart_loc (k := k) (e := fun a => e (-a)) e0' ea' hall' _ (Algebra.subset_adjoin (by simp)) (fun a i hi ha => by`. Establish `h : (fun a => e (-a)) a * r ^ i ∈ Subalgebra.toSubmodule (Algebra.adjoin A {(fun a => e (-a)) 1, (fun a => e (-a)) 1 ^ k * r})`. Rewrite using `[hC]`.

Conclude with `Submodule.subset_span ⟨a, i, hi, ha, rfl⟩`. Conclude with `h) }`. Use `⟨T, ?_, ?_, rfl, rfl, rfl, rfl⟩` and prove the remaining obligations. Use `⟨(Finset.range N).image (fun i => (e 1 ^ k * r) ^ i), ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨i, _, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `pow_mem (Algebra.subset_adjoin (by simp)) i`. Introduce `b hb`. Establish `hb' : b ∈ Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r})` using `hb`. Rewrite `hb'` using `[hB]`.

Use `Submodule.span_mono ?_ hb'` and prove the remaining obligations. Introduce and unpack `_ ⟨a, i, hi, ha, rfl⟩`. Conclude with `⟨(e 1 ^ k * r) ^ i, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩, (a - k * i).toNat, gen_eq e0 ea r k i a ha⟩`. Use `⟨ℤ × Fin N, β, {p | (k : ℤ) * ((p.2 : ℕ) : ℤ) ≤ p.1}, fun j => {p | p.1 ≤ (j : ℤ) - k * ((p.2 : ℕ) : ℤ)}, ?_, fun j => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `hB.trans (congrArg (Submodule.span A) (himg fun a i => (k : ℤ) * i ≤ a).symm)`.

Establish `hsj : e (-1) ^ j = e (-(j : ℤ))` using `e_pow (e := fun a => e (-a)) e0' ea' j`. Establish `hjj : e (-(j : ℤ)) * e j = 1` using `by rw [← ea]; simpa using e0`. Establish `hmap : (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j)) = (Subalgebra.toSubmodule T.C).map (LinearMap.mulLeft A (e j))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨e (-(j : ℤ)) * x, ?_, ?_⟩` and prove the remaining obligations. Establish `h : T.s ^ j * x ∈ Subalgebra.toSubmodule T.C` using `hx`. Rewrite `h` using `[show T.s ^ j = e (-(j : ℤ)) from hsj]`. Conclude with `h`.

Simplify using `only [LinearMap.mulLeft_apply]`. Rewrite using `[← mul_assoc, mul_comm (e j), hjj, one_mul]`. Introduce and unpack `⟨m, hm, rfl⟩`. Establish `h : T.s ^ j * (e j * m) = m`. Rewrite using `[show T.s ^ j = e (-(j : ℤ)) from hsj, ← mul_assoc, hjj, one_mul]`.

Use `show T.s ^ j * (e j * m) ∈ Subalgebra.toSubmodule T.C`. Rewrite using `[h]`. Conclude with `hm`. Establish `hC2 : Subalgebra.toSubmodule T.C = Submodule.span A {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧ x = (fun a => e (-a)) a * r ^ i}` using `hC`. Rewrite using `[hmap, hC2, Submodule.map_span]`.

Use `congrArg (Submodule.span A) ?_` and prove the remaining obligations. Use `Eq.trans ?_ (himg fun a i => a ≤ (j : ℤ) - k * i).symm` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, i, hi, ha, rfl⟩, rfl⟩`.

Use `⟨j - a, i, hi, by linarith, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.mulLeft_apply]`. Rewrite using `[← mul_assoc, ← ea, sub_eq_add_neg]`. Introduce and unpack `⟨a, i, hi, ha, rfl⟩`. Use `⟨_, ⟨j - a, i, hi, by linarith, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.mulLeft_apply]`. Rewrite using `[← mul_assoc, ← ea]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Use `Set.Finite.subset ((Set.finite_Icc (0 : ℤ) j).prod Set.finite_univ) ?_` and prove the remaining obligations.

Introduce and unpack `⟨a, i⟩ ⟨h1, h2⟩`. Establish `h1' : (k : ℤ) * ((i : ℕ) : ℤ) ≤ a` using `h1`. Establish `h2' : a ≤ (j : ℤ) - k * ((i : ℕ) : ℤ)` using `h2`. Establish `h0 : (0 : ℤ) ≤ k * ((i : ℕ) : ℤ)` using `by positivity`. Conclude with `⟨⟨by linarith, by linarith⟩, trivial⟩`.
-/
private theorem assemble {e : ℤ → D} (e0 : e 0 = 1) (ea : ∀ a b, e (a + b) = e a * e b) {r : D}
    {k N : ℕ} (β : Module.Basis (ℤ × Fin N) A D) (hβ : ∀ p, β p = e p.1 * r ^ (p.2 : ℕ))
    (hrel : r ^ N ∈ Submodule.span A
      {x : D | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧ x = e b * r ^ i}) :
    ∃ T : TC A D, T.Fin ∧ T.Coord ∧ T.t = e 1 ∧ T.s = e (-1) ∧
      T.B = Algebra.adjoin A {T.t, T.t ^ k * r} ∧ T.C = Algebra.adjoin A {T.s, T.s ^ k * r} := by
  classical
  have e0' : (fun a => e (-a)) 0 = 1 := by simpa using e0
  have ea' : ∀ a b, (fun a => e (-a)) (a + b) = (fun a => e (-a)) a * (fun a => e (-a)) b :=
    fun a b => by simp only [neg_add, ea]
  have himg : ∀ Q : ℤ → ℕ → Prop, β '' {p | Q p.1 p.2} =
      {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ Q a i ∧ x = e a * r ^ i} := by
    intro Q
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, p.2, p.2.2, hp, hβ p⟩
    · rintro ⟨a, i, hi, hq, rfl⟩
      exact ⟨(a, ⟨i, hi⟩), hq, hβ _⟩
  have hall : Submodule.span A
      {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = e a * r ^ i} = ⊤ := by
    rw [eq_top_iff, ← β.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨p, rfl⟩
    exact ⟨p.1, p.2, p.2.2, hβ p⟩
  have hall' : Submodule.span A
      {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ x = (fun a => e (-a)) a * r ^ i} = ⊤ := by
    rw [eq_top_iff, ← hall]
    apply Submodule.span_mono
    rintro _ ⟨a, i, hi, rfl⟩
    exact ⟨-a, i, hi, by simp⟩
  have hrel' : r ^ N ∈ Submodule.span A
      {x | ∃ (b : ℤ) (i : ℕ), i < N ∧ b.natAbs ≤ k ∧
        x = (fun a => e (-a)) b * r ^ i} := by
    refine Submodule.span_mono ?_ hrel
    rintro _ ⟨b, i, hi, hb, rfl⟩
    exact ⟨-b, i, hi, by simpa using hb, by simp⟩
  have hB := chart_eq (A := A) e0 ea hrel
  have hC := chart_eq (A := A) (e := fun a => e (-a)) e0' ea' hrel'
  have hsum : e 1 * e (-1) = 1 := by rw [← ea]; simpa using e0
  let T : TC A (D) :=
    { B := Algebra.adjoin A {e 1, e 1 ^ k * r}
      C := Algebra.adjoin A {e (-1), e (-1) ^ k * r}
      t := e 1
      s := e (-1)
      ts := hsum
      tB := Algebra.subset_adjoin (by simp)
      sC := Algebra.subset_adjoin (by simp)
      locB := chart_loc (k := k) e0 ea hall _ (Algebra.subset_adjoin (by simp)) (fun a i hi ha => by
        have h : e a * r ^ i ∈ Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r}) := by
          rw [hB]
          exact Submodule.subset_span ⟨a, i, hi, ha, rfl⟩
        exact h)
      locC := chart_loc (k := k) (e := fun a => e (-a)) e0' ea' hall' _ (Algebra.subset_adjoin (by simp)) (fun a i hi ha => by
        have h : (fun a => e (-a)) a * r ^ i ∈ Subalgebra.toSubmodule
            (Algebra.adjoin A {(fun a => e (-a)) 1, (fun a => e (-a)) 1 ^ k * r}) := by
          rw [hC]
          exact Submodule.subset_span ⟨a, i, hi, ha, rfl⟩
        exact h) }
  refine ⟨T, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · refine ⟨(Finset.range N).image (fun i => (e 1 ^ k * r) ^ i), ?_, ?_⟩
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
      exact pow_mem (Algebra.subset_adjoin (by simp)) i
    · intro b hb
      have hb' : b ∈ Subalgebra.toSubmodule (Algebra.adjoin A {e 1, e 1 ^ k * r}) := hb
      rw [hB] at hb'
      refine Submodule.span_mono ?_ hb'
      rintro _ ⟨a, i, hi, ha, rfl⟩
      exact ⟨(e 1 ^ k * r) ^ i, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩,
        (a - k * i).toNat, gen_eq e0 ea r k i a ha⟩
  · refine ⟨ℤ × Fin N, β, {p | (k : ℤ) * ((p.2 : ℕ) : ℤ) ≤ p.1},
      fun j => {p | p.1 ≤ (j : ℤ) - k * ((p.2 : ℕ) : ℤ)}, ?_, fun j => ⟨?_, ?_⟩⟩
    · exact hB.trans (congrArg (Submodule.span A) (himg fun a i => (k : ℤ) * i ≤ a).symm)
    · have hsj : e (-1) ^ j = e (-(j : ℤ)) := e_pow (e := fun a => e (-a)) e0' ea' j
      have hjj : e (-(j : ℤ)) * e j = 1 := by rw [← ea]; simpa using e0
      have hmap : (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j)) =
          (Subalgebra.toSubmodule T.C).map (LinearMap.mulLeft A (e j)) := by
        ext x
        constructor
        · intro hx
          refine ⟨e (-(j : ℤ)) * x, ?_, ?_⟩
          · have h : T.s ^ j * x ∈ Subalgebra.toSubmodule T.C := hx
            rw [show T.s ^ j = e (-(j : ℤ)) from hsj] at h
            exact h
          · simp only [LinearMap.mulLeft_apply]
            rw [← mul_assoc, mul_comm (e j), hjj, one_mul]
        · rintro ⟨m, hm, rfl⟩
          have h : T.s ^ j * (e j * m) = m := by
            rw [show T.s ^ j = e (-(j : ℤ)) from hsj, ← mul_assoc, hjj, one_mul]
          show T.s ^ j * (e j * m) ∈ Subalgebra.toSubmodule T.C
          rw [h]
          exact hm
      have hC2 : Subalgebra.toSubmodule T.C = Submodule.span A
          {x | ∃ (a : ℤ) (i : ℕ), i < N ∧ (k : ℤ) * i ≤ a ∧
            x = (fun a => e (-a)) a * r ^ i} := hC
      rw [hmap, hC2, Submodule.map_span]
      refine congrArg (Submodule.span A) ?_
      refine Eq.trans ?_ (himg fun a i => a ≤ (j : ℤ) - k * i).symm
      ext x
      constructor
      · rintro ⟨_, ⟨a, i, hi, ha, rfl⟩, rfl⟩
        refine ⟨j - a, i, hi, by linarith, ?_⟩
        simp only [LinearMap.mulLeft_apply]
        rw [← mul_assoc, ← ea, sub_eq_add_neg]
      · rintro ⟨a, i, hi, ha, rfl⟩
        refine ⟨_, ⟨j - a, i, hi, by linarith, rfl⟩, ?_⟩
        simp only [LinearMap.mulLeft_apply]
        rw [← mul_assoc, ← ea]
        congr 2
        ring
    · refine Set.Finite.subset ((Set.finite_Icc (0 : ℤ) j).prod Set.finite_univ) ?_
      rintro ⟨a, i⟩ ⟨h1, h2⟩
      have h1' : (k : ℤ) * ((i : ℕ) : ℤ) ≤ a := h1
      have h2' : a ≤ (j : ℤ) - k * ((i : ℕ) : ℤ) := h2
      have h0 : (0 : ℤ) ≤ k * ((i : ℕ) : ℤ) := by positivity
      exact ⟨⟨by linarith, by linarith⟩, trivial⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Set `pb` to `(AdjoinRoot.powerBasis' hP).basis.reindex (finCongr (AdjoinRoot.powerBasis'_dim hP))`. Use `⟨(AddMonoidAlgebra.basis ℤ A).smulTower pb, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.smulTower_apply, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen, Algebra.smul_def]`. Simplify using `only [AddMonoidAlgebra.basis_apply]`. Both sides reduce to the same expression.
-/
private theorem basis_model {A : Type} [CommRing A] {P : Polynomial (LaurentPolynomial A)}
    (hP : P.Monic) : ∃ β : Module.Basis (ℤ × Fin P.natDegree) A (AdjoinRoot P),
      ∀ p, β p = AdjoinRoot.of P (LaurentPolynomial.T p.1) * AdjoinRoot.root P ^ (p.2 : ℕ) := by
  let pb := (AdjoinRoot.powerBasis' hP).basis.reindex (finCongr (AdjoinRoot.powerBasis'_dim hP))
  refine ⟨(AddMonoidAlgebra.basis ℤ A).smulTower pb, fun p => ?_⟩
  rw [Module.Basis.smulTower_apply, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen, Algebra.smul_def]
  simp only [AddMonoidAlgebra.basis_apply]
  rfl

/- English proof (translation)
Establish `hof : ∀ (c : A) (x : LaurentPolynomial A), AdjoinRoot.of P (c • x) = c • AdjoinRoot.of P x`. Introduce `c x`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Establish `hev` using `congrArg (Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)) hP.as_sum`. Rewrite `hev` using `[AdjoinRoot.eval₂_root]`.

Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hev`. Establish `hr : AdjoinRoot.root P ^ P.natDegree = -∑ i ∈ Finset.range P.natDegree, AdjoinRoot.of P (P.coeff i) * AdjoinRoot.root P ^ i` using `eq_neg_of_add_eq_zero_left hev.symm`. Rewrite using `[hr]`. Use `neg_mem (sum_mem fun i hi => ?_)` and prove the remaining obligations. Establish `hi'` using `Finset.mem_range.1 hi`.

Establish `hc` using `hk i hi'`. Generalize the expression as in `P.coeff i = c at hc`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span ⟨b, i, hi', hb, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, add_mul]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx`. Rewrite using `[hof, smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
private theorem rel_model {A : Type} [CommRing A] {P : Polynomial (LaurentPolynomial A)}
    (hP : P.Monic) {k : ℕ} (hk : ∀ i < P.natDegree, P.coeff i ∈ Submodule.span A
      {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ k ∧ x = LaurentPolynomial.T b}) :
    AdjoinRoot.root P ^ P.natDegree ∈ Submodule.span A
      {x : AdjoinRoot P | ∃ (b : ℤ) (i : ℕ), i < P.natDegree ∧ b.natAbs ≤ k ∧
        x = AdjoinRoot.of P (LaurentPolynomial.T b) * AdjoinRoot.root P ^ i} := by
  have hof : ∀ (c : A) (x : LaurentPolynomial A),
      AdjoinRoot.of P (c • x) = c • AdjoinRoot.of P x := by
    intro c x
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]
  have hev := congrArg (Polynomial.eval₂ (AdjoinRoot.of P) (AdjoinRoot.root P)) hP.as_sum
  rw [AdjoinRoot.eval₂_root] at hev
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hev
  have hr : AdjoinRoot.root P ^ P.natDegree =
      -∑ i ∈ Finset.range P.natDegree, AdjoinRoot.of P (P.coeff i) * AdjoinRoot.root P ^ i :=
    eq_neg_of_add_eq_zero_left hev.symm
  rw [hr]
  refine neg_mem (sum_mem fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  have hc := hk i hi'
  generalize P.coeff i = c at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact Submodule.subset_span ⟨b, i, hi', hb, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, add_mul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [hof, smul_mul_assoc]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `A _ P hP k₀`. Take `⟨k, hk0, hk⟩ : ∃ k ≥ k₀, ∀ i < P.natDegree, P.coeff i ∈ Submodule.span A {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ k ∧ x = LaurentPolynomial.T b}` from `by choose f hf using fun i => exp_bound (P.coeff i)`. Use `⟨k₀ + ∑ i ∈ Finset.range P.natDegree, f i, Nat.le_add_right _ _, fun i hi => hf i _ ?_⟩` and prove the remaining obligations. Conclude with `(Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)).trans (Nat.le_add_left _ _)`. Establish `e0 : (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) 0 = 1` using `by show AdjoinRoot.of P (LaurentPolynomial.T 0) = 1`.

Rewrite using `[LaurentPolynomial.T_zero, map_one]`. Establish `ea : ∀ a b : ℤ, (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) (a + b) = (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) a * (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) b` using `fun a b => by show AdjoinRoot.of P (LaurentPolynomial.T (a + b)) = _`. Rewrite using `[LaurentPolynomial.T_add, map_mul]`. Take `⟨β, hβ⟩` from `basis_model hP`. Take `⟨T, h1, h2, h3, h4, h5, h6⟩` from `assemble (k := k) e0 ea β hβ (rel_model hP hk)`.

Conclude with `⟨k, hk0, T, h1, h2, h3, h4, h5, h6⟩`.
-/
theorem UpperTheory.exists_twoChart_adjoinRoot_laurent :
    ∀ (A : Type) [CommRing A] (P : Polynomial (LaurentPolynomial A)), P.Monic → ∀ k₀ : ℕ, ∃ k ≥ k₀, ∃ T : TC A (AdjoinRoot P), T.Fin ∧ T.Coord ∧
      T.t = AdjoinRoot.of P (LaurentPolynomial.T 1) ∧ T.s = AdjoinRoot.of P (LaurentPolynomial.T (-1)) ∧
      T.B = Algebra.adjoin A {T.t, T.t ^ k * AdjoinRoot.root P} ∧ T.C = Algebra.adjoin A {T.s, T.s ^ k * AdjoinRoot.root P} := by
  intro A _ P hP k₀
  obtain ⟨k, hk0, hk⟩ : ∃ k ≥ k₀, ∀ i < P.natDegree, P.coeff i ∈ Submodule.span A
      {x : LaurentPolynomial A | ∃ b : ℤ, b.natAbs ≤ k ∧ x = LaurentPolynomial.T b} := by
    choose f hf using fun i => exp_bound (P.coeff i)
    refine ⟨k₀ + ∑ i ∈ Finset.range P.natDegree, f i, Nat.le_add_right _ _, fun i hi => hf i _ ?_⟩
    exact (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)).trans
      (Nat.le_add_left _ _)
  have e0 : (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) 0 = 1 := by
    show AdjoinRoot.of P (LaurentPolynomial.T 0) = 1
    rw [LaurentPolynomial.T_zero, map_one]
  have ea : ∀ a b : ℤ, (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) (a + b) =
      (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) a *
        (fun a : ℤ => AdjoinRoot.of P (LaurentPolynomial.T a)) b := fun a b => by
    show AdjoinRoot.of P (LaurentPolynomial.T (a + b)) = _
    rw [LaurentPolynomial.T_add, map_mul]
  obtain ⟨β, hβ⟩ := basis_model hP
  obtain ⟨T, h1, h2, h3, h4, h5, h6⟩ := assemble (k := k) e0 ea β hβ (rel_model hP hk)
  exact ⟨k, hk0, T, h1, h2, h3, h4, h5, h6⟩

end
