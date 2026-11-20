import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Establish `hl0 : l ≠ 0` using `hl.ne_zero`. Establish `hln : l * n ≠ 0` using `mul_ne_zero hl0 hn`. Simplify using `only [eis, hln, hn, if_false]`. Rewrite using `[Finset.mul_sum]`. Use `symm`.

Use `Finset.sum_bij_ne_zero (fun p _ _ => (p.1, l * p.2)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp _`. Rewrite `hp`, the goal using `[Nat.mem_divisorsAntidiagonal]`. Use `⟨?_, hln⟩` and prove the remaining obligations. Rewrite using `[← hp.1]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `p _ _ q _ _ h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hl.pos h.2)`. Introduce `q hq hne`.

Rewrite `hq` using `[Nat.mem_divisorsAntidiagonal]`. Establish `h1 : ¬ l ∣ q.1`. Introduce `hd`. Apply `hne` to reduce the goal to its premises. Rewrite using `[ha q.1 (by exact_mod_cast hd)]; ring`.

Establish `h2 : l ∣ q.2`. Establish `: l ∣ q.1 * q.2` using `by rw [hq.1]; exact dvd_mul_right _ _`. Conclude with `(hl.dvd_mul.mp this).resolve_left h1`. Take `⟨y, hy⟩` from `h2`. Use `⟨(q.1, y), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.mem_divisorsAntidiagonal]`. Use `⟨?_, hn⟩` and prove the remaining obligations. Establish `h` using `hq.1`. Rewrite `h` using `[hy]`. Establish `: l * (q.1 * y) = l * n` using `by rw [← h]; ring`.

Conclude with `Nat.eq_of_mul_eq_mul_left hl.pos this`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `: b (q.2 : ℤ) = t * b (y : ℤ)` using `by rw [hy]; push_cast; exact hb _`. Rewrite using `[this]`.

Simplify using `only at h0`. Take the linear combination `h0`. Apply the tactic sequence `ext <;> simp [hy]`. Introduce `p _ _`. Simplify using `only`.

Use `push_cast`. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eis_U_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) (hb : ∀ y, b (l * y) = t * b y) (n : ℕ) (hn : n ≠ 0) :
    eis j c a b (l * n) = t * eis j c a b n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  have hln : l * n ≠ 0 := mul_ne_zero hl0 hn
  simp only [eis, hln, hn, if_false]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1, l * p.2)) ?_ ?_ ?_ ?_
  · intro p hp _
    rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
    refine ⟨?_, hln⟩
    rw [← hp.1]; ring
  · intro p _ _ q _ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hl.pos h.2)
  · intro q hq hne
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have h1 : ¬ l ∣ q.1 := by
      intro hd
      apply hne
      rw [ha q.1 (by exact_mod_cast hd)]; ring
    have h2 : l ∣ q.2 := by
      have : l ∣ q.1 * q.2 := by rw [hq.1]; exact dvd_mul_right _ _
      exact (hl.dvd_mul.mp this).resolve_left h1
    obtain ⟨y, hy⟩ := h2
    refine ⟨(q.1, y), ?_, ?_, ?_⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, hn⟩
      have h := hq.1
      rw [hy] at h
      have : l * (q.1 * y) = l * n := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hl.pos this
    · intro h0
      apply hne
      have : b (q.2 : ℤ) = t * b (y : ℤ) := by rw [hy]; push_cast; exact hb _
      rw [this]
      simp only at h0
      linear_combination h0
    · ext <;> simp [hy]
  · intro p _ _
    simp only
    push_cast
    rw [hb]; ring

/- English proof (translation)
Establish `hl0 : l ≠ 0` using `hl.ne_zero`. Distinguish the cases in `hd : l ∣ n`. Take `⟨m, rfl⟩` from `hd`. Establish `hm : m ≠ 0` using `by rintro rfl; simp at hn`. Simplify using `only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl.pos]`.

Simplify using `only [eis, hn, hm, if_false]`. Rewrite using `[Finset.mul_sum]`. Use `symm`. Use `Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1, p.2)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp _`.

Rewrite `hp`, the goal using `[Nat.mem_divisorsAntidiagonal]`. Use `⟨?_, hn⟩` and prove the remaining obligations. Rewrite using `[← hp.1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `p _ _ q _ _ h`.

Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext (Nat.eq_of_mul_eq_mul_left hl.pos h.1) h.2`. Introduce `q hq hne`. Rewrite `hq` using `[Nat.mem_divisorsAntidiagonal]`. Establish `h1 : l ∣ q.1`.

Assume the negation of the conclusion as `h`. Apply `hne` to reduce the goal to its premises. Establish `: ¬ (l : ℤ) ∣ (q.1 : ℤ)` using `by exact_mod_cast h`. Simplify using `[this]`. Take `⟨x, hx⟩` from `h1`.

Use `⟨(x, q.2), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.mem_divisorsAntidiagonal]`. Use `⟨?_, hm⟩` and prove the remaining obligations. Establish `h` using `hq.1`. Rewrite `h` using `[hx]`.

Establish `: l * (x * q.2) = l * m` using `by rw [← h]; ring`. Conclude with `Nat.eq_of_mul_eq_mul_left hl.pos this`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `hdv : (l : ℤ) ∣ (q.1 : ℤ)` using `by rw [hx]; push_cast; exact dvd_mul_right _ _`.

Simplify using `only [hdv, if_true]`. Establish `: a (q.1 : ℤ) = t * a (x : ℤ)` using `by rw [hx]; push_cast; exact ha _`. Rewrite using `[this, hx]`. Simplify using `only at h0`. Use `push_cast`.

Rewrite using `[mul_pow]`. Take the linear combination `h0`. Apply the tactic sequence `ext <;> simp [hx]`. Introduce `p _ _`. Establish `hdv : (l : ℤ) ∣ ((l * p.1 : ℕ) : ℤ)` using `by push_cast; exact dvd_mul_right _ _`.

Simplify using `only [hdv, if_true]`. Use `push_cast`. Rewrite using `[ha, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : Vo l (eis j c a b) n = 0` using `by simp [Vo, hd]`.

Rewrite using `[h0, mul_zero]`. Simplify using `only [eis, hn, if_false]`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations. Rewrite `hq` using `[Nat.mem_divisorsAntidiagonal]`. Establish `: ¬ (l : ℤ) ∣ (q.1 : ℤ)`.

Introduce `h`. Apply `hd` to reduce the goal to its premises. Establish `h' : l ∣ q.1` using `by exact_mod_cast h`. Rewrite using `[← hq.1]`. Conclude with `dvd_mul_of_dvd_left h' _`.

Simplify using `[this]`.
-/
theorem eis_V_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x, a (l * x) = t * a x) (n : ℕ) (hn : n ≠ 0) :
    eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  by_cases hd : l ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl.pos]
    simp only [eis, hn, hm, if_false]
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp _
      rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
      refine ⟨?_, hn⟩
      rw [← hp.1]; ring
    · intro p _ _ q _ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl.pos h.1) h.2
    · intro q hq hne
      rw [Nat.mem_divisorsAntidiagonal] at hq
      have h1 : l ∣ q.1 := by
        by_contra h
        apply hne
        have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by exact_mod_cast h
        simp [this]
      obtain ⟨x, hx⟩ := h1
      refine ⟨(x, q.2), ?_, ?_, ?_⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        refine ⟨?_, hm⟩
        have h := hq.1
        rw [hx] at h
        have : l * (x * q.2) = l * m := by rw [← h]; ring
        exact Nat.eq_of_mul_eq_mul_left hl.pos this
      · intro h0
        apply hne
        have hdv : (l : ℤ) ∣ (q.1 : ℤ) := by rw [hx]; push_cast; exact dvd_mul_right _ _
        simp only [hdv, if_true]
        have : a (q.1 : ℤ) = t * a (x : ℤ) := by rw [hx]; push_cast; exact ha _
        rw [this, hx]
        simp only at h0
        push_cast
        rw [mul_pow]
        linear_combination h0
      · ext <;> simp [hx]
    · intro p _ _
      have hdv : (l : ℤ) ∣ ((l * p.1 : ℕ) : ℤ) := by push_cast; exact dvd_mul_right _ _
      simp only [hdv, if_true]
      push_cast
      rw [ha, mul_pow]; ring
  · have h0 : Vo l (eis j c a b) n = 0 := by simp [Vo, hd]
    rw [h0, mul_zero]
    simp only [eis, hn, if_false]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by
      intro h
      apply hd
      have h' : l ∣ q.1 := by exact_mod_cast h
      rw [← hq.1]; exact dvd_mul_of_dvd_left h' _
    simp [this]

/- English proof (translation)
Introduce `hl` and use `⟨fun ha hb n hn => eis_U_pair j l c t a b hl ha hb n hn, fun _ ha n hn => eis_V_pair j l c t a b hl ha n hn⟩`.
-/
theorem eis_U_V (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) : l.Prime → ((∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) → (∀ y, b (l * y) = t * b y) → ∀ n, n ≠ 0 → eis j c a b (l * n) = t * eis j c a b n) ∧ (1 ≤ j → (∀ x, a (l * x) = t * a x) → ∀ n, n ≠ 0 → eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n) :=
  fun hl => ⟨fun ha hb n hn => eis_U_pair j l c t a b hl ha hb n hn,
    fun _ ha n hn => eis_V_pair j l c t a b hl ha n hn⟩

end GlobalTheory
