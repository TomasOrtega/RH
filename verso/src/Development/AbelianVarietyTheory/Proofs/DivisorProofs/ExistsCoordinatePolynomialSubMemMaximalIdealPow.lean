import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

/- English proof (translation)
Use `set P := Subring.closure (Set.range inc ∪ Set.range z) with hP`. Use `set m := maximalIdeal A with hmdef`. Establish `incP : ∀ r, inc r ∈ P` using `fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)`. Establish `zP : ∀ i, z i ∈ P` using `fun i => Subring.subset_closure (Or.inr ⟨i, rfl⟩)`. Establish `hker : ∀ x : A, x - inc (ev x) ∈ m`.

Introduce `x`. Establish `h1 : x - inc (ev x) ∈ RingHom.ker ev`. Simplify using `[RingHom.mem_ker, hev]`. Conclude with `le_maximalIdeal (RingHom.ker_ne_top ev) h1`. Set `C : ℕ → Ideal A` to `fun j => { carrier := {x | ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1)} add_mem' := by`.

Introduce and unpack `a b ⟨q, hq, hqm, hqe⟩ ⟨q', hq', hqm', hqe'⟩`. Use `⟨q + q', P.add_mem hq hq', Ideal.add_mem _ hqm hqm', ?_⟩` and prove the remaining obligations. Establish `: a + b - (q + q') = (a - q) + (b - q')` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ hqe hqe'`.

Use the proof step `zero_mem' := ⟨0, P.zero_mem, Ideal.zero_mem _, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨q, hq, hqm, hqe⟩`. Use `⟨inc (ev c) * q, P.mul_mem (incP _) hq, Ideal.mul_mem_left _ _ hqm, ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ m ^ j`.

Establish `: x = q + (x - q)` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ hqm (Ideal.pow_le_pow_right (Nat.le_succ j) hqe)`. Establish `: c • x - inc (ev c) * q = inc (ev c) * (x - q) + (c - inc (ev c)) * x`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqe) ?_` and prove the remaining obligations. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul (hker c) hx }`.

Establish `memC : ∀ j x, x ∈ C j ↔ ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1)` using `fun _ _ => Iff.rfl`. Establish `hC1 : m ≤ C 1`. Combine the equalities or inequalities in the displayed calculation. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `r hr`. Use `(memC _ _).2 ⟨inc r, incP r, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[pow_one, hm]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr)`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `(memC _ _).2 ⟨z i, zP i, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[pow_one, hm]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)`. Establish `hCj : ∀ j, m ^ j ≤ C j`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `x _`. Conclude with `(memC _ _).2 ⟨inc (ev x), incP _, by simp, by simpa using hker x⟩`.

Consider the case `succ j ih`. Rewrite using `[pow_succ]`. Use `Ideal.mul_le.2 fun y hy w hw => ?_` and prove the remaining obligations. Take `⟨q, hq, hqm, hqe⟩` from `(memC _ _).1 (ih hy)`. Take `⟨q1, hq1, hq1m, hq1e⟩` from `(memC _ _).1 (hC1 hw)`.

Use `(memC _ _).2 ⟨q * q1, P.mul_mem hq hq1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ]; exact Ideal.mul_mem_mul hqm (by simpa using hq1m)`. Establish `: y * w - q * q1 = q * (w - q1) + (y - q) * w` using `by ring`. Rewrite using `[this]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations.

Establish `: m ^ (j + 1 + 1) = m ^ j * m ^ (1 + 1)` using `by rw [← pow_add]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_mul hqm hq1e`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hqe hw`.

Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, P.zero_mem, by simp⟩`. Consider the case `succ k ih`. Take `⟨p, hp, hfp⟩` from `ih`. Take `⟨q, hq, -, hqe⟩` from `(memC _ _).1 (hCj k hfp)`.

Use `⟨p + q, P.add_mem hp hq, ?_⟩` and prove the remaining obligations. Rewrite using `[show f - (p + q) = f - p - q by ring]`. Conclude with `hqe`.
-/
theorem exists_mem_closure_sub_mem_maximalIdeal_pow
    (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) (n : ℕ) (z : Fin n → A)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z))
    (k : ℕ) (f : A) :
    ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  set P := Subring.closure (Set.range inc ∪ Set.range z) with hP
  set m := maximalIdeal A with hmdef
  have incP : ∀ r, inc r ∈ P := fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have zP : ∀ i, z i ∈ P := fun i => Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  have hker : ∀ x : A, x - inc (ev x) ∈ m := by
    intro x
    have h1 : x - inc (ev x) ∈ RingHom.ker ev := by
      simp [RingHom.mem_ker, hev]
    exact le_maximalIdeal (RingHom.ker_ne_top ev) h1
  let C : ℕ → Ideal A := fun j =>
    { carrier := {x | ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1)}
      add_mem' := by
        rintro a b ⟨q, hq, hqm, hqe⟩ ⟨q', hq', hqm', hqe'⟩
        refine ⟨q + q', P.add_mem hq hq', Ideal.add_mem _ hqm hqm', ?_⟩
        have : a + b - (q + q') = (a - q) + (b - q') := by ring
        rw [this]; exact Ideal.add_mem _ hqe hqe'
      zero_mem' := ⟨0, P.zero_mem, Ideal.zero_mem _, by simp⟩
      smul_mem' := by
        rintro c x ⟨q, hq, hqm, hqe⟩
        refine ⟨inc (ev c) * q, P.mul_mem (incP _) hq, Ideal.mul_mem_left _ _ hqm, ?_⟩
        have hx : x ∈ m ^ j := by
          have : x = q + (x - q) := by ring
          rw [this]; exact Ideal.add_mem _ hqm (Ideal.pow_le_pow_right (Nat.le_succ j) hqe)
        have : c • x - inc (ev c) * q = inc (ev c) * (x - q) + (c - inc (ev c)) * x := by
          simp only [smul_eq_mul]; ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqe) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hker c) hx }
  have memC : ∀ j x, x ∈ C j ↔ ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1) := fun _ _ => Iff.rfl
  have hC1 : m ≤ C 1 := by
    calc m = _ := hm
      _ ≤ C 1 := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro r hr
          refine (memC _ _).2 ⟨inc r, incP r, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr)
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          refine (memC _ _).2 ⟨z i, zP i, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hCj : ∀ j, m ^ j ≤ C j := by
    intro j
    induction j with
    | zero =>
      intro x _
      exact (memC _ _).2 ⟨inc (ev x), incP _, by simp, by simpa using hker x⟩
    | succ j ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun y hy w hw => ?_
      obtain ⟨q, hq, hqm, hqe⟩ := (memC _ _).1 (ih hy)
      obtain ⟨q1, hq1, hq1m, hq1e⟩ := (memC _ _).1 (hC1 hw)
      refine (memC _ _).2 ⟨q * q1, P.mul_mem hq hq1, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul hqm (by simpa using hq1m)
      · have : y * w - q * q1 = q * (w - q1) + (y - q) * w := by ring
        rw [this]
        refine Ideal.add_mem _ ?_ ?_
        · have : m ^ (j + 1 + 1) = m ^ j * m ^ (1 + 1) := by rw [← pow_add]
          rw [this]; exact Ideal.mul_mem_mul hqm hq1e
        · rw [pow_succ]; exact Ideal.mul_mem_mul hqe hw
  induction k with
  | zero => exact ⟨0, P.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hfp⟩ := ih
    obtain ⟨q, hq, -, hqe⟩ := (memC _ _).1 (hCj k hfp)
    refine ⟨p + q, P.add_mem hp hq, ?_⟩
    rw [show f - (p + q) = f - p - q by ring]
    exact hqe

end GlobalTheory
