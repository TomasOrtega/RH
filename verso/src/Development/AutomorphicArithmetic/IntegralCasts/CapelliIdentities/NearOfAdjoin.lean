import Mathlib

/- English proof (translation)
Introduce `P L _ _ _ G hG x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy => exact ⟨0, by simpa using hG y hy⟩`. Consider the case `algebraMap r => exact ⟨r, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨p, hp⟩` from `hy`. Take `⟨q, hq⟩` from `hz`. Use `⟨p + q, ?_⟩` and prove the remaining obligations. Establish `h` using `(Commute.all _ _).isNilpotent_add hp hq`. Use `h using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul y z _ _ hy hz`. Take `⟨p, hp⟩` from `hy`. Take `⟨q, hq⟩` from `hz`.

Use `⟨p * q, ?_⟩` and prove the remaining obligations. Rewrite `hp`, `hq`, the goal using `[← mem_nilradical]`. Establish `h` using `(nilradical L).add_mem ((nilradical L).mul_mem_right z hp) ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Reformulated.B.Qg2.near_of_adjoin :
    ∀ {P L : Type} [inst : CommRing P] [inst_1 : CommRing L]
    [inst_2 : Algebra P L] (G : Set L),
    (∀ g ∈ G, IsNilpotent g) →
      ∀ x ∈ Algebra.adjoin P G, ∃ (p : P), IsNilpotent (x - (Algebra.algebraMap P L : P → L) p) := by
  intro P L _ _ _ G hG x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, by simpa using hG y hy⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    have h := (Commute.all _ _).isNilpotent_add hp hq
    convert h using 1
    rw [map_add]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p * q, ?_⟩
    rw [← mem_nilradical] at hp hq ⊢
    have h := (nilradical L).add_mem ((nilradical L).mul_mem_right z hp)
      ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)
    convert h using 1
    rw [map_mul]
    ring
