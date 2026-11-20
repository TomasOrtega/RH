import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `A G _ _ _ _ _ P hP hnil`. Set `N : Subalgebra A G` to `{ carrier := {y | ∃ a : A, IsNilpotent (y - algebraMap A G a)} mul_mem' := by`. Introduce and unpack `x y ⟨a, ha⟩ ⟨b, hb⟩`. Use `⟨a * b, ?_⟩` and prove the remaining obligations. Establish `e : x * y - algebraMap A G (a * b) = (x - algebraMap A G a) * y + algebraMap A G a * (y - algebraMap A G b)`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Take `⟨k, hk⟩` from `ha`. Take `⟨m, hm⟩` from `hb`.

Conclude with `(Commute.all _ _).isNilpotent_add ⟨k, by rw [mul_pow, hk, zero_mul]⟩ ⟨m, by rw [mul_pow, hm, mul_zero]⟩`. Use the proof step `add_mem' := by`. Introduce and unpack `x y ⟨a, ha⟩ ⟨b, hb⟩`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Establish `e : x + y - algebraMap A G (a + b) = (x - algebraMap A G a) + (y - algebraMap A G b)`.

Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(Commute.all _ _).isNilpotent_add ha hb`. Use the proof step `algebraMap_mem' := fun r => ⟨r, by simp⟩ }`.

Establish `hS : Algebra.adjoin A (P : Set G) ≤ N` using `Algebra.adjoin_le (fun y hy => hnil y hy)`. Establish `hint : ∀ y, (∃ a : A, IsNilpotent (y - algebraMap A G a)) → IsIntegral A y`. Introduce and unpack `y ⟨a, k, hk⟩`. Establish `hn : IsIntegral A (y - algebraMap A G a)` using `⟨X ^ k, monic_X_pow k, by simp [hk]⟩`. Use `hn.add (isIntegral_algebraMap (x := a))` as an intermediate fact.

Simplify using `using this`. Use `⟨?_, ?_, fun y hy => hS hy⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hP`. Rewrite using `[← hs, Algebra.adjoin_span]`. Conclude with `Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun y hy => hint y (hnil y (hs ▸ Submodule.subset_span hy)))`.

Apply `IsLocalRing.of_isUnit_or_isUnit_one_sub_self` to reduce the goal to its premises. Introduce `y`. Take `⟨a, ha⟩` from `hS y.2`. Set `n : Algebra.adjoin A (P : Set G)` to `⟨(y : G) - algebraMap A G a, Subalgebra.sub_mem _ y.2 (Subalgebra.algebraMap_mem _ a)⟩`. Establish `hn : IsNilpotent n`.

Take `⟨k, hk⟩` from `ha`. Conclude with `⟨k, Subtype.ext (by simpa [n] using hk)⟩`. Establish `hy : y = algebraMap A _ a + n` using `Subtype.ext (by simp [n])`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu` into its components or cases. Use `left`.

Rewrite using `[hy, add_comm]`. Conclude with `hn.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)`. Use `right`. Establish `e : 1 - y = algebraMap A _ (1 - a) + (-n)`. Rewrite using `[hy, map_sub, map_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, add_comm]`. Conclude with `hn.neg.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)`.
-/
theorem UpperTheory.V.AlgebraTools.adjoin_nil_finite :
    ∀ {A G : Type} [CommRing A] [IsLocalRing A] [CommRing G] [Algebra A G] [Nontrivial G] (P : Submodule A G), P.FG → (∀ y ∈ P, ∃ a : A, IsNilpotent (y - algebraMap A G a)) → Module.Finite A (Algebra.adjoin A (P : Set G)) ∧ IsLocalRing (Algebra.adjoin A (P : Set G)) ∧ ∀ y ∈ Algebra.adjoin A (P : Set G), ∃ a : A, IsNilpotent (y - algebraMap A G a) := by
  intro A G _ _ _ _ _ P hP hnil
  let N : Subalgebra A G :=
    { carrier := {y | ∃ a : A, IsNilpotent (y - algebraMap A G a)}
      mul_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        have e : x * y - algebraMap A G (a * b) =
            (x - algebraMap A G a) * y + algebraMap A G a * (y - algebraMap A G b) := by
          rw [map_mul]; ring
        rw [e]
        obtain ⟨k, hk⟩ := ha
        obtain ⟨m, hm⟩ := hb
        exact (Commute.all _ _).isNilpotent_add ⟨k, by rw [mul_pow, hk, zero_mul]⟩
          ⟨m, by rw [mul_pow, hm, mul_zero]⟩
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        have e : x + y - algebraMap A G (a + b) =
            (x - algebraMap A G a) + (y - algebraMap A G b) := by
          rw [map_add]; ring
        rw [e]
        exact (Commute.all _ _).isNilpotent_add ha hb
      algebraMap_mem' := fun r => ⟨r, by simp⟩ }
  have hS : Algebra.adjoin A (P : Set G) ≤ N := Algebra.adjoin_le (fun y hy => hnil y hy)
  have hint : ∀ y, (∃ a : A, IsNilpotent (y - algebraMap A G a)) → IsIntegral A y := by
    rintro y ⟨a, k, hk⟩
    have hn : IsIntegral A (y - algebraMap A G a) :=
      ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
    have := hn.add (isIntegral_algebraMap (x := a))
    simpa using this
  refine ⟨?_, ?_, fun y hy => hS hy⟩
  · obtain ⟨s, hs⟩ := hP
    rw [← hs, Algebra.adjoin_span]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun y hy => hint y (hnil y (hs ▸ Submodule.subset_span hy)))
  · apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro y
    obtain ⟨a, ha⟩ := hS y.2
    let n : Algebra.adjoin A (P : Set G) :=
      ⟨(y : G) - algebraMap A G a, Subalgebra.sub_mem _ y.2 (Subalgebra.algebraMap_mem _ a)⟩
    have hn : IsNilpotent n := by
      obtain ⟨k, hk⟩ := ha
      exact ⟨k, Subtype.ext (by simpa [n] using hk)⟩
    have hy : y = algebraMap A _ a + n := Subtype.ext (by simp [n])
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
    · left
      rw [hy, add_comm]
      exact hn.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
    · right
      have e : 1 - y = algebraMap A _ (1 - a) + (-n) := by
        rw [hy, map_sub, map_one]; ring
      rw [e, add_comm]
      exact hn.neg.isUnit_add_right_of_commute (hu.map _) (Commute.all _ _)
