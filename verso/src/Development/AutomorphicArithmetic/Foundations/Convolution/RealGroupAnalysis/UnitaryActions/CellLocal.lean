import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.FiniteProjectionSingleSame

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `R _ _ ι s c d hj hcd`. Assume the negation of the conclusion as `hcon`. Establish `hbad : ∀ x : ℕ, ∃ i, i ∈ s ∧ ¬ IsUnit (c i + d i * x)`. Introduce `x`. Assume the negation of the conclusion as `h`.

Conclude with `hcon ⟨x, fun i hi => by`. Assume the negation of the conclusion as `h'`. Conclude with `h ⟨i, hi, h'⟩⟩`. Use `choose f hfs hf using hbad`. Establish `key : ∀ x y : ℕ, x < y → y ≤ s.card → f x = f y → False`.

Introduce `x y hxy hy he`. Establish `h1 : c (f x) + d (f x) * x ∈ IsLocalRing.maximalIdeal R` using `hf x`. Establish `h2 : c (f x) + d (f x) * y ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[he]`. Conclude with `hf y`.

Establish `hu : IsUnit ((y - x : ℕ) : R)` using `hj _ (by omega) (by omega)`. Establish `h3 : d (f x) * ((y - x : ℕ) : R) ∈ IsLocalRing.maximalIdeal R`. Use `Ideal.sub_mem _ h2 h1` as an intermediate fact. Rewrite using `[Nat.cast_sub hxy.le]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : d (f x) ∈ IsLocalRing.maximalIdeal R`. Introduce `hd`. Conclude with `h3 (hd.mul hu)`. Establish `h5 : c (f x) ∈ IsLocalRing.maximalIdeal R`.

Use `Ideal.sub_mem _ h1 (Ideal.mul_mem_right (x : R) _ h4)` as an intermediate fact. Simplify using `using this`. Break down `hcd _ (hfs x) with h | h` into its components or cases. Conclude with `h5 h`. Conclude with `h4 h`.

Take `⟨x, hx, y, hy, hne, he⟩` from `Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (s.card + 1)) (t := s) (by simp) (f := f) (fun x _ => hfs x)`. Rewrite `hx`, `hy` using `[Finset.mem_range]`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `key x y h (by omega) he`. Conclude with `key y x h (by omega) he.symm`.
-/
theorem UpperTheory.ConvolutionTheory.R2.cellLocal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (ι : Type) (s : Finset ι) (c d : ι → R),
      (∀ j : ℕ, 0 < j → j ≤ s.card → IsUnit (j : R)) → (∀ i ∈ s, IsUnit (c i) ∨ IsUnit (d i)) →
        ∃ x : ℕ, ∀ i ∈ s, IsUnit (c i + d i * x) := by
  intro R _ _ ι s c d hj hcd
  by_contra hcon
  have hbad : ∀ x : ℕ, ∃ i, i ∈ s ∧ ¬ IsUnit (c i + d i * x) := by
    intro x
    by_contra h
    exact hcon ⟨x, fun i hi => by
      by_contra h'
      exact h ⟨i, hi, h'⟩⟩
  choose f hfs hf using hbad
  have key : ∀ x y : ℕ, x < y → y ≤ s.card → f x = f y → False := by
    intro x y hxy hy he
    have h1 : c (f x) + d (f x) * x ∈ IsLocalRing.maximalIdeal R := hf x
    have h2 : c (f x) + d (f x) * y ∈ IsLocalRing.maximalIdeal R := by
      rw [he]; exact hf y
    have hu : IsUnit ((y - x : ℕ) : R) := hj _ (by omega) (by omega)
    have h3 : d (f x) * ((y - x : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h2 h1
      rw [Nat.cast_sub hxy.le]
      convert this using 1
      ring
    have h4 : d (f x) ∈ IsLocalRing.maximalIdeal R := by
      intro hd
      exact h3 (hd.mul hu)
    have h5 : c (f x) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ h1 (Ideal.mul_mem_right (x : R) _ h4)
      simpa using this
    rcases hcd _ (hfs x) with h | h
    · exact h5 h
    · exact h4 h
  obtain ⟨x, hx, y, hy, hne, he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (s.card + 1)) (t := s)
      (by simp) (f := f) (fun x _ => hfs x)
  rw [Finset.mem_range] at hx hy
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y h (by omega) he
  · exact key y x h (by omega) he.symm
