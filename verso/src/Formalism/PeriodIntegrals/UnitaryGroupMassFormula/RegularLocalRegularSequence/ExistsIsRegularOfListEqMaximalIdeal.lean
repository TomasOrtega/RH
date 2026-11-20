import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne

namespace PI.UnitaryGroupMassFormula.RLRS

namespace IsRegularLocalRing

open IsLocalRing RingTheory.Sequence

open scoped Pointwise

universe u

/- English proof (translation)
Rewrite using `[isWeaklyRegular_cons_iff]`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Establish `h : (x • ⊤ : Submodule A A) = Ideal.span ({x} : Set A)`. Rewrite using `[← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]`. Establish `e : QuotSMulTop x A ≃ₗ[A] A ⧸ Ideal.span ({x} : Set A)` using `Submodule.quotEquivOfEq _ _ h`.

Rewrite using `[e.isWeaklyRegular_congr]`. Use `(isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.span ({x} : Set A)) (A ⧸ Ideal.span ({x} : Set A)) ys).mp ?_` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.algebraMap_eq]`. Conclude with `hys`.
-/
theorem isWeaklyRegular_cons_of_quotient {A : Type u} [CommRing A] {x : A}
    (hx : IsSMulRegular A x) (ys : List A)
    (hys : IsWeaklyRegular (A ⧸ Ideal.span ({x} : Set A))
      (ys.map (Ideal.Quotient.mk (Ideal.span ({x} : Set A))))) :
    IsWeaklyRegular A (x :: ys) := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨hx, ?_⟩
  have h : (x • ⊤ : Submodule A A) = Ideal.span ({x} : Set A) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have e : QuotSMulTop x A ≃ₗ[A] A ⧸ Ideal.span ({x} : Set A) :=
    Submodule.quotEquivOfEq _ _ h
  rw [e.isWeaklyRegular_congr]
  refine (isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.span ({x} : Set A))
    (A ⧸ Ideal.span ({x} : Set A)) ys).mp ?_
  rw [Ideal.Quotient.algebraMap_eq]
  exact hys

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _ _ h`. Use `⟨[], ?_, rfl, IsWeaklyRegular.nil A A⟩` and prove the remaining obligations.

Rewrite using `[Ideal.ofList_nil]`. Conclude with `((Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian (maximalIdeal A))).mp h).symm`. Consider the case `succ n IH`. Introduce `A _ _ h`. Establish `hsq : ¬ maximalIdeal A ≤ maximalIdeal A ^ 2`.

Introduce `hle`. Establish `hbot` using `maximalIdeal_eq_bot_of_le_sq A hle`. Rewrite `h` using `[hbot, Submodule.spanFinrank_bot]`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal A ∧ x ∉ maximalIdeal A ^ 2 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hsq fun y hy => hc y hy`. Establish `hreg : IsRegularLocalRing (A ⧸ Ideal.span ({x} : Set A))` using `quotient_span_singleton hx hx2`. Establish `hdim` using `spanFinrank_quotient_eq_and_ringKrullDim_add_one A hx hx2`.

Establish `hn : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = n`. Establish `h3 : ((Submodule.spanFinrank (maximalIdeal A) : ℕ) : WithBot ℕ∞) = ringKrullDim A` using `_root_.IsRegularLocalRing.spanFinrank_maximalIdeal`. Establish `h2` using `hdim.2`. Rewrite `h2` using `[← hdim.1, ← h3, h]`. Establish `h4 : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) + 1 = n + 1` using `by exact_mod_cast h2`.

Use linear arithmetic over natural numbers and integers. Take `⟨ys', hys'1, hys'2, hys'3⟩` from `IH (A ⧸ Ideal.span ({x} : Set A)) hn`. Establish `hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({x} : Set A)))` using `Ideal.Quotient.mk_surjective`. Establish `hmap : (ys'.map (Function.surjInv hsurj)).map (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) = ys'`. Rewrite using `[List.map_map]`.

Use `conv_rhs => rw [← List.map_id ys']`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `a _`. Conclude with `Function.surjInv_eq hsurj a`. Generalize the expression as in `hL : ys'.map (Function.surjInv hsurj) = L at hmap`.

Establish `hcomap : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = maximalIdeal A`. Establish `hmax` using `Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) hsurj (K := maximalIdeal (A ⧸ Ideal.span ({x} : Set A)))`. Conclude with `IsLocalRing.eq_maximalIdeal hmax`. Establish `hofl : Ideal.ofList (x :: L) = maximalIdeal A`. Rewrite using `[← hcomap, ← hys'1, ← hmap, ← Ideal.map_ofList, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.ofList_cons, sup_comm]`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx2 (zero_mem _)`. Establish `hxreg : IsSMulRegular A x` using `fun a b hab => mul_left_cancel₀ hx0 hab`. Use `⟨x :: L, hofl, by rw [← hL]; simp [hys'2], ?_⟩` and prove the remaining obligations.

Use `isWeaklyRegular_cons_of_quotient hxreg _ ?_` and prove the remaining obligations. Rewrite using `[hmap]`. Conclude with `hys'3`.
-/
theorem exists_list_of_spanFinrank_eq :
    ∀ (n : ℕ) (A : Type u) [CommRing A] [IsRegularLocalRing A],
      Submodule.spanFinrank (maximalIdeal A) = n →
      ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧ xs.length = n ∧
        IsWeaklyRegular A xs := by
  intro n
  induction n with
  | zero =>
    intro A _ _ h
    refine ⟨[], ?_, rfl, IsWeaklyRegular.nil A A⟩
    rw [Ideal.ofList_nil]
    exact ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (IsNoetherian.noetherian (maximalIdeal A))).mp h).symm
  | succ n IH =>
    intro A _ _ h
    have hsq : ¬ maximalIdeal A ≤ maximalIdeal A ^ 2 := by
      intro hle
      have hbot := maximalIdeal_eq_bot_of_le_sq A hle
      rw [hbot, Submodule.spanFinrank_bot] at h
      omega
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal A ∧ x ∉ maximalIdeal A ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have hreg : IsRegularLocalRing (A ⧸ Ideal.span ({x} : Set A)) :=
      quotient_span_singleton hx hx2
    have hdim := spanFinrank_quotient_eq_and_ringKrullDim_add_one A hx hx2
    have hn : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = n := by
      have h3 : ((Submodule.spanFinrank (maximalIdeal A) : ℕ) : WithBot ℕ∞) = ringKrullDim A :=
        _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
      have h2 := hdim.2
      rw [← hdim.1, ← h3, h] at h2
      have h4 : Submodule.spanFinrank (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) + 1
          = n + 1 := by exact_mod_cast h2
      omega
    obtain ⟨ys', hys'1, hys'2, hys'3⟩ := IH (A ⧸ Ideal.span ({x} : Set A)) hn
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) :=
      Ideal.Quotient.mk_surjective
    have hmap : (ys'.map (Function.surjInv hsurj)).map
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) = ys' := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id ys']
      apply List.map_congr_left
      intro a _
      exact Function.surjInv_eq hsurj a
    generalize hL : ys'.map (Function.surjInv hsurj) = L at hmap
    have hcomap : Ideal.comap (Ideal.Quotient.mk (Ideal.span ({x} : Set A)))
        (maximalIdeal (A ⧸ Ideal.span ({x} : Set A))) = maximalIdeal A := by
      have hmax := Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk (Ideal.span ({x} : Set A))) hsurj
        (K := maximalIdeal (A ⧸ Ideal.span ({x} : Set A)))
      exact IsLocalRing.eq_maximalIdeal hmax
    have hofl : Ideal.ofList (x :: L) = maximalIdeal A := by
      rw [← hcomap, ← hys'1, ← hmap, ← Ideal.map_ofList,
        Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        Ideal.ofList_cons, sup_comm]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx2 (zero_mem _)
    have hxreg : IsSMulRegular A x := fun a b hab => mul_left_cancel₀ hx0 hab
    refine ⟨x :: L, hofl, by rw [← hL]; simp [hys'2], ?_⟩
    refine isWeaklyRegular_cons_of_quotient hxreg _ ?_
    rw [hmap]
    exact hys'3

/- English proof (translation)
Take `⟨xs, h1, h2, h3⟩` from `exists_list_of_spanFinrank_eq _ A rfl`. Use `⟨xs, h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `_root_.IsRegularLocalRing.spanFinrank_maximalIdeal`. Use `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A ?_ h3` and prove the remaining obligations.

Introduce `r hr`. Rewrite using `[← h1]`. Conclude with `Ideal.subset_span hr`.
-/
theorem exists_isRegular_ofList_eq_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧
      (xs.length : WithBot ℕ∞) = ringKrullDim A ∧ IsRegular A xs := by
  obtain ⟨xs, h1, h2, h3⟩ := exists_list_of_spanFinrank_eq _ A rfl
  refine ⟨xs, h1, ?_, ?_⟩
  · rw [h2]
    exact _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
  · refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A ?_ h3
    intro r hr
    rw [← h1]
    exact Ideal.subset_span hr

end IsRegularLocalRing

end PI.UnitaryGroupMassFormula.RLRS
