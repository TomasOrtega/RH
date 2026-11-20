import Mathlib
open MvPolynomial

namespace GlobalTheory
namespace GaussContentLinearForms

variable {V : Type} [CommRing V] {σ : Type}

/- English proof (translation)
Rewrite using `[Ideal.span_mul_span']`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [coeff_C_mul, Set.mem_range, Set.mem_mul, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨a, rfl, _, ⟨s, rfl⟩, rfl⟩`. Introduce and unpack `⟨b, rfl, y, ⟨s, rfl⟩, rfl⟩`. Conclude with `⟨s, rfl⟩`.
-/
theorem span_coeff_C_mul (a : V) (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (C a * f).coeff s) =
      Ideal.span {a} * Ideal.span (Set.range fun s => f.coeff s) := by
  rw [Ideal.span_mul_span']
  congr 1
  ext x
  simp only [coeff_C_mul, Set.mem_range, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨a, rfl, _, ⟨s, rfl⟩, rfl⟩
  · rintro ⟨b, rfl, y, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩

/- English proof (translation)
Establish `h1 : MvPolynomial.map (IsLocalRing.residue V) f = 0 ↔ Ideal.span (Set.range fun s => f.coeff s) ≤ IsLocalRing.maximalIdeal V`. Rewrite using `[Ideal.span_le, Set.range_subset_iff, MvPolynomial.ext_iff]`. Use `forall_congr' fun s => ?_` and prove the remaining obligations. Rewrite using `[coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff]`. Both sides reduce to the same expression.

Rewrite using `[ne_eq, h1]`. Prove the components needed by the constructor for the conclusion. Introduce `h h'`. Rewrite `h'` using `[h, top_le_iff]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal V).ne_top h'`.

Introduce `h`. Assume the negation of the conclusion as `h'`. Conclude with `h (IsLocalRing.le_maximalIdeal h')`.
-/
theorem span_coeff_eq_top_iff [IsLocalRing V] (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => f.coeff s) = ⊤ ↔
      MvPolynomial.map (IsLocalRing.residue V) f ≠ 0 := by
  have h1 : MvPolynomial.map (IsLocalRing.residue V) f = 0 ↔
      Ideal.span (Set.range fun s => f.coeff s) ≤ IsLocalRing.maximalIdeal V := by
    rw [Ideal.span_le, Set.range_subset_iff, MvPolynomial.ext_iff]
    refine forall_congr' fun s => ?_
    rw [coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff]
    rfl
  rw [ne_eq, h1]
  constructor
  · intro h h'
    rw [h, top_le_iff] at h'
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top h'
  · intro h
    by_contra h'
    exact h (IsLocalRing.le_maximalIdeal h')

/- English proof (translation)
Rewrite using `[Ideal.eq_top_iff_one]`. Conclude with `Ideal.subset_span ⟨0, by simp⟩`.
-/
theorem span_coeff_one :
    Ideal.span (Set.range fun s => (1 : MvPolynomial σ V).coeff s) = ⊤ := by
  classical
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span ⟨0, by simp⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `(IsPrincipalIdealRing.principal (Ideal.span (Set.range fun s => f.coeff s))).principal`. Establish `ha' : Ideal.span (Set.range fun s => f.coeff s) = Ideal.span {a}` using `ha`. Establish `hd : C a ∣ f`. Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `s`.

Rewrite using `[← Ideal.mem_span_singleton, ← ha']`. Conclude with `Ideal.subset_span ⟨s, rfl⟩`. Take `⟨g, rfl⟩` from `hd`. Distinguish the cases in `h0 : a = 0`. Conclude with `⟨0, 1, by simp [h0], span_coeff_one⟩`.

Use `⟨a, g, rfl, ?_⟩` and prove the remaining obligations. Rewrite `ha'` using `[span_coeff_C_mul]`. Establish `hne : Ideal.span {a} ≠ (0 : Ideal V)`. Rewrite using `[Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]`. Conclude with `h0`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[ha', Ideal.mul_top]`.
-/
theorem exists_primitive_part [IsDomain V] [IsDiscreteValuationRing V] (f : MvPolynomial σ V) :
    ∃ (a : V) (g : MvPolynomial σ V), f = C a * g ∧
      Ideal.span (Set.range fun s => g.coeff s) = ⊤ := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal
    (Ideal.span (Set.range fun s => f.coeff s))).principal
  have ha' : Ideal.span (Set.range fun s => f.coeff s) = Ideal.span {a} := ha
  have hd : C a ∣ f := by
    rw [C_dvd_iff_dvd_coeff]
    intro s
    rw [← Ideal.mem_span_singleton, ← ha']
    exact Ideal.subset_span ⟨s, rfl⟩
  obtain ⟨g, rfl⟩ := hd
  by_cases h0 : a = 0
  · exact ⟨0, 1, by simp [h0], span_coeff_one⟩
  · refine ⟨a, g, rfl, ?_⟩
    rw [span_coeff_C_mul] at ha'
    have hne : Ideal.span {a} ≠ (0 : Ideal V) := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact h0
    apply mul_left_cancel₀ hne
    rw [ha', Ideal.mul_top]

/- English proof (translation)
Take `⟨a, f', rfl, hf⟩` from `exists_primitive_part f`. Take `⟨b, g', rfl, hg⟩` from `exists_primitive_part g`. Establish `hfg : Ideal.span (Set.range fun s => (f' * g').coeff s) = ⊤`. Rewrite `hf`, `hg`, the goal using `[span_coeff_eq_top_iff]`. Rewrite using `[map_mul]`.

Conclude with `mul_ne_zero hf hg`. Establish `e : C a * f' * (C b * g') = C (a * b) * (f' * g')`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, span_coeff_C_mul, span_coeff_C_mul, span_coeff_C_mul, hf, hg, hfg, Ideal.mul_top, Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_mul_span_singleton]`.
-/
theorem span_coeff_mul [IsDomain V] [IsDiscreteValuationRing V] (f g : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (f * g).coeff s) =
      Ideal.span (Set.range fun s => f.coeff s) * Ideal.span (Set.range fun s => g.coeff s) := by
  obtain ⟨a, f', rfl, hf⟩ := exists_primitive_part f
  obtain ⟨b, g', rfl, hg⟩ := exists_primitive_part g
  have hfg : Ideal.span (Set.range fun s => (f' * g').coeff s) = ⊤ := by
    rw [span_coeff_eq_top_iff] at hf hg ⊢
    rw [map_mul]
    exact mul_ne_zero hf hg
  have e : C a * f' * (C b * g') = C (a * b) * (f' * g') := by
    rw [map_mul]; ring
  rw [e, span_coeff_C_mul, span_coeff_C_mul, span_coeff_C_mul, hf, hg, hfg, Ideal.mul_top,
    Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_mul_span_singleton]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.prod_empty, span_coeff_one, Ideal.one_eq_top]`. Consider the case `insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, span_coeff_mul, ih]`.
-/
theorem span_coeff_prod [IsDomain V] [IsDiscreteValuationRing V] {ι : Type} (t : Finset ι)
    (f : ι → MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (∏ j ∈ t, f j).coeff s) =
      ∏ j ∈ t, Ideal.span (Set.range fun s => (f j).coeff s) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, span_coeff_one, Ideal.one_eq_top]
  | insert j t hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, span_coeff_mul, ih]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le, Set.range_subset_iff]`. Introduce `s`. Simplify using `only [coeff_sum, coeff_C_mul, SetLike.mem_coe]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)`.

Apply `Ideal.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Use `⟨Finsupp.single i 1, ?_⟩` and prove the remaining obligations. Simplify using `only [coeff_sum, coeff_C_mul, coeff_X']`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Conclude with `hj (Finsupp.single_left_injective one_ne_zero h)`.

Simplify using the standard rewrite rules.
-/
theorem span_coeff_linear {m : ℕ} (c : Fin m → V) :
    Ideal.span (Set.range fun s => (∑ i, C (c i) * X i : MvPolynomial (Fin m) V).coeff s) =
      Ideal.span (Set.range c) := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro s
    simp only [coeff_sum, coeff_C_mul, SetLike.mem_coe]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨Finsupp.single i 1, ?_⟩
    simp only [coeff_sum, coeff_C_mul, coeff_X']
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      exact hj (Finsupp.single_left_injective one_ne_zero h)
    · simp

/- English proof (translation)
Rewrite using `[span_coeff_prod]`. Conclude with `Finset.prod_congr rfl fun j _ => span_coeff_linear (c j)`.
-/
theorem span_coeff_prod_linear (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (d m : ℕ) (c : Fin d → Fin m → V) :
    Ideal.span (Set.range fun s =>
        (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by
  rw [span_coeff_prod]
  exact Finset.prod_congr rfl fun j _ => span_coeff_linear (c j)

end GaussContentLinearForms
end GlobalTheory
