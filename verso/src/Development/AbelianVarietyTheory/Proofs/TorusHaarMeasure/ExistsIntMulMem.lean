import Mathlib

namespace GlobalTheory.IntegralMultiples

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ ({c} : Finset E)`. Conclude with `⟨y, hy0, ⟨y • c, hy c (Finset.mem_singleton_self c)⟩, (zsmul_eq_mul c y).symm⟩`.
-/
theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ y : NumberField.RingOfIntegers E, (d : E) * c = (y : E) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  exact ⟨y, hy0, ⟨y • c, hy c (Finset.mem_singleton_self c)⟩, (zsmul_eq_mul c y).symm⟩

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin r → E))`. Rewrite using `[hΛ]`. Conclude with `Submodule.mem_top`. Take `⟨n, f, g, hfg⟩` from `Submodule.mem_span_set'.mp hv`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image f)`.

Use `⟨y, hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfg, Finset.smul_sum]`. Use `Submodule.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Establish `hi` using `hy (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))`. Set `o : NumberField.RingOfIntegers E` to `⟨y • f i, hi⟩`.

Establish `e : y • f i • (g i : Fin r → E) = o • (g i : Fin r → E)`. Rewrite using `[← smul_assoc, ← algebraMap_smul E o]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Λ.smul_mem o (g i).2`.
-/
theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by
  classical
  have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by
    rw [hΛ]
    exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy0, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have hi := hy (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
  let o : NumberField.RingOfIntegers E := ⟨y • f i, hi⟩
  have e : y • f i • (g i : Fin r → E) = o • (g i : Fin r → E) := by
    rw [← smul_assoc, ← algebraMap_smul E o]
    rfl
  rw [e]
  exact Λ.smul_mem o (g i).2

/- English proof (translation)
Introduce `E _ _ r Λ hΛ v`. Conclude with `exists_int_smul_mem Λ hΛ v`.
-/
theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
      ∀ (v : Fin r → E), ∃ (k : ℤ), k ≠ (0 : ℤ) ∧ k • v ∈ Λ := by
  intro E _ _ r Λ hΛ v
  exact exists_int_smul_mem Λ hΛ v

end GlobalTheory.IntegralMultiples
