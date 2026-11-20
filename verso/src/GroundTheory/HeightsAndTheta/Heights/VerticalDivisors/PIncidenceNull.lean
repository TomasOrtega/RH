import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

/- English proof (translation)
Introduce `F _ n k I f hf`. Establish `hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈ MvPolynomial.vanishingIdeal F (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k))`. Introduce `j z hz`. Establish `hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0`. Introduce `g hg`.

Establish `hmem : rename Sum.inl g ∈ incIdeal I k` using `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)`. Establish `h` using `hz _ hmem`. Rewrite `h` using `[aeval_rename]`. Then use the resulting hypothesis. Establish `hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0`. Introduce `i`.

Establish `hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k` using `Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)`. Establish `h` using `hz _ hmem`. Simplify using `using h`. Rewrite using `[map_mul, aeval_rename, aeval_X]`. Distinguish the cases in `hx : z ∘ Sum.inl = 0`.

Establish `h0 : z (Sum.inl j) = 0` using `congrFun hx j`. Rewrite using `[h0, mul_zero]`. Establish `hu : z ∘ Sum.inr ∈ incidence I k` using `⟨z ∘ Sum.inl, hx, hI, hlin⟩`. Rewrite using `[(hf.2 f).2 dvd_rfl _ hu, zero_mul]`. Establish `hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k`.

Introduce `j`. Establish `h` using `hvan j`. Rewrite `h` using `[MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]`. Conclude with `h`. Use `choose m hm using hrad`.

Conclude with `⟨Finset.univ.sup m, fun j => Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩`.
-/
theorem IncidenceNull.proof : IncidenceNull.Statement := by
  intro F _ n k I f hf
  have hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈
      MvPolynomial.vanishingIdeal F
        (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k)) := by
    intro j z hz
    have hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0 := by
      intro g hg
      have hmem : rename Sum.inl g ∈ incIdeal I k :=
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
      have h := hz _ hmem
      rwa [aeval_rename] at h
    have hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0 := by
      intro i
      have hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) :
          MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
      have h := hz _ hmem
      simpa using h
    rw [map_mul, aeval_rename, aeval_X]
    by_cases hx : z ∘ Sum.inl = 0
    · have h0 : z (Sum.inl j) = 0 := congrFun hx j
      rw [h0, mul_zero]
    · have hu : z ∘ Sum.inr ∈ incidence I k := ⟨z ∘ Sum.inl, hx, hI, hlin⟩
      rw [(hf.2 f).2 dvd_rfl _ hu, zero_mul]
  have hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k := by
    intro j
    have h := hvan j
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose m hm using hrad
  exact ⟨Finset.univ.sup m, fun j =>
    Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩

end GroundTheory.Heights₂.Heights.Vertical
