import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompDich

/- English proof (translation)
Use `Ideal.subset_span ⟨he.one_sub, ?_⟩` and prove the remaining obligations. Establish `h0 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, he.eq, sub_self]`. Establish `h1 : e * (1 - e) ∈ P` using `by rw [h0]; exact P.zero_mem`. Conclude with `(hP.mem_or_mem h1).resolve_left heP`.
-/
theorem one_sub_mem_compI {S : Type} [CommRing S] {P : Ideal S} (hP : P.IsPrime) {e : S}
    (he : IsIdempotentElem e) (heP : e ∉ P) : 1 - e ∈ compI P := by
  refine Ideal.subset_span ⟨he.one_sub, ?_⟩
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h1 : e * (1 - e) ∈ P := by rw [h0]; exact P.zero_mem
  exact (hP.mem_or_mem h1).resolve_left heP

/- English proof (translation)
Introduce `S _ ϖ P hP`. Use `⟨fun hV => ?_, fun hϖ => ?_⟩` and prove the remaining obligations. Introduce and unpack `f g ⟨N, hN⟩`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective f`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective g`.

Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 hN`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `h1 : ϖ ^ N - (a * f + b * g) ∈ compI P`. Rewrite using `[← Ideal.Quotient.eq]`.

Simplify `hab.symm` using `only [map_add, map_mul, map_pow]`. Take `⟨e, he, heP, hez⟩` from `(GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1`. Establish `hc` using `one_sub_mem_compI hP he heP`. Establish `hee : e * e = e` using `he`. Establish `hff : Ideal.Quotient.mk (compI P) (e * f + (1 - e)) = Ideal.Quotient.mk (compI P) f`.

Rewrite using `[Ideal.Quotient.eq]`. Establish `h2 : e * f + (1 - e) - f = (1 - f) * (1 - e)` using `by ring`. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_left _ _ hc`. Establish `hmem : ϖ ^ N ∈ Ideal.span {e * f + (1 - e), g}`.

Use `Ideal.mem_span_pair.2 ⟨a * e + (1 - e) * ϖ ^ N, b * e, ?_⟩` and prove the remaining obligations. Take the linear combination `(a * f - a - ϖ ^ N * f + ϖ ^ N) * hee - hez`. Take `⟨e1, he1, h2, h3⟩` from `hV (e * f + (1 - e)) g ⟨N, hmem⟩`. Rewrite `h2`, `h3` using `[Ideal.mem_span_singleton]`. Distinguish the cases in `h : e1 ∈ P`.

Use `right`. Establish `h0 : Ideal.Quotient.mk (compI P) e1 = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨he1, h⟩)`. Take `⟨c, hc'⟩` from `h3`. Use `⟨Ideal.Quotient.mk (compI P) c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hff, ← map_mul, ← hc', map_mul, map_sub, h0, map_one, sub_zero, one_mul]`.

Use `left`. Establish `h0 : Ideal.Quotient.mk (compI P) (1 - e1) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (one_sub_mem_compI hP he1 h)`. Establish `h1' : Ideal.Quotient.mk (compI P) e1 = 1`. Rewrite `h0` using `[map_sub, map_one]`. Conclude with `(sub_eq_zero.1 h0).symm`.

Take `⟨c, hc'⟩` from `h2`. Use `⟨Ideal.Quotient.mk (compI P) c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hff, ← map_mul, ← hc', map_mul, h1', one_mul]`. Use `mem_nonZeroDivisors_iff_right.2 fun x hx => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Establish `h1 : x * ϖ ∈ compI P` using `Ideal.Quotient.eq_zero_iff_mem.1 (by rwa [map_mul])`. Take `⟨e, he, heP, hez⟩` from `(GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1`. Establish `h2 : e * x = 0` using `(mul_right_mem_nonZeroDivisors_eq_zero_iff hϖ).1 (by rw [mul_assoc]; exact hez)`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 ((GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP x).2 ⟨e, he, heP, h2⟩)`.
-/
theorem dich_comp : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime →
    (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧
    (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  intro S _ ϖ P hP
  refine ⟨fun hV => ?_, fun hϖ => ?_⟩
  · rintro f g ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : ϖ ^ N - (a * f + b * g) ∈ compI P := by
      rw [← Ideal.Quotient.eq]
      simpa only [map_add, map_mul, map_pow] using hab.symm
    obtain ⟨e, he, heP, hez⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1
    have hc := one_sub_mem_compI hP he heP
    have hee : e * e = e := he
    have hff : Ideal.Quotient.mk (compI P) (e * f + (1 - e)) = Ideal.Quotient.mk (compI P) f := by
      rw [Ideal.Quotient.eq]
      have h2 : e * f + (1 - e) - f = (1 - f) * (1 - e) := by ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ hc
    have hmem : ϖ ^ N ∈ Ideal.span {e * f + (1 - e), g} := by
      refine Ideal.mem_span_pair.2 ⟨a * e + (1 - e) * ϖ ^ N, b * e, ?_⟩
      linear_combination (a * f - a - ϖ ^ N * f + ϖ ^ N) * hee - hez
    obtain ⟨e1, he1, h2, h3⟩ := hV (e * f + (1 - e)) g ⟨N, hmem⟩
    rw [Ideal.mem_span_singleton] at h2 h3
    by_cases h : e1 ∈ P
    · right
      have h0 : Ideal.Quotient.mk (compI P) e1 = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨he1, h⟩)
      obtain ⟨c, hc'⟩ := h3
      refine ⟨Ideal.Quotient.mk (compI P) c, ?_⟩
      rw [← hff, ← map_mul, ← hc', map_mul, map_sub, h0, map_one, sub_zero, one_mul]
    · left
      have h0 : Ideal.Quotient.mk (compI P) (1 - e1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (one_sub_mem_compI hP he1 h)
      have h1' : Ideal.Quotient.mk (compI P) e1 = 1 := by
        rw [map_sub, map_one] at h0
        exact (sub_eq_zero.1 h0).symm
      obtain ⟨c, hc'⟩ := h2
      refine ⟨Ideal.Quotient.mk (compI P) c, ?_⟩
      rw [← hff, ← map_mul, ← hc', map_mul, h1', one_mul]
  · refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : x * ϖ ∈ compI P := Ideal.Quotient.eq_zero_iff_mem.1 (by rwa [map_mul])
    obtain ⟨e, he, heP, hez⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1
    have h2 : e * x = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff hϖ).1 (by rw [mul_assoc]; exact hez)
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP x).2 ⟨e, he, heP, h2⟩)

end GlobalTheory.CompanionTheory.CompDich
