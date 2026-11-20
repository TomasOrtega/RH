import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf

open GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `A A' A'' _ _ _ _ _ _ _ h h1 h2`. Take `⟨e1, s1, i1⟩` from `h1`. Take `⟨e2, s2, i2⟩` from `h2`. Establish `hsc : ∀ x : A, algebraMap A A'' x = algebraMap A' A'' (algebraMap A A' x)` using `fun x => IsScalarTower.algebraMap_apply A A' A'' x`. Use `⟨Algebra.Etale.comp A A' A'', ?_, ?_⟩` and prove the remaining obligations.

Introduce `a''`. Take `⟨a', ha'⟩` from `s2 a''`. Take `⟨a, ha⟩` from `s1 a'`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite `ha`, `ha'`, the goal using `[Ideal.mem_span_singleton]`.

Take `⟨c, hc⟩` from `ha`. Establish `key : a'' - algebraMap A A'' a = (a'' - algebraMap A' A'' a') + algebraMap A' A'' (algebraMap A A' h) * algebraMap A' A'' c`. Rewrite using `[← map_mul, ← hc, map_sub, hsc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, hsc]`.

Conclude with `dvd_add ha' (dvd_mul_right _ _)`. Introduce `a ha`. Rewrite `ha` using `[hsc, hsc]`. Conclude with `i1 a (i2 _ ha)`.
-/
theorem isExcisionNbhd_trans :
    ∀ (A A' A'' : Type) [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A' A''] [Algebra A A'']
      [IsScalarTower A A' A''] (h : A), IsExcisionNbhd A A' h → IsExcisionNbhd A' A'' (algebraMap A A' h) →
        IsExcisionNbhd A A'' h := by
  intro A A' A'' _ _ _ _ _ _ _ h h1 h2
  obtain ⟨e1, s1, i1⟩ := h1
  obtain ⟨e2, s2, i2⟩ := h2
  have hsc : ∀ x : A, algebraMap A A'' x = algebraMap A' A'' (algebraMap A A' x) :=
    fun x => IsScalarTower.algebraMap_apply A A' A'' x
  refine ⟨Algebra.Etale.comp A A' A'', ?_, ?_⟩
  · intro a''
    obtain ⟨a', ha'⟩ := s2 a''
    obtain ⟨a, ha⟩ := s1 a'
    refine ⟨a, ?_⟩
    rw [Ideal.mem_span_singleton] at ha ha' ⊢
    obtain ⟨c, hc⟩ := ha
    have key : a'' - algebraMap A A'' a = (a'' - algebraMap A' A'' a') +
        algebraMap A' A'' (algebraMap A A' h) * algebraMap A' A'' c := by
      rw [← map_mul, ← hc, map_sub, hsc]
      ring
    rw [key, hsc]
    exact dvd_add ha' (dvd_mul_right _ _)
  · intro a ha
    rw [hsc, hsc] at ha
    exact i1 a (i2 _ ha)

end GlobalTheory.EtC
