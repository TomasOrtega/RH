import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ n r f hf hrn`. Use `set m : Ideal (MvPolynomial (Fin n) k) := RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) with hm`. Establish `hsurj : Function.Surjective (MvPolynomial.eval (0 : Fin n → k))` using `fun c => ⟨MvPolynomial.C c, by simp⟩`. Use `haveI hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj`. Use `set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((Finset.univ.image f : Finset _) : Set (MvPolynomial (Fin n) k)) with hI`.

Establish `hIm : I ≤ m`. Rewrite using `[hI, Ideal.span_le]`. Introduce `g hg`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hg`. Take `⟨i, rfl⟩` from `hg`.

Simplify using `[hm, RingHom.mem_ker, MvPolynomial.eval_zero, hf i]`. Establish `hItop : I ≠ ⊤` using `fun h => hmax.ne_top (top_le_iff.mp (h ▸ hIm))`. Take `⟨P, hP⟩` from `Ideal.nonempty_minimalPrimes hItop`. Use `haveI hPp : P.IsPrime := hP.1.1`. Establish `hht : P.height ≤ r`.

Establish `h1` using `Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP`. Use `h1.trans ?_` and prove the remaining obligations. Conclude with `Finset.card_image_le.trans (by simp)` after adjusting the coercions. Establish `hmh : m.height = n` using `(ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n m).2`. Establish `hPne : P ≠ m`.

Introduce `h`. Rewrite `hht` using `[h, hmh]`. Conclude with `absurd (by exact_mod_cast hht : n ≤ r) (not_le.mpr hrn)`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hPne` to reduce the goal to its premises. Establish `hsub : MvPolynomial.zeroLocus k P ⊆ {0}`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Take `⟨i, hi⟩` from `hcon x hx0`.

Apply `hi` to reduce the goal to its premises. Use `hx (f i) (hP.1.2 (Ideal.subset_span (by simp)))` as an intermediate fact. Simplify `this` using `[MvPolynomial.coe_aeval_eq_eval]`. Establish `hle : m ≤ P`. Introduce `p hp`.

Establish `h2 : p ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P)`. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.mp (hsub hx)]`. Conclude with `hp`. Rewrite `h2` using `[MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hPp.radical]`. Then use the resulting hypothesis.

Conclude with `(hmax.eq_of_le hPp.ne_top hle).symm`.
-/
theorem exists_ne_zero_common_zero_of_constantCoeff_eq_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, MvPolynomial.constantCoeff (f i) = 0) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  classical
  set m : Ideal (MvPolynomial (Fin n) k) := RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) with hm
  have hsurj : Function.Surjective (MvPolynomial.eval (0 : Fin n → k)) :=
    fun c => ⟨MvPolynomial.C c, by simp⟩
  haveI hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((Finset.univ.image f : Finset _) : Set (MvPolynomial (Fin n) k)) with hI
  have hIm : I ≤ m := by
    rw [hI, Ideal.span_le]
    intro g hg
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hg
    obtain ⟨i, rfl⟩ := hg
    simp [hm, RingHom.mem_ker, MvPolynomial.eval_zero, hf i]
  have hItop : I ≠ ⊤ := fun h => hmax.ne_top (top_le_iff.mp (h ▸ hIm))
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hItop
  haveI hPp : P.IsPrime := hP.1.1
  have hht : P.height ≤ r := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
    refine h1.trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hmh : m.height = n := (ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n m).2
  have hPne : P ≠ m := by
    intro h
    rw [h, hmh] at hht
    exact absurd (by exact_mod_cast hht : n ≤ r) (not_le.mpr hrn)
  by_contra hcon
  push_neg at hcon
  apply hPne
  have hsub : MvPolynomial.zeroLocus k P ⊆ {0} := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (hP.1.2 (Ideal.subset_span (by simp)))
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  have hle : m ≤ P := by
    intro p hp
    have h2 : p ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k P) := by
      intro x hx
      rw [Set.mem_singleton_iff.mp (hsub hx)]
      exact hp
    rwa [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hPp.radical] at h2
  exact (hmax.eq_of_le hPp.ne_top hle).symm

end GlobalTheory
