import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Introduce `O _ _ _ F _ _ _ n P P' f hP hP'C hfP hP'`. Set `A` to `MvPolynomial (Fin n) O`. Set `T` to `MvPolynomial (Fin n) F`. Set `M : Submonoid A` to `(nonZeroDivisors O).map (C : O →+* A)`. Establish `hφ : (algebraMap A T) = MvPolynomial.map (algebraMap O F)` using `rfl`.

Establish `: IsLocalization M T` using `MvPolynomial.isLocalization (nonZeroDivisors O) F`. Establish `hP'p : P'.IsPrime` using `hP'.1.1`. Establish `hPP' : P ≤ P'` using `le_sup_left.trans hP'.1.2`. Establish `hfP' : f ∈ P'` using `hP'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Establish `hdisj' : Disjoint (M : Set A) (P' : Set A)`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨o, ho, rfl⟩ hmem`. Establish `h1 : o ∈ P'.comap (C : O →+* A)` using `hmem`. Rewrite `h1` using `[hP'C, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero ho h1`.

Establish `hdisj : Disjoint (M : Set A) (P : Set A)` using `Set.disjoint_of_subset_right hPP' hdisj'`. Set `I : Ideal T` to `P.map (algebraMap A T)`. Set `I' : Ideal T` to `P'.map (algebraMap A T)`. Establish `hI : I.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint M T P hP hdisj`. Establish `hI' : I'.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint M T P' hP'p hdisj'`.

Establish `hII' : I ≤ I'` using `Ideal.map_mono hPP'`. Set `Q : Ideal (A ⧸ P)` to `P'.map (Ideal.Quotient.mk P)`. Establish `hQ : Q.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hQne : Q ≠ ⊥`. Introduce `h`.

Establish `h1 : Ideal.Quotient.mk P f ∈ Q` using `Ideal.mem_map_of_mem _ hfP'`. Rewrite `h1` using `[h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hfP h1`. Establish `hQ1 : Q.height = 1`. Use `le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hP') ?_` and prove the remaining obligations.

Use `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQne)` as an intermediate fact. Simplify using `using this`. Set `M' : Submonoid (A ⧸ P)` to `Algebra.algebraMapSubmonoid (A ⧸ P) M`. Establish `hQdisj : Disjoint (M' : Set (A ⧸ P)) (Q : Set (A ⧸ P))`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `_ ⟨a, ha, rfl⟩ hmem`. Establish `h1 : Ideal.Quotient.mk P a ∈ Q` using `hmem`. Rewrite `h1` using `[Ideal.mem_quotient_iff_mem hPP']`. Conclude with `Set.disjoint_left.1 hdisj' ha h1`. Establish `hh` using `IsLocalization.height_map_of_disjoint (S := T ⧸ I) M' Q hQdisj`.

Establish `hmap : Q.map (algebraMap (A ⧸ P) (T ⧸ I)) = I'.map (Ideal.Quotient.mk I)`. Simplify using `only [Q, I', Ideal.map_map]`. Both sides reduce to the same expression. Rewrite `hh` using `[hmap, hQ1]`. Establish `_ : (I'.map (Ideal.Quotient.mk I)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`.

Establish `key` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (I'.map (Ideal.Quotient.mk I))`. Rewrite `key` using `[hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hII')]`. Use `show ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I') + 1`. Rewrite using `[← key, add_comm]`. Both sides reduce to the same expression.
-/
theorem GenericFibreDrop.proof : GenericFibreDrop.Statement := by
  intro O _ _ _ F _ _ _ n P P' f hP hP'C hfP hP'
  let A := MvPolynomial (Fin n) O
  let T := MvPolynomial (Fin n) F
  let M : Submonoid A := (nonZeroDivisors O).map (C : O →+* A)
  have hφ : (algebraMap A T) = MvPolynomial.map (algebraMap O F) := rfl
  have : IsLocalization M T := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hP'p : P'.IsPrime := hP'.1.1
  have hPP' : P ≤ P' := le_sup_left.trans hP'.1.2
  have hfP' : f ∈ P' := hP'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hdisj' : Disjoint (M : Set A) (P' : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨o, ho, rfl⟩ hmem
    have h1 : o ∈ P'.comap (C : O →+* A) := hmem
    rw [hP'C, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero ho h1
  have hdisj : Disjoint (M : Set A) (P : Set A) :=
    Set.disjoint_of_subset_right hPP' hdisj'

  let I : Ideal T := P.map (algebraMap A T)
  let I' : Ideal T := P'.map (algebraMap A T)
  have hI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P hP hdisj
  have hI' : I'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P' hP'p hdisj'
  have hII' : I ≤ I' := Ideal.map_mono hPP'

  let Q : Ideal (A ⧸ P) := P'.map (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : Ideal.Quotient.mk P f ∈ Q := Ideal.mem_map_of_mem _ hfP'
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hfP h1
  have hQ1 : Q.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hP') ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQne)
    simpa using this

  let M' : Submonoid (A ⧸ P) := Algebra.algebraMapSubmonoid (A ⧸ P) M
  have hQdisj : Disjoint (M' : Set (A ⧸ P)) (Q : Set (A ⧸ P)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have h1 : Ideal.Quotient.mk P a ∈ Q := hmem
    rw [Ideal.mem_quotient_iff_mem hPP'] at h1
    exact Set.disjoint_left.1 hdisj' ha h1
  have hh := IsLocalization.height_map_of_disjoint (S := T ⧸ I) M' Q hQdisj
  have hmap : Q.map (algebraMap (A ⧸ P) (T ⧸ I)) = I'.map (Ideal.Quotient.mk I) := by
    simp only [Q, I', Ideal.map_map]
    rfl
  rw [hmap, hQ1] at hh
  have _ : (I'.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F
    (I'.map (Ideal.Quotient.mk I))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hII')] at key
  show ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I') + 1
  rw [← key, add_comm]
  rfl

end GroundTheory.Heights₂.Heights.Vertical
