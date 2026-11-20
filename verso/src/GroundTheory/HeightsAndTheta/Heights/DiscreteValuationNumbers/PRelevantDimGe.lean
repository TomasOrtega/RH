import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `R _ K _ _ ι Q hQ`. Set `e : K ≃ Fin (Fintype.card K)` to `Fintype.equivFin K`. Set `B : ℕ → Set K` to `fun j => {k | (e k : ℕ) < j}`. Set `J : ℕ → Ideal (MRing ι R)` to `fun j => Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}`. Establish `hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q)` using `fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog`.

Establish `hle : ∀ j, Q ≤ J j` using `fun j => le_sup_left`. Establish `hmono : ∀ j, J j ≤ J (j + 1)` using `fun j => sup_le_sup_left (Ideal.span_mono (by`. Introduce and unpack `p ⟨v, hv, rfl⟩`. Conclude with `⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _`. Establish `hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1)`.

Introduce `j hj`. Use `lt_of_le_of_ne (hmono j) ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hQ.relevant (e.symm ⟨j, hj⟩)`. Introduce `heq`. Establish `hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1)` using `Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)`.

Rewrite `hmem` using `[← heq]`. Conclude with `hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)`. Set `f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R` to `MRing ι R) (Q : Set (MRing ι R)) := fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩`. Establish `hf : StrictMono f`. Use `Fin.strictMono_iff_lt_succ.2 fun j => ?_` and prove the remaining obligations.

Use `show J j < J (j + 1)`. Conclude with `hstrict j j.isLt`. Rewrite using `[ringKrullDim_quotient]`. Conclude with `Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)`.
-/
theorem RelevantDimGe.proof (h1 : BlockAdjoinPrime.Statement.{u}) : RelevantDimGe.Statement.{u} := by
  intro R _ K _ _ ι Q hQ
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let B : ℕ → Set K := fun j => {k | (e k : ℕ) < j}
  let J : ℕ → Ideal (MRing ι R) := fun j =>
    Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}
  have hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q) :=
    fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog
  have hle : ∀ j, Q ≤ J j := fun j => le_sup_left
  have hmono : ∀ j, J j ≤ J (j + 1) := fun j =>
    sup_le_sup_left (Ideal.span_mono (by
      rintro p ⟨v, hv, rfl⟩
      exact ⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _
  have hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) ?_
    obtain ⟨i, hi⟩ := hQ.relevant (e.symm ⟨j, hj⟩)
    intro heq
    have hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1) :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)
    rw [← heq] at hmem
    exact hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R := MRing ι R) (Q : Set (MRing ι R)) :=
    fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩
  have hf : StrictMono f := by
    refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
    show J j < J (j + 1)
    exact hstrict j j.isLt
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)

end GroundTheory.Heights₂.Heights.NumbersDVR
