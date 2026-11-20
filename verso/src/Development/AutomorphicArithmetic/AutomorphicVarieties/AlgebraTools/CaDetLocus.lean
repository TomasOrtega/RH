import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetMin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetAdj

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `P _ _ ι _ _ z m hc Z hZ hrel hm hdim Q hQ hdet`. Establish `hdZ : detIdeal z m ≤ Z` using `det_mem_of_rel P ι z m Z hZ hrel hm`. Distinguish the cases in `hne : Nonempty ι`. Use `swap`. It suffices to derive a contradiction.

Establish `: IsEmpty ι` using `not_nonempty_iff.1 hne`. Apply `hQ.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`. Use `le_trans ?_ hdet` and prove the remaining obligations. Simplify using `[detIdeal, Matrix.det_isEmpty]`.

Take `⟨K, hK, hKdet, hKmin⟩` from `exists_least_prime_detIdeal P ι z m hc hne`. Use `haveI := hK`. Use `haveI := hZ`. Use `le_trans ?_ (hKmin Q hQ hdet)` and prove the remaining obligations. Establish `hKZ : K ≤ Z` using `hKmin Z hZ hdZ`.

Assume the negation of the conclusion as `hnot`. Take `⟨x, hxZ, hxK⟩` from `Set.not_subset.1 hnot`. Establish `hrK : relIdeal z m ≤ K` using `le_trans (le_sup_left : relIdeal z m ≤ relIdeal z m ⊔ Ideal.span {z.det}) hKdet`. Establish `h1 : ringKrullDim (P ⧸ Z) + 1 ≤ ringKrullDim (P ⧸ K)`. Use `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hKZ) (Ideal.Quotient.factor_surjective hKZ) (r := Ideal.Quotient.mk K x) ?_ ?_` and prove the remaining obligations.

Conclude with `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Simplify `hxZ` using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h2 : ringKrullDim (P ⧸ K) ≤ ringKrullDim (P ⧸ relIdeal z m)` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hrK) (Ideal.Quotient.factor_surjective hrK)`. Establish `h3` using `dim_relIdeal_le P ι z m hc`. Establish `hfin : ringKrullDim (P ⧸ Z) < ⊤` using `lt_of_le_of_lt (ringKrullDim_quotient_le Z) ringKrullDim_lt_top`.

Establish `hbot : ringKrullDim (P ⧸ Z) ≠ ⊥` using `ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial`. Establish `h12` using `h1.trans h2`. Establish `key : ringKrullDim (P ⧸ Z) + 1 + (Fintype.card ι : ℕ) ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ)`. Use `le_trans ?_ (h3.trans hdim)` and prove the remaining obligations. Use `gcongr`.

Generalize the expression as in `ringKrullDim (P ⧸ Z) = d at key hfin hbot`. Generalize the expression as in `Fintype.card ι = c at key`. Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => exact hbot rfl`. Consider the case `coe d`.

Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top => simp at hfin`. Consider the case `coe d`. Normalize the coercions in `at key`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.AlgebraTools.le_of_detIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ Z : Ideal P, Z.IsPrime → relIdeal z m ≤ Z → (∃ j, m j ∉ Z) →
      ringKrullDim P ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) →
      ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → Z ≤ Q := by
  intro P _ _ ι _ _ z m hc Z hZ hrel hm hdim Q hQ hdet
  have hdZ : detIdeal z m ≤ Z := det_mem_of_rel P ι z m Z hZ hrel hm
  by_cases hne : Nonempty ι
  swap
  · exfalso
    have : IsEmpty ι := not_nonempty_iff.1 hne
    apply hQ.ne_top
    rw [eq_top_iff]
    refine le_trans ?_ hdet
    simp [detIdeal, Matrix.det_isEmpty]
  obtain ⟨K, hK, hKdet, hKmin⟩ := exists_least_prime_detIdeal P ι z m hc hne
  haveI := hK
  haveI := hZ
  refine le_trans ?_ (hKmin Q hQ hdet)
  have hKZ : K ≤ Z := hKmin Z hZ hdZ
  by_contra hnot
  obtain ⟨x, hxZ, hxK⟩ := Set.not_subset.1 hnot
  have hrK : relIdeal z m ≤ K :=
    le_trans (le_sup_left : relIdeal z m ≤ relIdeal z m ⊔ Ideal.span {z.det}) hKdet
  have h1 : ringKrullDim (P ⧸ Z) + 1 ≤ ringKrullDim (P ⧸ K) := by
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hKZ)
      (Ideal.Quotient.factor_surjective hKZ) (r := Ideal.Quotient.mk K x) ?_ ?_
    · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    · simpa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxZ
  have h2 : ringKrullDim (P ⧸ K) ≤ ringKrullDim (P ⧸ relIdeal z m) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hrK) (Ideal.Quotient.factor_surjective hrK)
  have h3 := dim_relIdeal_le P ι z m hc
  have hfin : ringKrullDim (P ⧸ Z) < ⊤ := lt_of_le_of_lt (ringKrullDim_quotient_le Z) ringKrullDim_lt_top
  have hbot : ringKrullDim (P ⧸ Z) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  have h12 := h1.trans h2
  have key : ringKrullDim (P ⧸ Z) + 1 + (Fintype.card ι : ℕ) ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) := by
    refine le_trans ?_ (h3.trans hdim)
    gcongr
  generalize ringKrullDim (P ⧸ Z) = d at key hfin hbot
  generalize Fintype.card ι = c at key
  induction d using WithBot.recBotCoe with
  | bot => exact hbot rfl
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => simp at hfin
    | coe d =>
      norm_cast at key
      omega
