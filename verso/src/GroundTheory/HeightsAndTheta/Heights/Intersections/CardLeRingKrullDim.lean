import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreExtra
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace RegularityRelativeClosedPoint

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq K]

def killBlocks (S : Finset K) : MRing ι →ₐ[ℤ] MRing ι :=
  aeval fun p => if p.1 ∈ S then 0 else X p

/- English proof (translation)
Establish `e : (fun p : (Σ k, ι k) => if p.1 ∈ S then (0 : MRing ι) else X p) = fun p => (if p.1 ∈ S then (0 : MRing ι) else 1) * X p`. Use function extensionality and compare the values at `p`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h` using `regularityLocalResidue_holds.aeval_blockScale_int hg (fun k => if k ∈ S then (0 : MRing ι) else 1) X`. Rewrite `h` using `[aeval_X_left_apply]`.

Rewrite using `[killBlocks, e]`. Conclude with `h`.
-/
theorem killBlocks_form (S : Finset K) {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    killBlocks S g = (∏ k, (if k ∈ S then (0 : MRing ι) else 1) ^ a k) * g := by
  have e : (fun p : (Σ k, ι k) => if p.1 ∈ S then (0 : MRing ι) else X p) =
      fun p => (if p.1 ∈ S then (0 : MRing ι) else 1) * X p := by
    funext p
    split_ifs <;> simp
  have h := regularityLocalResidue_holds.aeval_blockScale_int hg (fun k => if k ∈ S then (0 : MRing ι) else 1) X
  rw [aeval_X_left_apply] at h
  rw [killBlocks, e]
  exact h

/- English proof (translation)
Take `⟨T, hT, rfl⟩` from `hW`. Rewrite using `[Ideal.span_le]`. Introduce `g hg`. Take `⟨a, ha⟩` from `hT g hg`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span hg)`.
-/
theorem le_comap_killBlocks (S : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W) :
    W ≤ W.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hW
  rw [Ideal.span_le]
  intro g hg
  obtain ⟨a, ha⟩ := hT g hg
  rw [SetLike.mem_coe, Ideal.mem_comap, killBlocks_form S ha]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span hg)

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use `MvPolynomial.algHom_ext fun p => ?_` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, killBlocks, aeval_X]`. Distinguish the cases in `h : p.1 ∈ S`. Simplify using `[h, hST h]`. Simplify using `[h]`.
-/
theorem killBlocks_comp {S T : Finset K} (hST : S ⊆ T) :
    (killBlocks T).comp (killBlocks S) = (killBlocks T : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  simp only [AlgHom.comp_apply, killBlocks, aeval_X]
  by_cases h : p.1 ∈ S
  · simp [h, hST h]
  · simp [h]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
The claim follows from `MvPolynomial.algHom_ext fun p => by simp [killBlocks]`.
-/
theorem killBlocks_empty : (killBlocks ∅ : MRing ι →ₐ[ℤ] MRing ι) = AlgHom.id ℤ (MRing ι) :=
  MvPolynomial.algHom_ext fun p => by simp [killBlocks]

/- English proof (translation)
Use `choose j hj using hWr`. Set `Q : Finset K → Ideal (MRing ι)` to `fun S => W.comap (killBlocks S)`. Establish `hQp : ∀ S, (Q S).IsPrime` using `fun S => Ideal.comap_isPrime _ _`. Establish `hstep : ∀ S k, k ∉ S → Q S < Q (insert k S)`. Introduce `S k hk`.

Use `SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Ideal.mem_comap.mp (le_comap_killBlocks (insert k S) hWh (Ideal.mem_comap.mp hg))`. Rewrite `h1` using `[← AlgHom.comp_apply, killBlocks_comp (Finset.subset_insert k S)]`. Conclude with `Ideal.mem_comap.mpr h1`. Rewrite using `[Ideal.mem_comap]`.

Simplify using `[killBlocks]`. Introduce `h`. Rewrite `h` using `[Ideal.mem_comap]`. Simplify using `only [killBlocks, aeval_X, if_neg hk] at h`. Conclude with `hj k h`.

Establish `chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤ ringKrullDim (MRing ι ⧸ Q ∅)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert k S hk ih`.

Establish `: (Q S).IsPrime` using `hQp S`. Establish `: (Q (insert k S)).IsPrime` using `hQp _`. Establish `h1` using `HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)`. Rewrite using `[Finset.card_insert_of_notMem hk]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hQ0 : Q ∅ = W`. Use extensionality with `g`. Simplify using `[Q, killBlocks_empty]`. Establish `: (Q Finset.univ).IsPrime` using `hQp _`. Establish `: IsDomain (MRing ι ⧸ Q Finset.univ)` using `Ideal.Quotient.isDomain _`.

Establish `h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Q Finset.univ)` using `ringKrullDim_nonneg_of_nontrivial`. Establish `hc` using `chain Finset.univ`. Rewrite `hc` using `[Finset.card_univ, hQ0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le_ringKrullDim (W : Ideal (MRing ι)) [W.IsPrime] (hWh : IsMultiHomogIdeal W)
    (hWr : IsRelevant W) : ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ W) := by
  choose j hj using hWr
  let Q : Finset K → Ideal (MRing ι) := fun S => W.comap (killBlocks S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => Ideal.comap_isPrime _ _
  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · have h1 := Ideal.mem_comap.mp (le_comap_killBlocks (insert k S) hWh (Ideal.mem_comap.mp hg))
      rw [← AlgHom.comp_apply, killBlocks_comp (Finset.subset_insert k S)] at h1
      exact Ideal.mem_comap.mpr h1
    · rw [Ideal.mem_comap]
      simp [killBlocks]
    · intro h
      rw [Ideal.mem_comap] at h
      simp only [killBlocks, aeval_X, if_neg hk] at h
      exact hj k h
  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have hQ0 : Q ∅ = W := by
    ext g
    simp [Q, killBlocks_empty]
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRing ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Q Finset.univ) := ringKrullDim_nonneg_of_nontrivial
  have hc := chain Finset.univ
  rw [Finset.card_univ, hQ0] at hc
  calc ((Fintype.card K : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 0 := (add_zero _).symm
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) := by gcongr
    _ ≤ _ := hc

end RegularityRelativeClosedPoint

/- English proof (translation)
Introduce `K _ ι _ P W hP hW hPW hne`. Use `⟨hW, ?_⟩` and prove the remaining obligations. Take `⟨-, ⟨hPp, -, -⟩, -, hPdim⟩` from `hP`. Take `⟨hWp, hWh, hWr⟩` from `hW`. Use `hPp` as an intermediate fact.

Use `hWp` as an intermediate fact. Establish `e` using `mvPolynomialInt_dimFormula P W hPW`. Rewrite `e` using `[hPdim]`. Establish `hh : (W.map (Ideal.Quotient.mk P)).height ≠ 0` using `fun h0 => hne (le_antisymm (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0) hPW)`. Establish `hlow` using `RegularityRelativeClosedPoint.card_le_ringKrullDim W hWh hWr`.

Generalize the expression as in `ringKrullDim (MRing ι ⧸ W) = m at e hlow ⊢`. Generalize the expression as in `(W.map (Ideal.Quotient.mk P)).height = h at e hh`. Proceed by induction on `m using WithBot.recBotCoe with`. Consider the case `bot => exact absurd hlow (by simp)`. Consider the case `coe m`.

Establish `e' : m + h = ((1 + Fintype.card K : ℕ) : ℕ∞)` using `by exact_mod_cast e`. Establish `hlow' : ((Fintype.card K : ℕ) : ℕ∞) ≤ m` using `by exact_mod_cast hlow`. Proceed by induction on `m using ENat.recTopCoe with`. Consider the case `top => simp at e'`. Conclude with `absurd e'.symm (ENat.natCast_ne_top _)`.

Consider the case `coe m`. Proceed by induction on `h using ENat.recTopCoe with`. Consider the case `top => simp at e'`. Conclude with `absurd e'.symm (ENat.natCast_ne_top _)`. Consider the case `coe h`.

Establish `h1 : m + h = 1 + Fintype.card K` using `by exact_mod_cast e'`. Establish `h2 : Fintype.card K ≤ m` using `by exact_mod_cast hlow'`. Establish `h3 : h ≠ 0` using `by exact_mod_cast hh`. Establish `h4 : m = Fintype.card K` using `by omega`. Rewrite using `[h4]`.

Both sides reduce to the same expression.
-/
theorem RegularityRelativeClosedPoint.proof : RegularityRelativeClosedPoint.Statement := by
  intro K _ ι _ P W hP hW hPW hne
  classical
  refine ⟨hW, ?_⟩
  obtain ⟨-, ⟨hPp, -, -⟩, -, hPdim⟩ := hP
  obtain ⟨hWp, hWh, hWr⟩ := hW
  have := hPp
  have := hWp
  have e := mvPolynomialInt_dimFormula P W hPW
  rw [hPdim] at e
  have hh : (W.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
    hne (le_antisymm (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0) hPW)
  have hlow := RegularityRelativeClosedPoint.card_le_ringKrullDim W hWh hWr
  generalize ringKrullDim (MRing ι ⧸ W) = m at e hlow ⊢
  generalize (W.map (Ideal.Quotient.mk P)).height = h at e hh
  induction m using WithBot.recBotCoe with
  | bot => exact absurd hlow (by simp)
  | coe m =>
    have e' : m + h = ((1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast e
    have hlow' : ((Fintype.card K : ℕ) : ℕ∞) ≤ m := by exact_mod_cast hlow
    induction m using ENat.recTopCoe with
    | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
    | coe m =>
      induction h using ENat.recTopCoe with
      | top => simp at e'; exact absurd e'.symm (ENat.natCast_ne_top _)
      | coe h =>
        have h1 : m + h = 1 + Fintype.card K := by exact_mod_cast e'
        have h2 : Fintype.card K ≤ m := by exact_mod_cast hlow'
        have h3 : h ≠ 0 := by exact_mod_cast hh
        have h4 : m = Fintype.card K := by omega
        rw [h4]
        rfl

end

end GroundTheory.Heights₂.Heights.Inter
