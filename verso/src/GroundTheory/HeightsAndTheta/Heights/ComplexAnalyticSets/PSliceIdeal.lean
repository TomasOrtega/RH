import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j`.
-/
theorem SliceIdeal.isHomogeneous_linForm {n : ℕ} (u : Fin n → ℂ) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

/- English proof (translation)
Use `⟨f.totalDegree, ∑ i ∈ Finset.range (f.totalDegree + 1), linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f, ?_, ?_⟩` and prove the remaining obligations. Use `IsHomogeneous.sum _ _ _ fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ f.totalDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `h` using `((SliceIdeal.isHomogeneous_linForm ℓ).pow (f.totalDegree - i)).mul (homogeneousComponent_isHomogeneous i f)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use linear arithmetic over natural numbers and integers. Establish `hsum : (∑ i ∈ Finset.range (f.totalDegree + 1), linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f) - f = ∑ i ∈ Finset.range (f.totalDegree + 1), (linForm ℓ ^ (f.totalDegree - i) - 1) * homogeneousComponent i f` using `by conv_lhs => arg 2; rw [← sum_homogeneousComponent f]`. Rewrite using `[← Finset.sum_sub_distrib]`. Simplify using `only [sub_one_mul]`. Rewrite using `[hsum]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr ?_)` and prove the remaining obligations. Simplify using `using sub_dvd_pow_sub_pow (linForm ℓ) 1 (f.totalDegree - i)`.
-/
theorem SliceIdeal.exists_homogeneous_sub_mem {n : ℕ} (ℓ : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    ∃ d, ∃ G : MvPolynomial (Fin n) ℂ, G.IsHomogeneous d ∧ G - f ∈ Ideal.span {linForm ℓ - 1} := by
  classical
  refine ⟨f.totalDegree, ∑ i ∈ Finset.range (f.totalDegree + 1),
      linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := ((SliceIdeal.isHomogeneous_linForm ℓ).pow (f.totalDegree - i)).mul
      (homogeneousComponent_isHomogeneous i f)
    convert h using 1
    omega
  · have hsum : (∑ i ∈ Finset.range (f.totalDegree + 1),
          linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f) - f =
        ∑ i ∈ Finset.range (f.totalDegree + 1),
          (linForm ℓ ^ (f.totalDegree - i) - 1) * homogeneousComponent i f := by
      conv_lhs => arg 2; rw [← sum_homogeneousComponent f]
      rw [← Finset.sum_sub_distrib]
      simp only [sub_one_mul]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr ?_)
    simpa using sub_dvd_pow_sub_pow (linForm ℓ) 1 (f.totalDegree - i)

/- English proof (translation)
Introduce `n k J F ℓ hJ hF hℓ`. Establish `hA : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J (k + 1)` using `(IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := k) hJ).mp ⟨F, hF⟩`. Establish `hP` using `hJ.isPrime`. Establish `hdeh : ∀ (G : MvPolynomial (Fin n) ℂ) (d : ℕ), G.IsHomogeneous d → G ∈ J ⊔ Ideal.span {linForm ℓ - 1} → G ∈ J` using `fun G d hG hm => ChartDehomog.proof ℂ n J ℓ G d hP hJ.isHomog hℓ hG hm`. Establish `hspan : Ideal.span {linForm ℓ - 1} ≤ J ⊔ Ideal.span {linForm ℓ - 1}` using `le_sup_right`.

Establish `hprime : (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime`. Use `Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {a b} hab => ?_⟩` and prove the remaining obligations. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one J).mpr (hdeh 1 0 (isHomogeneous_one _ _) (htop ▸ Submodule.mem_top)))`. Take `⟨da, A, hA', hAa⟩` from `SliceIdeal.exists_homogeneous_sub_mem ℓ a`. Take `⟨db, B, hB', hBb⟩` from `SliceIdeal.exists_homogeneous_sub_mem ℓ b`.

Establish `hAB : A * B ∈ J ⊔ Ideal.span {linForm ℓ - 1}`. Establish `h : A * B = (A - a) * B + a * (B - b) + a * b` using `by ring`. Rewrite using `[h]`. Conclude with `Ideal.add_mem _ (Ideal.add_mem _ (hspan (Ideal.mul_mem_right _ _ hAa)) (hspan (Ideal.mul_mem_left _ _ hBb))) hab`. Break down `hP.mem_or_mem (hdeh _ _ (hA'.mul hB') hAB) with h | h` into its components or cases.

Use `left`. Establish `e : a = A - (A - a)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hAa)`. Use `right`.

Establish `e : b = B - (B - b)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hBb)`. Use `⟨hprime, le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA hJ.isHomog hℓ), fun u hu hmem => hu (hdeh _ 1 (SliceIdeal.isHomogeneous_linForm u) hmem)⟩` and prove the remaining obligations. Establish `hx : Ideal.Quotient.mk J (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ J)⁰`.

Use `mem_nonZeroDivisors_of_ne_zero fun h => hP.ne_top ?_` and prove the remaining obligations. Establish `h0` using `hJ.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h) 0`. Rewrite `h0` using `[homogeneousComponent_zero]`. Establish `hc : coeff 0 (linForm ℓ - 1) = -1`. Simplify using `[linForm, coeff_sum, coeff_C_mul, coeff_X]`.

Rewrite `h0` using `[hc, map_neg, map_one, Ideal.neg_mem_iff]`. Conclude with `(Ideal.eq_top_iff_one J).mpr h0`. Establish `h1` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx`. Rewrite `h1` using `[hA.dim]`. Establish `e` using `DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {linForm ℓ - 1})`.

Rewrite `e` using `[Ideal.map_span, Set.image_singleton]`. Rewrite `h1` using `[ringKrullDim_eq_of_ringEquiv e]`. Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at h1 ⊢`. Proceed by induction on `D using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`.

Consider the case `coe b`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction. Establish `ht : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞)`.

Rewrite using `[← WithBot.coe_one, ← WithBot.coe_add, top_add]`. Rewrite `h1` using `[ht]`. Establish `h2 : (⊤ : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast h1`. Conclude with `ENat.natCast_ne_top _ (top_le_iff.mp h2)`. Consider the case `coe m`.

Establish `h2 : m + 1 ≤ k + 1` using `by exact_mod_cast h1`. Conclude with `(by omega : m ≤ k)` after adjusting the coercions.
-/
theorem SliceIdeal.proof : SliceIdeal.Statement := by
  intro n k J F ℓ hJ hF hℓ
  have hA : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety J (k + 1) :=
    (IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := k) hJ).mp ⟨F, hF⟩
  have hP := hJ.isPrime
  have hdeh : ∀ (G : MvPolynomial (Fin n) ℂ) (d : ℕ), G.IsHomogeneous d →
      G ∈ J ⊔ Ideal.span {linForm ℓ - 1} → G ∈ J :=
    fun G d hG hm => ChartDehomog.proof ℂ n J ℓ G d hP hJ.isHomog hℓ hG hm
  have hspan : Ideal.span {linForm ℓ - 1} ≤ J ⊔ Ideal.span {linForm ℓ - 1} := le_sup_right

  have hprime : (J ⊔ Ideal.span {linForm ℓ - 1}).IsPrime := by
    refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr
        (hdeh 1 0 (isHomogeneous_one _ _) (htop ▸ Submodule.mem_top)))
    obtain ⟨da, A, hA', hAa⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ a
    obtain ⟨db, B, hB', hBb⟩ := SliceIdeal.exists_homogeneous_sub_mem ℓ b
    have hAB : A * B ∈ J ⊔ Ideal.span {linForm ℓ - 1} := by
      have h : A * B = (A - a) * B + a * (B - b) + a * b := by ring
      rw [h]
      exact Ideal.add_mem _ (Ideal.add_mem _ (hspan (Ideal.mul_mem_right _ _ hAa))
        (hspan (Ideal.mul_mem_left _ _ hBb))) hab
    rcases hP.mem_or_mem (hdeh _ _ (hA'.mul hB') hAB) with h | h
    · left
      have e : a = A - (A - a) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hAa)
    · right
      have e : b = B - (B - b) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left h) (hspan hBb)
  refine ⟨hprime, le_antisymm ?_ (IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA hJ.isHomog hℓ), fun u hu hmem =>
    hu (hdeh _ 1 (SliceIdeal.isHomogeneous_linForm u) hmem)⟩

  have hx : Ideal.Quotient.mk J (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ J)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h => hP.ne_top ?_
    have h0 := hJ.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h) 0
    rw [homogeneousComponent_zero] at h0
    have hc : coeff 0 (linForm ℓ - 1) = -1 := by
      simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
    rw [hc, map_neg, map_one, Ideal.neg_mem_iff] at h0
    exact (Ideal.eq_top_iff_one J).mpr h0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  rw [hA.dim] at h1
  have e := DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {linForm ℓ - 1})
  rw [Ideal.map_span, Set.image_singleton] at e
  rw [ringKrullDim_eq_of_ringEquiv e] at h1
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) = D at h1 ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have ht : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [ht] at h1
      have h2 : (⊤ : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      exact ENat.natCast_ne_top _ (top_le_iff.mp h2)
    | coe m =>
      have h2 : m + 1 ≤ k + 1 := by exact_mod_cast h1
      exact_mod_cast (by omega : m ≤ k)

end

end GroundTheory.Heights₂.Heights
