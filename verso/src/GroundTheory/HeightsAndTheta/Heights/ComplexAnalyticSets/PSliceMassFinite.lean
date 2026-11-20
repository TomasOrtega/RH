import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MeasurableOfContinuousOnNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets
open scoped nonZeroDivisors

noncomputable section

/- English proof (translation)
Take `⟨W, hW, hℓW, hWI, -⟩` from `ChartHomogenise.proof ℂ n I ℓ hI hℓ`. Establish `hP` using `hW.isPrime`. Establish `hx : Ideal.Quotient.mk W (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ W)⁰`. Use `mem_nonZeroDivisors_of_ne_zero fun h0 => hP.ne_top ?_` and prove the remaining obligations. Establish `h00` using `hW.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) 0`.

Rewrite `h00` using `[homogeneousComponent_zero]`. Establish `hc : coeff 0 (linForm ℓ - 1) = -1`. Simplify using `[linForm, coeff_sum, coeff_C_mul, coeff_X]`. Rewrite `h00` using `[hc, map_neg, map_one, Ideal.neg_mem_iff]`. Conclude with `(Ideal.eq_top_iff_one W).mpr h00`.

Establish `h1` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx`. Establish `eq` using `DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {linForm ℓ - 1})`. Rewrite `eq` using `[Ideal.map_span, Set.image_singleton]`. Rewrite `h1` using `[ringKrullDim_eq_of_ringEquiv eq, hWI, hdim]`. Establish `h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : WithBot ℕ∞)`.

Use `ringKrullDim_quotient_le W` as an intermediate fact. Rewrite `this` using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]`. Then use the resulting hypothesis. Establish `hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞)`. Generalize the expression as in `hD : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h1 h2`. Proceed by induction on `D using WithBot.recBotCoe with`.

Consider the case `bot => simp at h1`. Consider the case `coe b`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction.

Establish `h3 : (⊤ : ℕ∞) ≤ (n : ℕ∞)` using `by exact_mod_cast h2`. Conclude with `ENat.natCast_ne_top _ (top_le_iff.mp h3)`. Consider the case `coe m`. Establish `hm1 : e + 1 + 1 ≤ m` using `by exact_mod_cast h1`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`.

Establish `hA' : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety W (k + 1)` using `⟨hP, by rw [hD]; rfl⟩`. Establish `h3` using `IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA' hW.isHomog hℓW`. Rewrite `h3` using `[hWI, hdim]`. Establish `hk : k ≤ e + 1` using `by exact_mod_cast h3`. Establish `hke : k + 1 = e + 1 + 1` using `by omega`.

Rewrite using `[hke]`. Both sides reduce to the same expression. Take `⟨F, hFW⟩` from `(IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := e + 1) hW).mpr ⟨hP, hdimW⟩`. Conclude with `⟨W, F, hW, hFW, hℓW, hWI⟩`.
-/
theorem SliceMassFinite.exists_projClosure {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (W : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ),
      IsProjPrime W ∧ IsChowForm W (e + 2) F ∧ linForm ℓ ∉ W ∧ W ⊔ Ideal.span {linForm ℓ - 1} = I := by
  obtain ⟨W, hW, hℓW, hWI, -⟩ := ChartHomogenise.proof ℂ n I ℓ hI hℓ
  have hP := hW.isPrime

  have hx : Ideal.Quotient.mk W (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ W)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hP.ne_top ?_
    have h00 := hW.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) 0
    rw [homogeneousComponent_zero] at h00
    have hc : coeff 0 (linForm ℓ - 1) = -1 := by
      simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
    rw [hc, map_neg, map_one, Ideal.neg_mem_iff] at h00
    exact (Ideal.eq_top_iff_one W).mpr h00
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  have eq := DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {linForm ℓ - 1})
  rw [Ideal.map_span, Set.image_singleton] at eq
  rw [ringKrullDim_eq_of_ringEquiv eq, hWI, hdim] at h1

  have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : WithBot ℕ∞) := by
    have := ringKrullDim_quotient_le W
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at this

  have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    generalize hD : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h1 h2
    induction D using WithBot.recBotCoe with
    | bot => simp at h1
    | coe b =>
      induction b using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h2
        exact ENat.natCast_ne_top _ (top_le_iff.mp h3)
      | coe m =>
        have hm1 : e + 1 + 1 ≤ m := by exact_mod_cast h1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hA' : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety W (k + 1) := ⟨hP, by rw [hD]; rfl⟩
        have h3 := IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA' hW.isHomog hℓW
        rw [hWI, hdim] at h3
        have hk : k ≤ e + 1 := by exact_mod_cast h3
        have hke : k + 1 = e + 1 + 1 := by omega
        rw [hke]
        rfl
  obtain ⟨F, hFW⟩ := (IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := e + 1) hW).mpr ⟨hP, hdimW⟩
  exact ⟨W, F, hW, hFW, hℓW, hWI⟩

/- English proof (translation)
Introduce `n d h I ℓ A hI hℓ hdim hA`. Consider the cases of `d with`. Consider the case `zero`. Establish `hconst : chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) = fun _ => chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) 0`. Use function extensionality and compare the values at `fun y => congrArg _ (Subsingleton.elim y 0)`.

Rewrite using `[hconst]`. Establish `: IsFiniteMeasure (volume : Measure (Fin 0 → ℂ))`. Rewrite using `[MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]`. Use `infer_instance`. Conclude with `integrable_const _`.

Consider the case `succ e`. Take `⟨W, F, hW, hFW, hℓW, hWI⟩` from `SliceMassFinite.exists_projClosure I ℓ hI hℓ hdim`. Establish `hA2 : IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A`. Rewrite using `[hWI]`. Conclude with `hA`.

Establish `hmass` using `hF n e h W F ℓ A (fun _ => 1) (fun _ => 1) (fun _ _ => 0) hW hFW hℓW hA2 (fun _ _ _ => rfl) continuousOn_const (fun _ _ _ _ => rfl) (fun _ => contDiffOn_const)`. Rewrite `hmass` using `[hWI]`. Simplify `hmass` using `only [one_mul, add_zero]`.
-/
theorem SliceMassFinite.proof (hF : SliceFormMass.Statement) : SliceMassFinite.Statement := by
  intro n d h I ℓ A hI hℓ hdim hA
  cases d with
  | zero =>
    have hconst : chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) =
        fun _ => chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) 0 :=
      funext fun y => congrArg _ (Subsingleton.elim y 0)
    rw [hconst]
    have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := by
      rw [MeasureTheory.volume_pi, Measure.pi_of_empty (x := 0)]
      infer_instance
    exact integrable_const _
  | succ e =>
    obtain ⟨W, F, hW, hFW, hℓW, hWI⟩ := SliceMassFinite.exists_projClosure I ℓ hI hℓ hdim
    have hA2 : IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A := by
      rw [hWI]
      exact hA
    have hmass := hF n e h W F ℓ A (fun _ => 1) (fun _ => 1) (fun _ _ => 0) hW hFW hℓW hA2
      (fun _ _ _ => rfl) continuousOn_const (fun _ _ _ _ => rfl) (fun _ => contDiffOn_const)
    rw [hWI] at hmass
    simpa only [one_mul, add_zero] using hmass

end

end GroundTheory.Heights₂.Heights
