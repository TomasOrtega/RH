import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.UnitComb

/- English proof (translation)
Unfold `minorIJ`. Use `split_ifs with e`. Conclude with `RingHom.map_det V.subtype _`. Both sides reduce to the same expression.
-/
theorem coe_minorIJ {L : Type} [Field L] (V : ValuationSubring L) {N : ℕ}
    (h : Matrix (Fin N) (Fin N) V) (I J : Finset (Fin N)) :
    ((minorIJ h I J : V) : L) = minorIJ (h.map V.subtype) I J := by
  unfold minorIJ
  split_ifs with e
  · exact RingHom.map_det V.subtype _
  · rfl

/- English proof (translation)
Unfold `minorIJ`. Rewrite using `[dif_pos rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]`.
-/
theorem minorIJ_one_diag {R : Type} [CommRing R] {N : ℕ} (J : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) J J = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R` using `Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 this h`.
-/
theorem exists_isUnit_of_sum {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ a ∈ s, f a)) : ∃ a ∈ s, IsUnit (f a) := by
  by_contra hc
  push_neg at hc
  have : ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)
  exact (IsLocalRing.mem_maximalIdeal _).1 this h

/- English proof (translation)
Establish `hi` using `i.2`. Distinguish the cases in `c : (i : ℕ) + 1 ≤ j`. Use `Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]`. Use linear arithmetic over natural numbers and integers.

Use `Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]`. Use linear arithmetic over natural numbers and integers.
-/
theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
    omega

/- English proof (translation)
Introduce `L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth`. Set `Hv : Matrix (Fin N) (Fin N) V` to `Matrix.of fun a b => ⟨H a b, hH a b⟩`. Establish `hHv : Hv.map V.subtype = H` using `by ext a b; rfl`. Set `uv : κ → Finset (Fin N) → V` to `fun m I => ⟨u m I, hu m I⟩`. Set `uv' : Finset (Fin N) → κ → V` to `fun I m => ⟨u' I m, hu' I m⟩`.

Establish `hdetc : ((Hv.det : V) : L) = H.det`. Use `RingHom.map_det V.subtype Hv` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, hHv]`. Conclude with `this`. Establish `hunit : IsUnit Hv.det`.

Use `IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((Hv.det : V) : L) * (H.det)⁻¹ = 1`. Rewrite using `[hdetc, mul_inv_cancel₀ hdet]`. Establish `main` using `GlobalTheory.T.block_diagonal_minor_vanishing V N j i hj`.

Establish `hJ` using `stepCols_ne_empty (j := j) i hj`. Establish `hBv : IsBlockDiag j Hv` using `fun a b hab => Subtype.ext (hB a b hab)`. Establish `hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0` using `fun I hI => (main.2.1 Hv I hBv hI).resolve_right hJ`. Establish `hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i))`. Rewrite using `[← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]`.

Conclude with `isUnit_one`. Take `⟨I₀, -, hI₀⟩` from `exists_isUnit_of_sum _ _ hsum1`. Establish `hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i))` using `isUnit_of_mul_isUnit_right hI₀`. Establish `hI₀s : IsStepRows N j i I₀`. Assume the negation of the conclusion as `hc`.

Rewrite `hI₀'` using `[hstep I₀ hc]`. Conclude with `not_isUnit_zero hI₀'`. Establish `horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0`. Introduce `I' hI'`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `horth I₀ I' hI₀s hI'` as an intermediate fact. Use `split_ifs at this ⊢ with e`. Simplify `this` using `[uv, uv']`. Simplify `this` using `[uv, uv']`. Set `w : κ → V` to `fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)`.

Establish `hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i)`. Establish `e1 : ∑ m, uv' I₀ m * w m = ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i)`. Simplify using `only [w, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc]`.

Rewrite using `[e1, Finset.sum_eq_single I₀]`. Rewrite using `[horthV I₀ hI₀s, if_pos rfl, one_mul]`. Introduce `b _ hb`. Distinguish the cases in `hs : IsStepRows N j i b`. Rewrite using `[horthV b hs, if_neg (Ne.symm hb), zero_mul]`.

Rewrite using `[hstep b hs, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `hI₀'` using `[← hw]`. Take `⟨m, -, hm⟩` from `exists_isUnit_of_sum _ _ hI₀'`.

Establish `hwm : IsUnit (w m)` using `isUnit_of_mul_isUnit_right hm`. Establish `hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i)`. Simplify using `only [w, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, coe_minorIJ, hHv]`. Both sides reduce to the same expression. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hcoe]`. Introduce `h0`. Conclude with `hwm.ne_zero (Subtype.ext h0)`. Take `⟨c, hc⟩` from `hwm.exists_right_inv`. Establish `hc' : ((w m : V) : L) * (c : L) = 1` using `congrArg Subtype.val hc`.

Rewrite using `[← hcoe, inv_eq_of_mul_eq_one_right hc']`. Conclude with `c.2`.
-/
theorem unit_comb : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  intro L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hHv : Hv.map V.subtype = H := by ext a b; rfl
  let uv : κ → Finset (Fin N) → V := fun m I => ⟨u m I, hu m I⟩
  let uv' : Finset (Fin N) → κ → V := fun I m => ⟨u' I m, hu' I m⟩
  have hdetc : ((Hv.det : V) : L) = H.det := by
    have := RingHom.map_det V.subtype Hv
    rw [RingHom.mapMatrix_apply, hHv] at this
    exact this
  have hunit : IsUnit Hv.det := by
    refine IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_
    apply Subtype.ext
    change ((Hv.det : V) : L) * (H.det)⁻¹ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  have main := GlobalTheory.T.block_diagonal_minor_vanishing V N j i hj
  have hJ := stepCols_ne_empty (j := j) i hj
  have hBv : IsBlockDiag j Hv := fun a b hab => Subtype.ext (hB a b hab)
  have hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0 := fun I hI =>
    (main.2.1 Hv I hBv hI).resolve_right hJ
  have hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i)) := by
    rw [← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]
    exact isUnit_one
  obtain ⟨I₀, -, hI₀⟩ := exists_isUnit_of_sum _ _ hsum1
  have hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i)) := isUnit_of_mul_isUnit_right hI₀
  have hI₀s : IsStepRows N j i I₀ := by
    by_contra hc
    rw [hstep I₀ hc] at hI₀'
    exact not_isUnit_zero hI₀'
  have horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0 := by
    intro I' hI'
    apply Subtype.ext
    have := horth I₀ I' hI₀s hI'
    split_ifs at this ⊢ with e
    · simpa [uv, uv'] using this
    · simpa [uv, uv'] using this
  let w : κ → V := fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)
  have hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i) := by
    have e1 : ∑ m, uv' I₀ m * w m =
        ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i) := by
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [e1, Finset.sum_eq_single I₀]
    · rw [horthV I₀ hI₀s, if_pos rfl, one_mul]
    · intro b _ hb
      by_cases hs : IsStepRows N j i b
      · rw [horthV b hs, if_neg (Ne.symm hb), zero_mul]
      · rw [hstep b hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← hw] at hI₀'
  obtain ⟨m, -, hm⟩ := exists_isUnit_of_sum _ _ hI₀'
  have hwm : IsUnit (w m) := isUnit_of_mul_isUnit_right hm
  have hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i) := by
    simp only [w, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, coe_minorIJ, hHv]
    rfl
  refine ⟨m, ?_, ?_⟩
  · rw [← hcoe]
    intro h0
    exact hwm.ne_zero (Subtype.ext h0)
  · obtain ⟨c, hc⟩ := hwm.exists_right_inv
    have hc' : ((w m : V) : L) * (c : L) = 1 := congrArg Subtype.val hc
    rw [← hcoe, inv_eq_of_mul_eq_one_right hc']
    exact c.2

end GlobalTheory.CompanionTheory.Ar.PB.UnitComb
