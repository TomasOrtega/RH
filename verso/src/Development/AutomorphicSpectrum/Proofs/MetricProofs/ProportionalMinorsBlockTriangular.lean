import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinorDeterminants
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PlVanish

/- English proof (translation)
Introduce `e`. Establish `hi` using `i.2`. Distinguish the cases in `h : (i : ℕ) + 1 ≤ j`. Establish `: (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[e] at this`. Establish `: (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[e] at this`.
-/
theorem cols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

/- English proof (translation)
Unfold `minorIJ`. Use `split_ifs with e`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `h (Finset.eq_of_subset_of_card_le hc e.ge)`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by`. Establish `h2 : a ∈ Set.range (I.orderEmbOfFin e)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `ha`.

Conclude with `h2`. Use `Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_` and prove the remaining obligations. Rewrite using `[Matrix.submatrix_apply, hr]`. Conclude with `Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)`. Both sides reduce to the same expression.
-/
theorem minor_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  unfold minorIJ
  split_ifs with e
  · obtain ⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by
      by_contra hc
      push_neg at hc
      exact h (Finset.eq_of_subset_of_card_le hc e.ge)
    obtain ⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by
      have h2 : a ∈ Set.range (I.orderEmbOfFin e) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      exact h2
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, hr]
    exact Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)
  · rfl

/- English proof (translation)
Unfold `minorIJ`. Rewrite using `[dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]`.
-/
theorem minor_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MinorDeterminants.main C S f hf h0`.
-/
theorem det_submatrix_eq_zero {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (f : Fin S.card → Fin N) (hf : Function.Injective f)
    (h0 : minorIJ C (Finset.univ.image f) S = 0) :
    (C.submatrix f (S.orderEmbOfFin rfl)).det = 0 :=
  _root_.UpperTheory.Reformulated.B.MinorDeterminants.main C S f hf h0

/- English proof (translation)
Take `⟨cb, off, -, -⟩` from `GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj`. Establish `hne` using `cols_ne_empty hj i`. Establish `hall : ∀ J, α * minorIJ h₁ J (stepCols N j i) = β * minorIJ h₂ J (stepCols N j i)` using `fun J => by`. Distinguish the cases in `hJ : IsStepRows N j i J`. Conclude with `hp J hJ`.

Rewrite using `[(off h₁ J hb₁ hJ).resolve_right hne, (off h₂ J hb₂ hJ).resolve_right hne, mul_zero, mul_zero]`. Establish `e1 : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) = minorIJ (h₁⁻¹ * h₁) I (stepCols N j i)`. Rewrite using `[Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]`. Rewrite using `[e1, cb, cb, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations.

Take the linear combination `(-minorIJ h₁⁻¹ I J) * hall J`.
-/
theorem minor_quot {N j : ℕ} (hj : j ≤ N) (i : Fin N) {h₁ h₂ : Matrix (Fin N) (Fin N) ℂ} {α β : ℂ}
    (hb₁ : IsBlockDiag j h₁) (hb₂ : IsBlockDiag j h₂) (hd : h₁.det ≠ 0)
    (hp : ∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i))
    (I : Finset (Fin N)) :
    β * minorIJ (h₁⁻¹ * h₂) I (stepCols N j i) =
      α * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj
  have hne := cols_ne_empty hj i
  have hall : ∀ J, α * minorIJ h₁ J (stepCols N j i) = β * minorIJ h₂ J (stepCols N j i) := fun J => by
    by_cases hJ : IsStepRows N j i J
    · exact hp J hJ
    · rw [(off h₁ J hb₁ hJ).resolve_right hne, (off h₂ J hb₂ hJ).resolve_right hne, mul_zero, mul_zero]
  have e1 : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) =
      minorIJ (h₁⁻¹ * h₁) I (stepCols N j i) := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]
  rw [e1, cb, cb, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  linear_combination (-minorIJ h₁⁻¹ I J) * hall J

/- English proof (translation)
Introduce `N j i h₁ h₂ α β hj hb₁ hb₂ hd hα hβ hp r c hc hr`. Establish `hq` using `minor_quot hj i hb₁ hb₂ hd hp`. Use `set S := stepCols N j i with hS`. Use `set C := h₁⁻¹ * h₂ with hC`. Set `e` to `S.orderEmbOfFin rfl`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, e t = c := by`. Establish `h2 : c ∈ Set.range e`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `hc`. Conclude with `h2`.

Set `D : Matrix (Fin S.card) (Fin S.card) ℂ` to `C.submatrix e e`. Establish `hD : D.det ≠ 0`. Establish `h1` using `hq S`. Rewrite `h1` using `[minor_one_same, mul_one]`. Establish `h2 : minorIJ C S S = D.det` using `dif_pos rfl`.

Rewrite using `[← h2]`. Introduce `h0`. Rewrite `h1` using `[h0, mul_zero]`. Conclude with `hα h1.symm`. Set `v : Fin S.card → ℂ` to `fun s => C r (e s)`.

Establish `hrow : ∀ u, (D.updateRow u v).det = 0` using `fun u => by`. Set `f : Fin S.card → Fin N` to `Function.update e u r`. Establish `hmem : ∀ s, e s ∈ S` using `fun s => Finset.orderEmbOfFin_mem _ _ _`. Establish `hf : Function.Injective f` using `fun a b hab => by`. Distinguish the cases in `ha : a = u`.

Distinguish the cases in `hb : b = u`. Rewrite using `[ha, hb]`. Substitute `ha` using the available equality. Simplify using `only [f, Function.update_self, Function.update_of_ne hb] at hab`. Conclude with `absurd (hab ▸ hmem b) hr`.

Distinguish the cases in `hb : b = u`. Substitute `hb` using the available equality. Simplify using `only [f, Function.update_self, Function.update_of_ne ha] at hab`. Conclude with `absurd (hab ▸ hmem a) hr`. Simplify using `only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab`.

Conclude with `e.injective hab`. Establish `hI : Finset.univ.image f ≠ S` using `fun h => hr (by`. Rewrite using `[← h]`. Conclude with `Finset.mem_image.2 ⟨u, Finset.mem_univ _, Function.update_self _ _ _⟩)`. Establish `h0 : minorIJ C (Finset.univ.image f) S = 0`.

Establish `h1` using `hq (Finset.univ.image f)`. Rewrite `h1` using `[minor_one_ne hI, mul_zero]`. Conclude with `(mul_eq_zero.1 h1).resolve_left hβ`. Establish `h2` using `det_submatrix_eq_zero C S f hf h0`. Establish `e2 : D.updateRow u v = C.submatrix f e`.

Use extensionality with `a b`. Distinguish the cases in `ha : a = u`. Substitute `ha` using the available equality. Simplify using `[f, D, v, Matrix.updateRow_self]`. Simplify using `[f, D, Matrix.updateRow_ne ha, Function.update_of_ne ha]`.

Rewrite using `[e2]`. Conclude with `h2`. Establish `hcr : Dᵀ.cramer v = 0`. Use function extensionality and compare the values at `u`. Rewrite using `[Matrix.cramer_transpose_apply]`.

Conclude with `hrow u`. Establish `h3` using `Matrix.mulVec_cramer Dᵀ v`. Rewrite `h3` using `[hcr, Matrix.mulVec_zero, Matrix.det_transpose]`. Establish `h4 : D.det * v t = 0`. Use `congrFun h3 t` as an intermediate fact.

Simplify using `using this.symm`. Establish `h5 : v t = 0` using `(mul_eq_zero.1 h4).resolve_left hD`. Rewrite using `[← ht]`. Conclude with `h5`.
-/
theorem quot_vanish : ∀ (N j : ℕ) (i : Fin N) (h₁ h₂ : Matrix (Fin N) (Fin N) ℂ) (α β : ℂ), j ≤ N →
    IsBlockDiag j h₁ → IsBlockDiag j h₂ → h₁.det ≠ 0 → α ≠ 0 → β ≠ 0 →
    (∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i)) →
    ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → (h₁⁻¹ * h₂) r c = 0 := by
  intro N j i h₁ h₂ α β hj hb₁ hb₂ hd hα hβ hp r c hc hr
  have hq := minor_quot hj i hb₁ hb₂ hd hp
  set S := stepCols N j i with hS
  set C := h₁⁻¹ * h₂ with hC
  let e := S.orderEmbOfFin rfl
  obtain ⟨t, ht⟩ : ∃ t, e t = c := by
    have h2 : c ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hc
    exact h2
  let D : Matrix (Fin S.card) (Fin S.card) ℂ := C.submatrix e e
  have hD : D.det ≠ 0 := by
    have h1 := hq S
    rw [minor_one_same, mul_one] at h1
    have h2 : minorIJ C S S = D.det := dif_pos rfl
    rw [← h2]
    intro h0
    rw [h0, mul_zero] at h1
    exact hα h1.symm
  let v : Fin S.card → ℂ := fun s => C r (e s)
  have hrow : ∀ u, (D.updateRow u v).det = 0 := fun u => by
    let f : Fin S.card → Fin N := Function.update e u r
    have hmem : ∀ s, e s ∈ S := fun s => Finset.orderEmbOfFin_mem _ _ _
    have hf : Function.Injective f := fun a b hab => by
      by_cases ha : a = u
      · by_cases hb : b = u
        · rw [ha, hb]
        · subst ha
          simp only [f, Function.update_self, Function.update_of_ne hb] at hab
          exact absurd (hab ▸ hmem b) hr
      · by_cases hb : b = u
        · subst hb
          simp only [f, Function.update_self, Function.update_of_ne ha] at hab
          exact absurd (hab ▸ hmem a) hr
        · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
          exact e.injective hab
    have hI : Finset.univ.image f ≠ S := fun h => hr (by
      rw [← h]
      exact Finset.mem_image.2 ⟨u, Finset.mem_univ _, Function.update_self _ _ _⟩)
    have h0 : minorIJ C (Finset.univ.image f) S = 0 := by
      have h1 := hq (Finset.univ.image f)
      rw [minor_one_ne hI, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hβ
    have h2 := det_submatrix_eq_zero C S f hf h0
    have e2 : D.updateRow u v = C.submatrix f e := by
      ext a b
      by_cases ha : a = u
      · subst ha
        simp [f, D, v, Matrix.updateRow_self]
      · simp [f, D, Matrix.updateRow_ne ha, Function.update_of_ne ha]
    rw [e2]
    exact h2
  have hcr : Dᵀ.cramer v = 0 := by
    funext u
    rw [Matrix.cramer_transpose_apply]
    exact hrow u
  have h3 := Matrix.mulVec_cramer Dᵀ v
  rw [hcr, Matrix.mulVec_zero, Matrix.det_transpose] at h3
  have h4 : D.det * v t = 0 := by
    have := congrFun h3 t
    simpa using this.symm
  have h5 : v t = 0 := (mul_eq_zero.1 h4).resolve_left hD
  rw [← ht]
  exact h5

end GlobalTheory.CompanionTheory.Ar.PB.PlVanish
