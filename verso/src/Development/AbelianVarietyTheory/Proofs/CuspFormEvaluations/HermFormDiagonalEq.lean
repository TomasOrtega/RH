import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PeriodTorusConstantEqBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

/- English proof (translation)
Simplify using `only [hermForm, dotProduct, mulVec_diagonal]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.star_apply, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_diagonal_eq (d z w : Fin g → ℂ) :
    hermForm (Matrix.diagonal d) z w = ∑ j, d j * z j * conj (w j) := by
  simp only [hermForm, dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  ring

/- English proof (translation)
Use `⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha⟩ : ∃ a, (bas a : Fin r → E) = x` from `⟨bas.symm ⟨x, hx⟩, by simp⟩`. Take `⟨b, hb⟩ : ∃ b, (bas b : Fin r → E) = y` from `⟨bas.symm ⟨y, hy⟩, by simp⟩`. Use `⟨-omegaStd a b, ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, ← hb, hs a b]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hint : ∀ c, ∃ n : ℤ, GlobalTheory.SW.crd X bas x c = n`. Introduce `c`. Consider the cases of `c with`.

Consider the case `inl j`. Take `⟨k, hk⟩` from `h _ (bas (Pi.single (Sum.inr j) 1)).2`. Establish `e` using `GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x) (fun c => (((Pi.single (Sum.inr j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))`. Rewrite `e` using `[GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk]`. Simplify using `[Pi.single_apply] at e`.

Conclude with `⟨-k, by push_cast; linarith⟩`. Consider the case `inr j`. Take `⟨k, hk⟩` from `h _ (bas (Pi.single (Sum.inl j) 1)).2`. Establish `e` using `GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x) (fun c => (((Pi.single (Sum.inl j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))`. Rewrite `e` using `[GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk]`.

Simplify using `[Pi.single_apply] at e`. Conclude with `⟨k, by linarith⟩`. Use `choose n hn using hint`. Establish `hx : x = (bas n : Fin r → E)`. Rewrite using `[← GlobalTheory.SW.vecQ_crd X bas x, ← GlobalTheory.SW.vecQ_intCast]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Conclude with `hn c`. Rewrite using `[hx]`. Conclude with `(bas n).2`.
-/
theorem selfD_of_isSympl (hs : IsSympl X bas) : SelfD X X.Λ := by
  refine ⟨X.Λ_fg, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha⟩ : ∃ a, (bas a : Fin r → E) = x := ⟨bas.symm ⟨x, hx⟩, by simp⟩
    obtain ⟨b, hb⟩ : ∃ b, (bas b : Fin r → E) = y := ⟨bas.symm ⟨y, hy⟩, by simp⟩
    refine ⟨-omegaStd a b, ?_⟩
    rw [← ha, ← hb, hs a b]
    push_cast
    rfl
  · have hint : ∀ c, ∃ n : ℤ, GlobalTheory.SW.crd X bas x c = n := by
      intro c
      cases c with
      | inl j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inr j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inr j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨-k, by push_cast; linarith⟩
      | inr j =>
        obtain ⟨k, hk⟩ := h _ (bas (Pi.single (Sum.inl j) 1)).2
        have e := GlobalTheory.SW.EF_vecQ hs (GlobalTheory.SW.crd X bas x)
          (fun c => (((Pi.single (Sum.inl j) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) c : ℤ) : ℚ))
        rw [GlobalTheory.SW.vecQ_intCast, GlobalTheory.SW.vecQ_crd, hk] at e
        simp [Pi.single_apply] at e
        exact ⟨k, by linarith⟩
    choose n hn using hint
    have hx : x = (bas n : Fin r → E) := by
      rw [← GlobalTheory.SW.vecQ_crd X bas x, ← GlobalTheory.SW.vecQ_intCast]
      congr 1
      funext c
      exact hn c
    rw [hx]
    exact (bas n).2

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx hs x hxd ho`. Establish `hHm` using `GlobalTheory.ThFr.Hm_of_isOrtho idx hs ho`. Establish `h1 : ∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j)`. Introduce `z z'`. Rewrite using `[hx_eq_hermForm idx x z z', hHm, hermForm_diagonal_eq]`.

Establish `h2 : ∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u)`. Introduce `u`. Rewrite using `[hx_eq_hermForm idx x, hHm]`. Conclude with `(congrArg Complex.re (GlobalTheory.ThFr.hermForm_diagonal_c_self idx hxd ho u)).trans (Complex.ofReal_re _)`. Establish `h0 : ∀ z, 0 ≤ (hx X bas idx x z z).re`.

Introduce `z`. Rewrite using `[h1, Complex.re_sum]`. Use `Finset.sum_nonneg fun j _ => ?_` and prove the remaining obligations. Establish `e : ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z j) = ((X.c (idx j).1 * Complex.normSq (z j) : ℝ) : ℂ)`. Rewrite using `[_root_.mul_assoc, Complex.mul_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.ofReal_re]`. Conclude with `mul_nonneg (GlobalTheory.ThFr.c_pos X _).le (Complex.normSq_nonneg _)`. Use `⟨h1, h2, ?_, ?_, selfD_of_isSympl hs⟩` and prove the remaining obligations.

Introduce `u hu hne`. Rewrite using `[h2]`. Unfold `Data.firstMinimumSq`. Apply `csInf_le` to reduce the goal to its premises. Use `⟨0, ?_⟩` and prove the remaining obligations.

Introduce and unpack `t ⟨v, -, -, rfl⟩`. Rewrite using `[← h2]`. Conclude with `h0 _`. Conclude with `⟨u, hu, hne, rfl⟩`. Unfold `IsUnitFr`.

Introduce `τ i`. Unfold `dmin lminor`. Rewrite using `[ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Complex.norm_real]`.

Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hx_ortho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, X.IsOrtho x → (∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j)) ∧ (∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re = ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u)) ∧ (∀ u ∈ X.Λ, u ≠ 0 → X.firstMinimumSq x ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) ∧ IsUnitFr X x ∧ SelfD X X.Λ := by
  intro E _ _ _ r X g bas idx hs x hxd ho
  have hHm := GlobalTheory.ThFr.Hm_of_isOrtho idx hs ho
  have h1 : ∀ z z', hx X bas idx x z z' = ∑ j, ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z' j) := by
    intro z z'
    rw [hx_eq_hermForm idx x z z', hHm, hermForm_diagonal_eq]
  have h2 : ∀ u, (hx X bas idx x (pv X idx x u) (pv X idx x u)).re =
      ∑ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 u) := by
    intro u
    rw [hx_eq_hermForm idx x, hHm]
    exact (congrArg Complex.re (GlobalTheory.ThFr.hermForm_diagonal_c_self idx hxd ho u)).trans
      (Complex.ofReal_re _)
  have h0 : ∀ z, 0 ≤ (hx X bas idx x z z).re := by
    intro z
    rw [h1, Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    have e : ((X.c (idx j).1 : ℝ) : ℂ) * z j * conj (z j) =
        ((X.c (idx j).1 * Complex.normSq (z j) : ℝ) : ℂ) := by
      rw [_root_.mul_assoc, Complex.mul_conj]
      push_cast
      ring
    rw [e, Complex.ofReal_re]
    exact mul_nonneg (GlobalTheory.ThFr.c_pos X _).le (Complex.normSq_nonneg _)
  refine ⟨h1, h2, ?_, ?_, selfD_of_isSympl hs⟩
  · intro u hu hne
    rw [h2]
    unfold Data.firstMinimumSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨v, -, -, rfl⟩
      rw [← h2]
      exact h0 _
    · exact ⟨u, hu, hne, rfl⟩
  · unfold IsUnitFr
    intro τ i
    unfold dmin lminor
    rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp_apply, Complex.norm_real]
    unfold sgn
    split_ifs <;> simp

end GlobalTheory.Dict
