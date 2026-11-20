import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WeilPsi

/- English proof (translation)
Substitute `hpq` using the available equality. Both sides reduce to the same expression.
-/
theorem choose_congr {α : Type*} {p q : α → Prop} (hpq : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    hp.choose = hq.choose := by
  subst hpq
  rfl

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem unipotent_mul_val_real (x : F) (g : GL (Fin 2) F) :
    (uni2 x * g).val =
      !![g.val 0 0 + x * g.val 1 0, g.val 0 1 + x * g.val 1 1; g.val 1 0, g.val 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Rewrite using `[unipotent_mul_val_real, Matrix.det_fin_two_of, Matrix.det_fin_two g.val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_left_unipotent_mul (x : F) (g : GL (Fin 2) F) : ((uni2 x * g).val).det = (g.val).det := by
  rw [unipotent_mul_val_real, Matrix.det_fin_two_of, Matrix.det_fin_two g.val]
  ring

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Establish `had` using `hc0 hc`. Substitute `hc` using the available equality. Establish `h1 : a * (b + x * d) * Algebra.norm F (1 : E) = x + a * b * Algebra.norm F (1 : E)`. Rewrite using `[map_one]`.

Take the linear combination `x * had`. Simplify using `only [rW, if_true, mul_zero, add_zero]`. Rewrite using `[h1, AddChar.map_add_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hk : ∀ u : E, ((χ (((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u = (χ x : ℂ) * (((χ ((a * Algebra.norm F (1 : E) + d * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u)`. Introduce `u`. Establish `h2 : ((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / c = x + (a * Algebra.norm F (1 : E) + d * Algebra.norm F u - Algebra.trace F E (σ 1 * u)) / c`. Rewrite using `[map_one]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, AddChar.map_add_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [rW, if_neg hc, hk]`.

Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rW_shift (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d x : F)
    (hc0 : c = 0 → a * d = 1) (Φ : E → ℂ) :
    rW χ σ μE lam (a + x * c) (b + x * d) c d Φ 1 = (χ x : ℂ) * rW χ σ μE lam a b c d Φ 1 := by
  by_cases hc : c = 0
  · have had := hc0 hc
    subst hc
    have h1 : a * (b + x * d) * Algebra.norm F (1 : E) = x + a * b * Algebra.norm F (1 : E) := by
      rw [map_one]
      linear_combination x * had
    simp only [rW, if_true, mul_zero, add_zero]
    rw [h1, AddChar.map_add_eq_mul]
    push_cast
    ring
  · have hk : ∀ u : E,
        ((χ (((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u =
          (χ x : ℂ) * (((χ ((a * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c) : Circle) : ℂ) * Φ u) := by
      intro u
      have h2 : ((a + x * c) * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c =
          x + (a * Algebra.norm F (1 : E) + d * Algebra.norm F u -
            Algebra.trace F E (σ 1 * u)) / c := by
        rw [map_one]
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul]
      push_cast
      ring
    simp only [rW, if_neg hc, hk]
    rw [integral_const_mul]
    ring

/- English proof (translation)
Establish `hdet` using `det_left_unipotent_mul x g`. Establish `hΔ : (g.val).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det g.val).1 g.isUnit).ne_zero`. Unfold `Wc`. Distinguish the cases in `h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det`. Establish `h' : ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det` using `by rwa [hdet]`.

Rewrite using `[dif_pos h', dif_pos h]`. Establish `hch : h'.choose = h.choose` using `choose_congr (by simp only [hdet]) h' h`. Establish `e00 : (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0`. Rewrite using `[unipotent_mul_val_real]`. Simplify using the standard rewrite rules.

Establish `e01 : (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1`. Rewrite using `[unipotent_mul_val_real]`. Simplify using the standard rewrite rules. Establish `e10 : (uni2 x * g).val 1 0 = g.val 1 0`. Rewrite using `[unipotent_mul_val_real]`.

Simplify using the standard rewrite rules. Establish `e11 : (uni2 x * g).val 1 1 = g.val 1 1`. Rewrite using `[unipotent_mul_val_real]`. Simplify using the standard rewrite rules. Establish `hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det = g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det)`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc0 : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1`. Introduce `h0`. Establish `hC : g.val 1 0 = 0`. Break down `div_eq_zero_iff.1 h0 with h1 | h1` into its components or cases.

Conclude with `h1`. Conclude with `absurd h1 hΔ`. Establish `hD : (g.val).det = g.val 0 0 * g.val 1 1`. Rewrite using `[Matrix.det_fin_two g.val, hC]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[div_mul_eq_mul_div, ← hD]`. Conclude with `div_self hΔ`. Rewrite using `[hch, hdet, e00, e01, e10, e11, hsplit, rW_shift χ σ μE lam _ _ _ _ x hc0]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det` using `by rwa [hdet]`.

Rewrite using `[dif_neg h', dif_neg h, mul_zero]`.
-/
theorem weil_whittaker_unipotent_equivariance (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ)
    (Φ : E → ℂ) (x : F) (g : GL (Fin 2) F) :
    Wc χ σ μE lam c Φ (uni2 x * g) = (χ x : ℂ) * Wc χ σ μE lam c Φ g := by
  have hdet := det_left_unipotent_mul x g
  have hΔ : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g.val).1 g.isUnit).ne_zero
  unfold Wc
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have h' : ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_pos h', dif_pos h]
    have hch : h'.choose = h.choose :=
      choose_congr (by simp only [hdet]) h' h
    have e00 : (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 := by
      rw [unipotent_mul_val_real]; simp
    have e01 : (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 := by
      rw [unipotent_mul_val_real]; simp
    have e10 : (uni2 x * g).val 1 0 = g.val 1 0 := by
      rw [unipotent_mul_val_real]; simp
    have e11 : (uni2 x * g).val 1 1 = g.val 1 1 := by
      rw [unipotent_mul_val_real]; simp
    have hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det =
        g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
      ring
    have hc0 : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
      intro h0
      have hC : g.val 1 0 = 0 := by
        rcases div_eq_zero_iff.1 h0 with h1 | h1
        · exact h1
        · exact absurd h1 hΔ
      have hD : (g.val).det = g.val 0 0 * g.val 1 1 := by
        rw [Matrix.det_fin_two g.val, hC]
        ring
      rw [div_mul_eq_mul_div, ← hD]
      exact div_self hΔ
    rw [hch, hdet, e00, e01, e10, e11, hsplit,
      rW_shift χ σ μE lam _ _ _ _ x hc0]
    ring
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_neg h', dif_neg h, mul_zero]

end

/- English proof (translation)
Unfold `Ad3.K.GL2LocalData.WPsi Ad3.K.GL2LocalData.ForEF`. Introduce `F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ _ _ σ _ η _ c Φ x g`. Conclude with `weil_whittaker_unipotent_equivariance χ σ _ _ c Φ x g`.
-/
theorem wPsi : Ad3.K.GL2LocalData.WPsi := by
  unfold Ad3.K.GL2LocalData.WPsi Ad3.K.GL2LocalData.ForEF
  intro F _ _ _ _ _ _ _ χ _ _ E _ _ _ _ _ _ _ _ _ σ _ η _ c Φ x g
  exact weil_whittaker_unipotent_equivariance χ σ _ _ c Φ x g

end GlobalTheory.CompanionTheory.WeilPsi
