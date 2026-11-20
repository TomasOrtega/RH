import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormUnitPair
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open Ad3 Ad3.K GlobalTheory.CompanionTheory.WeilSplit

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSplit.Uni

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Unfold `GL2LocalData.rW`. Distinguish the cases in `h0 : c = 0`. Establish `had` using `hc h0`. Substitute `h0` using the available equality. Simplify using `only [if_true, mul_zero, add_zero, hz, mul_one]`.

Establish `e : a * (b + x * d) = a * b + x`. Take the linear combination `x * had`. Rewrite using `[e, AddChar.map_add_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg h0, if_neg h0]`. Establish `key : ∀ u : E, (χ (((a + x * c) * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) = (χ x : ℂ) * (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ)`. Introduce `u`. Establish `e : ((a + x * c) * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c = x + (a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c`. Rewrite using `[hz]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, AddChar.map_add_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression.

Simplify using `only [key, mul_assoc]`. Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rW_shift {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d x : F)
    (Φ : E → ℂ) (z : E) (hz : Algebra.norm F z = 1) (hc : c = 0 → a * d = 1) :
    GL2LocalData.rW χ σ μE lam (a + x * c) (b + x * d) c d Φ z =
      (χ x : ℂ) * GL2LocalData.rW χ σ μE lam a b c d Φ z := by
  unfold GL2LocalData.rW
  by_cases h0 : c = 0
  · have had := hc h0
    subst h0
    simp only [if_true, mul_zero, add_zero, hz, mul_one]
    have e : a * (b + x * d) = a * b + x := by
      linear_combination x * had
    rw [e, AddChar.map_add_eq_mul]
    push_cast
    ring
  · rw [if_neg h0, if_neg h0]
    have key : ∀ u : E, (χ (((a + x * c) * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ)
        = (χ x : ℂ) * (χ ((a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c) : ℂ) := by
      intro u
      have e : ((a + x * c) * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c
          = x + (a * Algebra.norm F z + d * Algebra.norm F u - Algebra.trace F E (σ z * u)) / c := by
        rw [hz]; field_simp; ring
      rw [e, AddChar.map_add_eq_mul]
      push_cast
      rfl
    simp only [key, mul_assoc]
    rw [integral_const_mul]
    ring

/- English proof (translation)
Simplify using `[uni2, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem unipotent_mul_val_real (x : F) (g : GL (Fin 2) F) :
    (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 ∧ (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 ∧
    (uni2 x * g).val 1 0 = g.val 1 0 ∧ (uni2 x * g).val 1 1 = g.val 1 1 := by
  simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `unipotent_mul_val_real x g`. Rewrite using `[Matrix.det_fin_two, Matrix.det_fin_two, h1, h2, h3, h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_unipotent_mul (x : F) (g : GL (Fin 2) F) : (uni2 x * g).val.det = g.val.det := by
  obtain ⟨h1, h2, h3, h4⟩ := unipotent_mul_val_real x g
  rw [Matrix.det_fin_two, Matrix.det_fin_two, h1, h2, h3, h4]
  ring

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `unipotent_mul_val_real x g`. Establish `hd` using `det_unipotent_mul x g`. Establish `hdet : Matrix.GeneralLinearGroup.det (uni2 x * g) = Matrix.GeneralLinearGroup.det g` using `by ext; simpa using hd`. Establish `hΔ : (g.val).det ≠ 0`. Use `(Matrix.GeneralLinearGroup.det g).ne_zero` as an intermediate fact.

Simplify using `using this`. Unfold `GL2LocalData.WcS`. Rewrite using `[hdet, hd, h1, h2, h3, h4]`. Establish `e : (g.val 0 0 + x * g.val 1 0) / (g.val).det = g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `hc : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1`. Introduce `h`. Establish `h0 : g.val 1 0 = 0`. Break down `div_eq_zero_iff.mp h with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hΔ`. Rewrite `hΔ`, the goal using `[Matrix.det_fin_two, h0]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Establish `hint : ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det)) (g.val 0 1 + x * g.val 1 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun y => Φ (y * ((g.val).det, 1))) ((u : F), ((u⁻¹ : …` using `fun u => rW_shift χ _ _ 1 _ _ _ _ x _ _ (norm_unit_pair u) hc`. Simplify using `only [hint, mul_assoc]`. Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem split_weil_whittaker_unipotent_equivariant (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (x : F)
    (g : GL (Fin 2) F) :
    GL2LocalData.WcS χ c₁ c₂ Φ (uni2 x * g) = (χ x : ℂ) * GL2LocalData.WcS χ c₁ c₂ Φ g := by
  obtain ⟨h1, h2, h3, h4⟩ := unipotent_mul_val_real x g
  have hd := det_unipotent_mul x g
  have hdet : Matrix.GeneralLinearGroup.det (uni2 x * g) = Matrix.GeneralLinearGroup.det g := by
    ext; simpa using hd
  have hΔ : (g.val).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    simpa using this
  unfold GL2LocalData.WcS
  rw [hdet, hd, h1, h2, h3, h4]
  have e : (g.val 0 0 + x * g.val 1 0) / (g.val).det = g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
    ring
  rw [e]
  have hc : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
    intro h
    have h0 : g.val 1 0 = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hΔ
    rw [Matrix.det_fin_two, h0] at hΔ ⊢
    field_simp
    simp
  have hint : ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1
        (g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det)) (g.val 0 1 + x * g.val 1 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun y => Φ (y * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      (χ x : ℂ) * GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1
        (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun y => Φ (y * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) :=
    fun u => rW_shift χ _ _ 1 _ _ _ _ x _ _ (norm_unit_pair u) hc
  simp only [hint, mul_assoc]
  rw [integral_const_mul]
  ring

end GlobalTheory.CompanionTheory.WeilSplit.Uni
