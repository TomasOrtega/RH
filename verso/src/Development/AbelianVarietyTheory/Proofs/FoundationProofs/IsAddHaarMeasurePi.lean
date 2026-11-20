import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MeasureTheory
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitaryTheta

/- English proof (translation)
The claim follows from `Measure.pi.isAddHaarMeasure _`.
-/
theorem isAddHaarMeasure_pi {ι G : Type} [Fintype ι] [NormedAddCommGroup G] [MeasureSpace G] [BorelSpace G]
    [SecondCountableTopology G] [SigmaFinite (volume : Measure G)] [(volume : Measure G).IsAddHaarMeasure] :
    (volume : Measure (ι → G)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

instance isAddHaarMeasure_VC (D : D7) (N N' : ℕ) : (volume : Measure (VC D N N')).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin N → ℂ)).IsAddHaarMeasure := isAddHaarMeasure_pi
  haveI : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := isAddHaarMeasure_pi
  exact isAddHaarMeasure_pi

/- English proof (translation)
Take `⟨L, hL⟩` from `GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC`. Conclude with `(GlobalTheory.PlaneLattice.area_pos_and_selfDual L _ hL).1`.
-/
theorem area_pos (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hC
  exact (GlobalTheory.PlaneLattice.area_pos_and_selfDual L _ hL).1

/- English proof (translation)
The claim follows from `D.host.conjE_apply φ x`.
-/
theorem emb_conj (D : D7) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (D.host.conj x) = (starRingEnd ℂ) (φ x) :=
  D.host.conjE_apply φ x

/- English proof (translation)
Rewrite using `[hYY, ← GlobalTheory.InducedType.sum_eq_trace D]`. Simplify using `only [map_sum, map_mul, emb_conj]`.
-/
theorem map_hYY (D : D7) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) =
      ∑ τ, ∑ i, ∑ j, embT D τ (x i j) * (starRingEnd ℂ) (embT D τ (y i j)) := by
  rw [hYY, ← GlobalTheory.InducedType.sum_eq_trace D]
  simp only [map_sum, map_mul, emb_conj]

/- English proof (translation)
Simplify using `only [map_hYY, map_sum, map_mul, Complex.conj_conj, mul_comm]`.
-/
theorem map_hYY_symm (D : D7) {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D y x : D.host.K) : D.host.E) =
      (starRingEnd ℂ) (D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E)) := by
  simp only [map_hYY, map_sum, map_mul, Complex.conj_conj, mul_comm]

/- English proof (translation)
Simplify using `only [map_hYY, Finset.mul_sum, Matrix.smul_apply]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.InducedType.restrict_K D τ z, ← mul_assoc, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem map_hYY_smul_left (D : D7) {N N' : ℕ} (z : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D (z • x) y : D.host.K) : D.host.E) =
      D.host.φ₀ (z : D.host.E) * D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  simp only [map_hYY, Finset.mul_sum, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← GlobalTheory.InducedType.restrict_K D τ z, ← mul_assoc, ← map_mul]
  rfl

/- English proof (translation)
Rewrite using `[map_hYY_symm, map_hYY_smul_left, map_mul, ← map_hYY_symm]`.
-/
theorem map_hYY_smul_right (D : D7) {N N' : ℕ} (z : D.host.K) (x y : Matrix (Fin N') (Fin N) D.host.E) :
    D.host.φ₀ ((hYY D x (z • y) : D.host.K) : D.host.E) =
      (starRingEnd ℂ) (D.host.φ₀ (z : D.host.E)) * D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  rw [map_hYY_symm, map_hYY_smul_left, map_mul, ← map_hYY_symm]

/- English proof (translation)
Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hz`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb.1 i j]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[map_hYY_smul_left, map_hYY_smul_right, ← mul_assoc, hz, one_mul]`. Rewrite using `[eq_top_iff, ← hb.2, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Establish `: b j = z⁻¹ • (z • b j)` using `by rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem onB_smul (D : D7) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b)
    (z : D.host.K) (hz : D.host.φ₀ (z : D.host.E) * (starRingEnd ℂ) (D.host.φ₀ (z : D.host.E)) = 1) :
    OnB D (fun j => z • b j) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  refine ⟨fun i j => ?_, ?_⟩
  · rw [← hb.1 i j]
    apply Subtype.ext
    apply D.host.φ₀.injective
    rw [map_hYY_smul_left, map_hYY_smul_right, ← mul_assoc, hz, one_mul]
  · rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : b j = z⁻¹ • (z • b j) := by rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.UnitaryTheta
