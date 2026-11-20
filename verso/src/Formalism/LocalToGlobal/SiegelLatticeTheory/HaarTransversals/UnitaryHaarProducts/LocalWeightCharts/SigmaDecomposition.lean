import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Matrix
open scoped InnerProductSpace

namespace WlocSk

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

/- English proof (translation)
The claim follows from `Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)`.
-/
lemma cay_inv_mul {P : Mat k r} (hP : IsUnit P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

/- English proof (translation)
The claim follows from `Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)`.
-/
lemma cay_mul_inv {P : Mat k r} (hP : IsUnit P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

/- English proof (translation)
Establish `h2` using `cay_mul_inv hP.1`. Establish `hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r` using `hg`. Use `show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε`. Rewrite `hg'` using `[← hP.2]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hg']`. Use `_ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [h2]; simp`.
-/
lemma cay_mem {P : Mat k r} (hP : IsCayley k r ε P) {g : Mat k r} (hg : g ∈ Gr k r) :
    P * g * P⁻¹ ∈ UJset ε := by
  have h2 := cay_mul_inv hP.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [← hP.2] at hg'
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hg']
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2]; simp

/- English proof (translation)
Establish `h1` using `cay_inv_mul hP`. Establish `h2` using `cay_mul_inv hP`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma cay_back {P : Mat k r} (hP : IsUnit P) (g : Mat k r) : P⁻¹ * (P * g * P⁻¹) * P = g := by
  have h1 := cay_inv_mul hP
  have h2 := cay_mul_inv hP
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

end Cayley

/- English proof (translation)
Introduce `k r ε lam H _ _ σ hσ`. Take `⟨P, hP, hDS⟩` from `hσ`. Take `⟨⟨h1, hmul⟩, hiso, hcont⟩` from `hDS.2.2.1`. Establish `hPu` using `hP.1.1`. Establish `hσ' : ∀ g, σ g = σ (P⁻¹ * (P * g * P⁻¹) * P)` using `fun g => by rw [cay_back hPu]`.

Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `h1` as an intermediate fact. Simplify using `only [Matrix.mul_one, cay_inv_mul hPu] at this`. Conclude with `this`. Introduce `a ha b hb`.

Establish `hab : P * (a * b) * P⁻¹ = P * a * P⁻¹ * (P * b * P⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cay_inv_mul hPu]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = P * a * P⁻¹ * (P * b * P⁻¹) := by simp only [Matrix.mul_assoc]`.

Rewrite using `[hσ' (a * b), hab]`. Use `hmul _ (cay_mem hP.1 ha) _ (cay_mem hP.1 hb)` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this, cay_back hPu, cay_back hPu]`. Introduce `g hg v`.

Rewrite using `[hσ' g]`. Conclude with `hiso _ (cay_mem hP.1 hg) v`. Introduce `v`. Establish `hc : Continuous fun g : Mat k r => P * g * P⁻¹` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Use `(hcont v).comp hc.continuousOn (fun g hg => cay_mem hP.1 hg)` as an intermediate fact.

Use `this.congr (fun g _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[cay_back hPu]`.
-/
theorem sigma_decomposition : SigmaG := by
  intro k r ε lam H _ _ σ hσ
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  have hPu := hP.1.1
  have hσ' : ∀ g, σ g = σ (P⁻¹ * (P * g * P⁻¹) * P) := fun g => by rw [cay_back hPu]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := h1
    simp only [Matrix.mul_one, cay_inv_mul hPu] at this
    exact this
  · intro a ha b hb
    have hab : P * (a * b) * P⁻¹ = P * a * P⁻¹ * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
            rw [cay_inv_mul hPu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = P * a * P⁻¹ * (P * b * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [hσ' (a * b), hab]
    have := hmul _ (cay_mem hP.1 ha) _ (cay_mem hP.1 hb)
    simp only at this
    rw [this, cay_back hPu, cay_back hPu]
  · intro g hg v
    rw [hσ' g]
    exact hiso _ (cay_mem hP.1 hg) v
  · intro v
    have hc : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hcont v).comp hc.continuousOn (fun g hg => cay_mem hP.1 hg)
    refine this.congr (fun g _ => ?_)
    simp only [Function.comp]
    rw [cay_back hPu]

end WlocSk
