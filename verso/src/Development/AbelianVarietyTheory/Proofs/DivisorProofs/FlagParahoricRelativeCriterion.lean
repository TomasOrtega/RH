import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

namespace GlobalTheory.FlagBundle.FrameChange

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K]

/- English proof (translation)
Introduce `τ` and use `⟨(h2 τ).1, (h2 τ).2.1, (h2 τ).2.2.1, (h1 τ).2.2.2⟩`.
-/
theorem par_of_top_of_zero {O : Subring K} {g : GlobalTheory.FlagBundle.Mat m K}
    (h1 : GlobalTheory.FlagBundle.Par k ⊤ g) (h2 : GlobalTheory.FlagBundle.Par 0 O g) : GlobalTheory.FlagBundle.Par k O g := fun τ =>
  ⟨(h2 τ).1, (h2 τ).2.1, (h2 τ).2.2.1, (h1 τ).2.2.2⟩

/- English proof (translation)
Introduce `hB`. Use `h.det_ne τ` as an intermediate fact. Rewrite `this` using `[Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, hB, Ring.inverse_zero, mul_zero]`. Conclude with `this rfl`.
-/
theorem det_ne_of_par {O : Subring K} {A B : GlobalTheory.FlagBundle.Mat m K}
    (h : GlobalTheory.FlagBundle.Par k O (A * B⁻¹)) (τ : ι) : (B τ).det ≠ 0 := by
  intro hB
  have := h.det_ne τ
  rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, hB, Ring.inverse_zero, mul_zero] at this
  exact this rfl

/- English proof (translation)
Establish `hB : ∀ τ, (B τ).det ≠ 0` using `det_ne_of_par hAB`. Establish `hAd : ∀ τ, (A τ).det ≠ 0` using `hA.det_ne`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `par_of_top_of_zero ?_ (h1.mul hA.inv)` and prove the remaining obligations.

Establish `e : A' * A⁻¹ = (A' * B⁻¹) * (A * B⁻¹)⁻¹`. Rewrite using `[GlobalTheory.FlagBundle.Mat.mul_inv_rev, GlobalTheory.FlagBundle.Mat.inv_inv hB, mul_assoc, ← mul_assoc B⁻¹, GlobalTheory.FlagBundle.Mat.inv_mul hB, one_mul]`. Rewrite using `[e]`. Conclude with `h2.mul hAB.inv`. Introduce `h`.

Establish `e1 : A' = (A' * A⁻¹) * A` using `by rw [mul_assoc, GlobalTheory.FlagBundle.Mat.inv_mul hAd, mul_one]`. Establish `e2 : A' * B⁻¹ = (A' * A⁻¹) * (A * B⁻¹)`. Rewrite using `[mul_assoc, ← mul_assoc A⁻¹, GlobalTheory.FlagBundle.Mat.inv_mul hAd, one_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`.

Conclude with `(h.mono (fun τ => Nat.zero_le (k τ)) le_rfl).mul hA`. Rewrite using `[e2]`. Conclude with `(h.mono le_rfl le_top).mul hAB`.
-/
theorem par_iff (O : Subring K) (A B A' : GlobalTheory.FlagBundle.Mat m K)
    (hA : GlobalTheory.FlagBundle.Par 0 O A) (hAB : GlobalTheory.FlagBundle.Par k ⊤ (A * B⁻¹)) :
    GlobalTheory.FlagBundle.Par 0 O A' ∧ GlobalTheory.FlagBundle.Par k ⊤ (A' * B⁻¹) ↔ GlobalTheory.FlagBundle.Par k O (A' * A⁻¹) := by
  have hB : ∀ τ, (B τ).det ≠ 0 := det_ne_of_par hAB
  have hAd : ∀ τ, (A τ).det ≠ 0 := hA.det_ne
  constructor
  · rintro ⟨h1, h2⟩
    refine par_of_top_of_zero ?_ (h1.mul hA.inv)
    have e : A' * A⁻¹ = (A' * B⁻¹) * (A * B⁻¹)⁻¹ := by
      rw [GlobalTheory.FlagBundle.Mat.mul_inv_rev, GlobalTheory.FlagBundle.Mat.inv_inv hB, mul_assoc, ← mul_assoc B⁻¹,
        GlobalTheory.FlagBundle.Mat.inv_mul hB, one_mul]
    rw [e]
    exact h2.mul hAB.inv
  · intro h
    have e1 : A' = (A' * A⁻¹) * A := by rw [mul_assoc, GlobalTheory.FlagBundle.Mat.inv_mul hAd, mul_one]
    have e2 : A' * B⁻¹ = (A' * A⁻¹) * (A * B⁻¹) := by
      rw [mul_assoc, ← mul_assoc A⁻¹, GlobalTheory.FlagBundle.Mat.inv_mul hAd, one_mul]
    refine ⟨?_, ?_⟩
    · rw [e1]; exact (h.mono (fun τ => Nat.zero_le (k τ)) le_rfl).mul hA
    · rw [e2]; exact (h.mono le_rfl le_top).mul hAB

end GlobalTheory.FlagBundle.FrameChange
