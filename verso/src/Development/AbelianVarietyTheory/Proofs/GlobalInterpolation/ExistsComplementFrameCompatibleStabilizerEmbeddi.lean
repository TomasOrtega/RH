import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabFrameCompat

/- English proof (translation)
Take `⟨N, -, -, hN, -⟩` from `GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx h1 h2`. Use `set X : Matrix (Fin P ⊕ Fin Q) Unit ℂ := replicateCol Unit x with hX`. Establish `e : Y = C * (N * Y).toRows₁ + X * (N * Y).toRows₂`. Rewrite using `[← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hN, Matrix.one_mul]`. Use `set U := (N * Y).toRows₁`.

Use `set V := (N * Y).toRows₂`. Use `⟨U, ?_⟩` and prove the remaining obligations. Establish `hV : V = 0`. Establish `h3 : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x = Uᴴ *ᵥ ((Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x) + Vᴴ *ᵥ ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x)` using `by conv_lhs => rw [e]`. Rewrite using `[conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Matrix.add_mul, add_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec x Vᴴ]`.

Rewrite `h3` using `[hY, h2, mulVec_zero, zero_add]`. Establish `h4 : ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) () = star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x`. Rewrite using `[← mulVec_mulVec]`. Both sides reduce to the same expression. Use extensionality with `u i`.

Establish `h5` using `congrFun h3 i`. Rewrite `h5` using `[Pi.zero_apply, mulVec, dotProduct, Fintype.sum_unique]`. Establish `h6 : star (V () i) * (star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x) = 0`. Rewrite using `[← h4]`. Conclude with `h5.symm`.

Break down `mul_eq_zero.1 h6 with h | h` into its components or cases. Simplify using `using h`. Conclude with `absurd h hx`. Rewrite `e` using `[hV, Matrix.mul_zero, add_zero]`. Conclude with `e`.
-/
theorem exists_factor {P Q P' Q' : ℕ} (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0)
    {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q')
    (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) {m : Type} [Fintype m]
    (Y : Matrix (Fin P ⊕ Fin Q) m ℂ) (hY : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) :
    ∃ U : Matrix (Fin P' ⊕ Fin Q') m ℂ, Y = C * U := by
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx h1 h2
  set X : Matrix (Fin P ⊕ Fin Q) Unit ℂ := replicateCol Unit x with hX
  have e : Y = C * (N * Y).toRows₁ + X * (N * Y).toRows₂ := by
    rw [← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hN, Matrix.one_mul]
  set U := (N * Y).toRows₁
  set V := (N * Y).toRows₂
  refine ⟨U, ?_⟩
  have hV : V = 0 := by
    have h3 : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x
        = Uᴴ *ᵥ ((Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x) + Vᴴ *ᵥ ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) := by
      conv_lhs => rw [e]
      rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Matrix.add_mul, add_mulVec,
        Matrix.mul_assoc, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec x Vᴴ]
    rw [hY, h2, mulVec_zero, zero_add] at h3
    have h4 : ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) () = star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x := by
      rw [← mulVec_mulVec]
      rfl
    ext u i
    have h5 := congrFun h3 i
    rw [Pi.zero_apply, mulVec, dotProduct, Fintype.sum_unique] at h5
    have h6 : star (V () i) * (star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x) = 0 := by
      rw [← h4]; exact h5.symm
    rcases mul_eq_zero.1 h6 with h | h
    · simpa using h
    · exact absurd h hx
  rw [hV, Matrix.mul_zero, add_zero] at e
  exact e

/- English proof (translation)
Introduce `P Q P' Q' M M' hc hM G G' B x A hA hB hdet hBx hx j hj`. Take `⟨C, h1, h2, h3⟩` from `hj`. Establish `hY : ((A * B)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A *ᵥ x) = 0`. Rewrite using `[mulVec_mulVec, conjTranspose_mul, ← hBx, ← hA]`. Simplify using `only [Matrix.mul_assoc]`.

Take `⟨A', hA'⟩` from `exists_factor hc hx h1 h2 (A * B) hY`. Establish `hG : A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G'`. Establish `: (C * A')ᴴ * Formalism.UG.Jpq P Q * (C * A') = G'`. Rewrite using `[← hA', ← hB, ← hA, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← this, ← h1, conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `⟨A', hG, ?_⟩` and prove the remaining obligations. Introduce `g g' t t' hg hgB ht ht'`. Establish `hl : (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') * A' = 1`.

Use `Matrix.nonsing_inv_mul G' (Ne.isUnit hdet)` as an intermediate fact. Rewrite using `[← this]`. Use `conv_rhs => arg 2`. Rewrite using `[← hG]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `e : Fin M' ≃ Fin P' ⊕ Fin Q'` using `(finCongr hM).trans finSumFinEquiv.symm`. Establish `hr : A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 hl`. Use `GlobalTheory.UnfoldingCompare.eq_of_frame hc hx h1 h2 ?_ ?_` and prove the remaining obligations. Establish `k : UpqT.mat t * C * A' = UpqT.mat (j t') * C * A'`. Rewrite using `[(h3 t').2, Matrix.mul_assoc, Matrix.mul_assoc, ← hA', ht', ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hA', ht, Matrix.mul_assoc, hgB, Matrix.mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hr, Matrix.mul_one]`. Use `_ = UpqT.mat (j t') * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by`. Rewrite using `[← Matrix.mul_assoc _ A', k, Matrix.mul_assoc _ A']`. Use `_ = _ := by rw [hr, Matrix.mul_one]`.

Rewrite using `[(h3 t').1, mulVec_mulVec, ht, ← mulVec_mulVec, hg]`.
-/
theorem exists_compatible_frame : ∀ (P Q P' Q' M M' : ℕ), P' + Q' + 1 = P + Q → M' = P' + Q' → ∀ (G : Matrix (Fin M) (Fin M) ℂ) (G' : Matrix (Fin M') (Fin M') ℂ) (B : Matrix (Fin M) (Fin M') ℂ) (x : Fin M → ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), Aᴴ * Formalism.UG.Jpq P Q * A = G → Bᴴ * G * B = G' → G'.det ≠ 0 → (Bᴴ * G) *ᵥ x = 0 → star (A *ᵥ x) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ x) ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb (A *ᵥ x) j → ∃ A' : Matrix (Fin P' ⊕ Fin Q') (Fin M') ℂ, A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' ∧ ∀ (g : Matrix (Fin M) (Fin M) ℂ) (g' : Matrix (Fin M') (Fin M') ℂ) (t : UpqT P Q) (t' : UpqT P' Q'), g *ᵥ x = x → g * B = B * g' → UpqT.mat t * A = A * g → UpqT.mat t' * A' = A' * g' → t = j t' := by
  intro P Q P' Q' M M' hc hM G G' B x A hA hB hdet hBx hx j hj
  obtain ⟨C, h1, h2, h3⟩ := hj
  have hY : ((A * B)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A *ᵥ x) = 0 := by
    rw [mulVec_mulVec, conjTranspose_mul, ← hBx, ← hA]
    simp only [Matrix.mul_assoc]
  obtain ⟨A', hA'⟩ := exists_factor hc hx h1 h2 (A * B) hY
  have hG : A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' := by
    have : (C * A')ᴴ * Formalism.UG.Jpq P Q * (C * A') = G' := by
      rw [← hA', ← hB, ← hA, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [← this, ← h1, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨A', hG, ?_⟩
  intro g g' t t' hg hgB ht ht'
  have hl : (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') * A' = 1 := by
    have := Matrix.nonsing_inv_mul G' (Ne.isUnit hdet)
    rw [← this]
    conv_rhs => arg 2; rw [← hG]
    simp only [Matrix.mul_assoc]
  have e : Fin M' ≃ Fin P' ⊕ Fin Q' := (finCongr hM).trans finSumFinEquiv.symm
  have hr : A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  refine GlobalTheory.UnfoldingCompare.eq_of_frame hc hx h1 h2 ?_ ?_
  · have k : UpqT.mat t * C * A' = UpqT.mat (j t') * C * A' := by
      rw [(h3 t').2, Matrix.mul_assoc, Matrix.mul_assoc, ← hA', ht', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hA', ht, Matrix.mul_assoc, hgB, Matrix.mul_assoc]
    calc UpqT.mat t * C = UpqT.mat t * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [hr, Matrix.mul_one]
      _ = UpqT.mat (j t') * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [← Matrix.mul_assoc _ A', k, Matrix.mul_assoc _ A']
      _ = _ := by rw [hr, Matrix.mul_one]
  · rw [(h3 t').1, mulVec_mulVec, ht, ← mulVec_mulVec, hg]

end GlobalTheory.StabFrameCompat
