import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeMemOfHaar

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Dx2.MN.castM_rfl, Dx2.Tower.castV_rfl, Dx2.Tower.castV_rfl]` and apply the resulting hypothesis.
-/
theorem om_cast {a b : ℕ} (h : a = b) (v v' : Fin (2 * a + k + 1) → ℂ) (g : B.Mat k a) (hg : g ∈ JF.Om k a v v') :
    D.castM h g ∈ JF.Om k b (D.castV h v) (D.castV h v') := by
  subst h; rwa [Dx2.MN.castM_rfl, Dx2.Tower.castV_rfl, Dx2.Tower.castV_rfl]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [U.lowV, liftVec]`. Rewrite using `[dif_pos (by omega)]`. Use `congr 1`. Use `ext`.

Simplify using the standard rewrite rules.
-/
theorem lowV_lift (ρ : ℕ) (v : Fin (2 * ρ + k + 1) → ℂ) : U.lowV k 1 ρ (liftVec k 1 ρ v) = v := by
  funext i
  simp only [U.lowV, liftVec]
  rw [dif_pos (by omega)]
  congr 1; ext; simp

/- English proof (translation)
Introduce `k ρ z0 z0' hz0 hz0' c hc γ hγ hγO`. Apply `om_cast` to reduce the goal to its premises. Use `set Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c with hZd`. Establish `hZdet : Z.det = c` using `by rw [Matrix.det_unique]; rfl`. Establish `hz` using `Qx4.lift_inWb hz0`.

Establish `hz'` using `Qx4.lift_inWb hz0'`. Establish `hZ : Zhat k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) = Matrix.reindex (Ux3.eC 1 ρ) (Ux3.eC 1 ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ z0 z0' γ))`. Unfold `U.mMap`. Rewrite using `[Ux3.z_hat_of_block3 _ _ hz hz', Formalism.QuantumDeterminants.Zhat_eq, lowV_lift, lowV_lift]`. Use `congr 1`.

Simplify using `[← Matrix.mul_assoc, Ux3.wMat_mul_self]`. Use `⟨(Formalism.FourierDecayAlt.P.slice_membership k 1 ρ).1 Z γ (by rw [hZdet]; exact hc) hγ, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl`. Take `⟨lv, hlv⟩` from `l`. Break down `Nat.eq_zero_or_pos lv with h0 | hpos` into its components or cases.

Substitute `h0` using the available equality. Unfold `Dmin`. Rewrite using `[Matrix.det_isEmpty]`. Conclude with `one_ne_zero`. Take `⟨l', rfl⟩ : ∃ l', lv = 1 + l'` from `⟨lv - 1, by omega⟩`.

Establish `hl' : l' ≤ ρ` using `by simp only at hl; omega`. Unfold `Dmin`. Rewrite using `[hZ, Ux3.minor_blocks Z _ l' (by omega) (by omega), hZdet]`. Use `mul_ne_zero hc ?_` and prove the remaining obligations. Conclude with `hγO.1 ⟨l', by omega⟩ hl'`.

Establish `h1 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) (Fin.last _) = Z.det * Dmin k ρ z0 z0' γ (Fin.last _)`. Unfold `Dmin`. Rewrite using `[hZ]`. Conclude with `Ux3.minor_blocks _ _ (ρ + 1) le_rfl _`. Establish `h0 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) ⟨1 + ρ, by omega⟩ = Z.det * Dmin k ρ z0 z0' γ ⟨ρ, by omega⟩`.

Unfold `Dmin`. Rewrite using `[hZ]`. Conclude with `Ux3.minor_blocks _ _ ρ (by omega) _`. Establish `ht : Tz k (1 + ρ) (liftVec k 1 ρ z0) = Tz k ρ z0` using `by rw [Ux3.tz_low _ hz, lowV_lift]`. Establish `ht' : Tz k (1 + ρ) (liftVec k 1 ρ z0') = Tz k ρ z0'` using `by rw [Ux3.tz_low _ hz', lowV_lift]`.

Establish `hG : Gf k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) = Complex.normSq c * Gf k ρ z0 z0' γ`. Unfold `Gf`. Rewrite using `[h1, h0, ht, ht', hZdet, Complex.normSq_mul, Complex.normSq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hG]`.

Conclude with `mul_pos (Complex.normSq_pos.2 hc) hγO.2`.
-/
theorem mcOm : MCOm := by
  intro k ρ z0 z0' hz0 hz0' c hc γ hγ hγO
  apply om_cast
  set Z : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => c with hZd
  have hZdet : Z.det = c := by rw [Matrix.det_unique]; rfl
  have hz := Qx4.lift_inWb hz0
  have hz' := Qx4.lift_inWb hz0'
  have hZ : Zhat k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
      Matrix.reindex (Ux3.eC 1 ρ) (Ux3.eC 1 ρ) (Matrix.fromBlocks Z 0 0 (Zhat k ρ z0 z0' γ)) := by
    unfold U.mMap
    rw [Ux3.z_hat_of_block3 _ _ hz hz', Formalism.QuantumDeterminants.Zhat_eq, lowV_lift, lowV_lift]
    congr 1
    simp [← Matrix.mul_assoc, Ux3.wMat_mul_self]
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k 1 ρ).1 Z γ (by rw [hZdet]; exact hc) hγ, ?_, ?_⟩
  · intro l hl
    obtain ⟨lv, hlv⟩ := l
    rcases Nat.eq_zero_or_pos lv with h0 | hpos
    · subst h0
      unfold Dmin
      rw [Matrix.det_isEmpty]; exact one_ne_zero
    · obtain ⟨l', rfl⟩ : ∃ l', lv = 1 + l' := ⟨lv - 1, by omega⟩
      have hl' : l' ≤ ρ := by simp only at hl; omega
      unfold Dmin
      rw [hZ, Ux3.minor_blocks Z _ l' (by omega) (by omega), hZdet]
      refine mul_ne_zero hc ?_
      exact hγO.1 ⟨l', by omega⟩ hl'
  · have h1 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) (Fin.last _) =
        Z.det * Dmin k ρ z0 z0' γ (Fin.last _) := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ (ρ + 1) le_rfl _
    have h0 : Dmin k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) ⟨1 + ρ, by omega⟩ =
        Z.det * Dmin k ρ z0 z0' γ ⟨ρ, by omega⟩ := by
      unfold Dmin
      rw [hZ]
      exact Ux3.minor_blocks _ _ ρ (by omega) _
    have ht : Tz k (1 + ρ) (liftVec k 1 ρ z0) = Tz k ρ z0 := by rw [Ux3.tz_low _ hz, lowV_lift]
    have ht' : Tz k (1 + ρ) (liftVec k 1 ρ z0') = Tz k ρ z0' := by rw [Ux3.tz_low _ hz', lowV_lift]
    have hG : Gf k (1 + ρ) (liftVec k 1 ρ z0) (liftVec k 1 ρ z0') (U.mMap k 1 ρ Z γ) =
        Complex.normSq c * Gf k ρ z0 z0' γ := by
      unfold Gf
      rw [h1, h0, ht, ht', hZdet, Complex.normSq_mul, Complex.normSq_mul]
      ring
    rw [hG]
    exact mul_pos (Complex.normSq_pos.2 hc) hγO.2

/- English proof (translation)
The claim follows from `jfStep_of mcOm`.
-/
theorem jfStep : JFStep := jfStep_of mcOm

end Formalism.FourierDecayAlt.P.PBH
