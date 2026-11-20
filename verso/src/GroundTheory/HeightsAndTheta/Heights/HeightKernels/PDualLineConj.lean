import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding

noncomputable section

namespace DualLineConjugation

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def conjPerm (K : Type) [Field K] : Equiv.Perm (K →+* ℂ) :=
  Function.Involutive.toPerm _ (involutive_conjugate K)

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [mulVec, dotProduct, map_sum, map_mul]`. Use `Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_` and prove the remaining obligations. Simplify using `[conjPerm, dualEmbMatrix]`.
-/
theorem conj_mulVec (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by
  funext t
  simp only [mulVec, dotProduct, map_sum, map_mul]
  refine Fintype.sum_equiv ((conjPerm K).prodCongr (Equiv.refl _)) _ _ fun p => ?_
  simp [conjPerm, dualEmbMatrix]

/- English proof (translation)
Establish `h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w` using `fun w => by`. Simplify using `[dualRecover]`. Apply `(dualRecover b hb).symm.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1, LinearEquiv.symm_apply_apply]`.
-/
theorem recover_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by
  have h1 : ∀ w, (dualRecover b hb).symm w = dualEmbMatrix b *ᵥ w := fun w => by
    simp [dualRecover]
  apply (dualRecover b hb).symm.injective
  rw [LinearEquiv.symm_apply_apply, h1, ← conj_mulVec b (dualRecover b hb z), ← h1,
    LinearEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[← Complex.conj_re (star v ⬝ᵥ _)]`. Use `congr 1`. Simplify using `[dotProduct, mulVec, map_sum, map_mul]`.
-/
theorem re_conj_form {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by
  rw [← Complex.conj_re (star v ⬝ᵥ _)]
  congr 1
  simp [dotProduct, mulVec, map_sum, map_mul]

/- English proof (translation)
Unfold `dualNormSq`. Rewrite using `[recover_conj]`. Use `Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_` and prove the remaining obligations. Establish `hσ : conjPerm K σ = conjugate σ` using `rfl`. Rewrite using `[hσ, F.conj σ]`.

Conclude with `re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)`.
-/
theorem normSq_conj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by
  unfold dualNormSq
  rw [recover_conj]
  refine Fintype.sum_equiv (conjPerm K) _ _ fun σ => ?_
  have hσ : conjPerm K σ = conjugate σ := rfl
  rw [hσ, F.conj σ]
  exact re_conj_form (F.metric σ) fun j => dualRecover b hb z (conjugate σ, j)

end DualLineConjugation

/- English proof (translation)
Introduce `K _ _ i F T _ _ b hb z`. Use `show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) = Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)`. Rewrite using `[DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]`.
-/
theorem DualLineConj.proof : DualLineConj.Statement := by
  intro K _ _ i F T _ _ b hb z
  show Real.sqrt (dualNormSq b hb fun t => starRingEnd ℂ (z ⟨(), t⟩)) =
    Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩)
  rw [DualLineConjugation.normSq_conj b hb fun t => z ⟨(), t⟩]

end

end GroundTheory.Heights₂.Heights
