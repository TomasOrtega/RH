import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselContra

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Prove the second alternative. Rewrite the conclusion using the stated equalities. Prove the first alternative.

A detailed English derivation is pending.
-/
theorem isContIrred_contra_conj : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  intro m W _ _ _ J₀ A Ai h1 h2 hA π₀ hπ
  have hJ : Aiᴴ * Ai = J₀ := by
    calc Aiᴴ * Ai = Aiᴴ * (Aᴴ * J₀ * A) * Ai := by rw [hA, Matrix.mul_one]
      _ = (A * Ai)ᴴ * J₀ * (A * Ai) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by simp [h1]
  have hmem : ∀ h, h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) →
      A * hᴴ * Ai ∈ Formalism.QuantumDeterminants.UH J₀ := by
    intro h hh
    have hh' : h * hᴴ = 1 := mul_eq_one_comm.1 (mem_UH_one.1 hh)
    show (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = J₀
    calc (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = Aiᴴ * h * (Aᴴ * J₀ * A) * hᴴ * Ai := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = Aiᴴ * (h * hᴴ) * Ai := by
          rw [hA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = J₀ := by rw [hh', Matrix.mul_one, hJ]
  have hadj : ∀ g, g ∈ Formalism.QuantumDeterminants.UH J₀ →
      (Ai * g * A)ᴴ ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro g hg
    have hg' : gᴴ * J₀ * g = J₀ := hg
    refine mem_UH_one.2 (mul_eq_one_comm.1 ?_)
    rw [conjTranspose_conjTranspose]
    calc (Ai * g * A)ᴴ * (Ai * g * A) = Aᴴ * (gᴴ * (Aiᴴ * Ai) * g) * A := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hg', hA]
  have hback : ∀ g : Matrix (Fin m) (Fin m) ℂ, A * ((Ai * g * A)ᴴ)ᴴ * Ai = g := by
    intro g
    rw [conjTranspose_conjTranspose]
    calc A * (Ai * g * A) * Ai = (A * Ai) * g * (A * Ai) := by
          simp only [Matrix.mul_assoc]
      _ = g := by simp [h1]
  obtain ⟨⟨hone, hmul⟩, hc, hi⟩ := hπ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun w l => ?_, fun U hU => ?_⟩
  · have : A * (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * Ai = 1 := by simp [h1]
    beta_reduce
    rw [this, hone]
    ext l x
    simp
  · have e : A * (a * b)ᴴ * Ai = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by
      calc A * (a * b)ᴴ * Ai = A * bᴴ * (Ai * A) * aᴴ * Ai := by
            rw [h2, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by simp only [Matrix.mul_assoc]
    beta_reduce
    rw [e, hmul _ (hmem b hb) _ (hmem a ha)]
    ext l x
    simp
  · obtain ⟨x, rfl⟩ := (Module.evalEquiv ℂ W).surjective l
    have hφ : Continuous fun h : Matrix (Fin m) (Fin m) ℂ => A * hᴴ * Ai :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    exact (hc x w).comp hφ.continuousOn hmem
  · have hs : ∀ g ∈ Formalism.QuantumDeterminants.UH J₀, ∀ v ∈ U.dualCoannihilator,
        π₀ g v ∈ U.dualCoannihilator := fun g hg v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have := hv _ (hU _ (hadj g hg) l hl)
      beta_reduce at this
      rw [hback] at this
      simpa using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]
    rcases hi _ hs with h | h
    · rw [h]; exact Or.inr Submodule.dualAnnihilator_bot
    · rw [h]; exact Or.inl Submodule.dualAnnihilator_top

end UpperTheory.Lit.Bur.BesselContra

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  first | exact @UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | exact UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | (intros; apply UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj <;> assumption)
