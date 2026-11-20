import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.BesselContra

/- English proof (translation)
Introduce `m W _ _ _ J₀ A Ai h1 h2 hA π₀ hπ`. Establish `hJ : Aiᴴ * Ai = J₀`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = J₀ := by simp [h1]`.

Establish `hmem : ∀ h, h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ) → A * hᴴ * Ai ∈ Formalism.QuantumDeterminants.UH J₀`. Introduce `h hh`. Establish `hh' : h * hᴴ = 1` using `mul_eq_one_comm.1 (mem_UH_one.1 hh)`. Use `show (A * hᴴ * Ai)ᴴ * J₀ * (A * hᴴ * Ai) = J₀`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Use `_ = Aiᴴ * (h * hᴴ) * Ai := by`. Rewrite using `[hA]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = J₀ := by rw [hh', Matrix.mul_one, hJ]`.

Establish `hadj : ∀ g, g ∈ Formalism.QuantumDeterminants.UH J₀ → (Ai * g * A)ᴴ ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)`. Introduce `g hg`. Establish `hg' : gᴴ * J₀ * g = J₀` using `hg`. Use `mem_UH_one.2 (mul_eq_one_comm.1 ?_)` and prove the remaining obligations. Rewrite using `[conjTranspose_conjTranspose]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hJ, hg', hA]`. Establish `hback : ∀ g : Matrix (Fin m) (Fin m) ℂ, A * ((Ai * g * A)ᴴ)ᴴ * Ai = g`. Introduce `g`.

Rewrite using `[conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = g := by simp [h1]`. Take `⟨⟨hone, hmul⟩, hc, hi⟩` from `hπ`.

Use `⟨⟨?_, fun a ha b hb => ?_⟩, fun w l => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Establish `: A * (1 : Matrix (Fin m) (Fin m) ℂ)ᴴ * Ai = 1` using `by simp [h1] beta_reduce`. Rewrite using `[this, hone]`. Use extensionality with `l x`. Simplify using the standard rewrite rules.

Establish `e : A * (a * b)ᴴ * Ai = (A * bᴴ * Ai) * (A * aᴴ * Ai)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2, conjTranspose_mul]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = (A * bᴴ * Ai) * (A * aᴴ * Ai) := by simp only [Matrix.mul_assoc]`.

Use `beta_reduce`. Rewrite using `[e, hmul _ (hmem b hb) _ (hmem a ha)]`. Use extensionality with `l x`. Simplify using the standard rewrite rules. Take `⟨x, rfl⟩` from `(Module.evalEquiv ℂ W).surjective l`.

Establish `hφ : Continuous fun h : Matrix (Fin m) (Fin m) ℂ => A * hᴴ * Ai` using `(continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const`. Conclude with `(hc x w).comp hφ.continuousOn hmem`. Establish `hs : ∀ g ∈ Formalism.QuantumDeterminants.UH J₀, ∀ v ∈ U.dualCoannihilator, π₀ g v ∈ U.dualCoannihilator` using `fun g hg v hv => by`. Rewrite `hv`, the goal using `[Submodule.mem_dualCoannihilator]`. Introduce `l hl`.

Use `hv _ (hU _ (hadj g hg) l hl)` as an intermediate fact. Use `beta_reduce at this`. Rewrite `this` using `[hback]`. Simplify using `using this`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)]`.

Break down `hi _ hs with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `Or.inr Submodule.dualAnnihilator_bot`. Rewrite using `[h]`. Conclude with `Or.inl Submodule.dualAnnihilator_top`.
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
Apply the tactic sequence `first | exact @UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | exact UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | (intros; apply UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Bur.contragredient_conj_definiteUnitary_isContIrred : ∀ {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {J₀ A Ai : Matrix (Fin m) (Fin m) ℂ} (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hA : Aᴴ * J₀ * A = 1) {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀), IsContIrred (Formalism.QuantumDeterminants.UH (1 : Matrix (Fin m) (Fin m) ℂ)) (fun h => ((π₀ (A * hᴴ * Ai)).dualMap : Module.End ℂ (Module.Dual ℂ W))) := by
  first | exact @UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | exact UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj | (intros; apply UpperTheory.Lit.Bur.BesselContra.isContIrred_contra_conj <;> assumption)
