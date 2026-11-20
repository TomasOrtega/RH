import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealCap

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem closure_eq_hat (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) :
    AddSubgroup.closure {u : Fin n → GlobalTheory.AdLat.RA F E | ∃ b ∈ I, ∃ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      u = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i} =
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨b, hb, z, hz, rfl⟩
    rw [SetLike.mem_coe]
    induction hz using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a, ha, b • x, Submodule.smul_mem_smul hb hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    | zero =>
      convert AddSubgroup.zero_mem _ using 1
      funext i; simp
    | add w w' _ _ h h' =>
      convert add_mem h h' using 1
      funext i; simp [mul_add]
    | neg w _ h =>
      convert neg_mem h using 1
      funext i; simp
  · unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx ⊢
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b hb y hy
      refine AddSubgroup.subset_closure ⟨b, hb, fun i => a ⊗ₜ y i,
        AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
    · intro y y' h h'
      convert add_mem h h' using 1
      funext i; simp [TensorProduct.tmul_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem span_smul_eq_top (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span E ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have hb1 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using hb0
  have e : x = (algebraMap (𝓞 E) E b)⁻¹ • (b • x) := by
    rw [← algebraMap_smul E b x, smul_smul, inv_mul_cancel₀ hb1, one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hb hx))

end General

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem finVec_mem_closure_iff : ∀ (D : D7) (V : HSp D) (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ a : Fin V.rank → D.host.E, finVec V a ∈ AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z} ↔ a ∈ I • latG V 1 := by
  intro D V I hI a
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hfg' : (I • latG V 1).FG := Submodule.FG.smul (IsNoetherian.noetherian I) hfg
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg'
    (span_smul_eq_top _ I hI hsp)).1 a
  rw [hhat, ← key, ← closure_eq_hat]
  rfl

end GlobalTheory.IdealCap
