import Mathlib
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral

namespace Formalism.HermitianLattices.RamifiedHeckeModels

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem lemma_c_twist_ramified : LemmaC_twist_ram := by
  unfold LemmaC_twist_ram
  intro R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin
  have hpow : ∀ n : ℕ, ∀ x : M, ϖ ^ n • x ∈ P → x ∈ P := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply hsat
      apply ih
      rwa [← mul_smul, ← pow_succ]
  have h1 : (S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B ⊓ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hSB ⟨s, hs.1, rfl⟩, by simpa using P.smul_mem (ϖ ^ b) hs.2⟩
  have h2 : (B ⊓ P).map U ≤ S ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hBU ⟨x, hx.1, rfl⟩, hPU ⟨x, hx.2, rfl⟩⟩
  have h3 : (S ⊓ P).map D ≤ B ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hSD ⟨x, hx.1, rfl⟩, hPD ⟨x, hx.2, rfl⟩⟩
  let ι : (S ⊓ P : Submodule R M) →ₗ[R] S := Submodule.inclusion inf_le_left
  have hι : Function.Injective ι := Submodule.inclusion_injective _
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R S)
    ((S ⊓ P).comap S.subtype)
  let eN : ((S ⊓ P).comap S.subtype) ≃ₗ[R] (S ⊓ P : Submodule R M) :=
    Submodule.comapSubtypeEquivOfLe inf_le_left
  haveI : Module.Free R (S ⊓ P : Submodule R M) := Module.Free.of_basis (bN.map eN)
  haveI : Module.Finite R (S ⊓ P : Submodule R M) := Module.Finite.of_basis (bN.map eN)
  have key := lemma_c_under_twist
  unfold LemmaC_twist at key
  have key' := key R ϖ hϖ M (S ⊓ P) (B ⊓ P) U D e b h1 h2 h3 hUD inferInstance inferInstance
  have hrank : Module.finrank R (S ⊓ P : Submodule R M) ≤ Module.finrank R S :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hlen : Module.length R ((B ⊓ P : Submodule R M) ⧸
      ((S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap (B ⊓ P).subtype) ≤
      Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) := by
    refine Module.length_le_of_injective
      (Submodule.mapQ _ _ (Submodule.inclusion (inf_le_left : B ⊓ P ≤ B)) ?_) ?_
    · intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact Submodule.map_mono inf_le_left hx
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢
      obtain ⟨s, hs, hsx⟩ := hq
      refine ⟨s, ⟨hs, ?_⟩, hsx⟩
      apply hpow b
      have hx' : (ϖ ^ b • s : M) = x := by simpa using hsx
      rw [hx']
      exact x.2.2
  refine key'.trans (add_le_add hlen ?_)
  exact_mod_cast Nat.mul_le_mul_left e hrank

end Formalism.HermitianLattices.RamifiedHeckeModels
