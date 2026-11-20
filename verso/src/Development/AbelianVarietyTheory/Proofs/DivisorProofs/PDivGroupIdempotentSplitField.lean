import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAppEqBialgHomKernelIdealOfIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersion
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem idempotent_split (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k)
    (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧
      ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  obtain ⟨h₀, hrank⟩ := @kerIdeal_finrank_eq_pow_of_idempotent p _ k _ G u v huv h1 h2
  obtain ⟨K, i, hi⟩ := @KerGrp.exists_kernel p _ k _ G u h₀ hrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p k K G i (fun n => (hi n).1)
  have hvu : v + u = 𝟙 G := by rw [add_comm]; exact huv
  have hker : ∀ n, RingHom.ker (i.app n) = RingHom.ker (v.app n) := fun n => by
    rw [(hi n).2, ker_app_eq_kerIdeal_of_idempotents p k G v u hvu h2 h1 n]
  obtain ⟨q, hq⟩ := hfac G v (fun n => (hker n).le)
  have hiu : i ≫ u = 0 := by
    refine hom_ext fun n => BialgHom.ext fun b => ?_
    have h := (kerIdeal_le_ker_iff (u.app n) (i.app n : G.A n →ₐ[k] K.A n)).1 (hi n).2.ge b
    change i.app n (u.app n b) = (1 : WithConv (G.A n →ₐc[k] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiv : i ≫ v = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiu, zero_add, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq, hi⟩
  apply hcan K
  rw [Category.assoc, hq, hiv, Category.id_comp]

end PDivGroup

end GlobalTheory
