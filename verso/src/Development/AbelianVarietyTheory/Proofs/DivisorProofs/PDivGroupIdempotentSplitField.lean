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
Take `⟨h₀, hrank⟩` from `@kerIdeal_finrank_eq_pow_of_idempotent p _ k _ G u v huv h1 h2`. Take `⟨K, i, hi⟩` from `@KerGrp.exists_kernel p _ k _ G u h₀ hrank`. Take `⟨hfac, hcan⟩` from `factor_closedImmersion p k K G i (fun n => (hi n).1)`. Establish `hvu : v + u = 𝟙 G` using `by rw [add_comm]; exact huv`. Establish `hker : ∀ n, RingHom.ker (i.app n) = RingHom.ker (v.app n)` using `fun n => by`.

Rewrite using `[(hi n).2, ker_app_eq_kerIdeal_of_idempotents p k G v u hvu h2 h1 n]`. Take `⟨q, hq⟩` from `hfac G v (fun n => (hker n).le)`. Establish `hiu : i ≫ u = 0`. Use `hom_ext fun n => BialgHom.ext fun b => ?_` and prove the remaining obligations. Establish `h` using `(kerIdeal_le_ker_iff (u.app n) (i.app n : G.A n →ₐ[k] K.A n)).1 (hi n).2.ge b`.

Express the relevant statement in the definitionally equal form `i.app n (u.app n b) = (1 : WithConv (G.A n →ₐc[k] K.A n)).ofConv b`. Use `Eq.trans h ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hiv : i ≫ v = i`. Establish `e` using `Preadditive.comp_add _ _ _ i u v`.

Rewrite `e` using `[huv, hiu, zero_add, Category.comp_id]`. Conclude with `e.symm`. Use `⟨K, i, q, ?_, hq, hi⟩` and prove the remaining obligations. Apply `hcan K` to reduce the goal to its premises. Rewrite using `[Category.assoc, hq, hiv, Category.id_comp]`.
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
