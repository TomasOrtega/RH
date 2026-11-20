import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFiniteStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

/- English proof (translation)
Introduce `p _ k _ _ _ G hG`. Establish `hp : (p : k) = 0` using `CharP.cast_eq_zero k p`. Establish `h1 : Subsingleton G.omega`. Use `⟨fun v w => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ u : G.omega, u = 0` using `fun u => Subtype.ext (funext fun n => by haveI := hG n`.

Take `⟨a, ha⟩` from `AugCot.d_surjective _ (u.1 n)`. Take `⟨b, rfl⟩` from `GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) a`. Rewrite using `[← ha]`. Conclude with `dUnit_pow_prime hp b)`. Rewrite using `[hz v, hz w]`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom)`. Use `Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]`. Conclude with `hinj.subsingleton`.
-/
theorem subsingleton_omega_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  intro p _ k _ _ _ G hG
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have h1 : Subsingleton G.omega := by
    refine ⟨fun v w => ?_⟩
    have hz : ∀ u : G.omega, u = 0 := fun u => Subtype.ext (funext fun n => by
      haveI := hG n
      obtain ⟨a, ha⟩ := AugCot.d_surjective _ (u.1 n)
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) a
      rw [← ha]
      exact dUnit_pow_prime hp b)
    rw [hz v, hz w]
  refine ⟨h1, ?_⟩
  have hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom) := by
    refine Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  exact hinj.subsingleton

end PDivGroup

end GlobalTheory
