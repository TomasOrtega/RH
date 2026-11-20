import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualRev

/- English proof (translation)
Use `set v : Fin r → Fin r → Ω := fun j t => w.dualBasis (Fin.rev j) (fun s => if t = s then 1 else 0) with hv`. Establish `key : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0`. Introduce `i j`. Establish `h1 : w i ⬝ᵥ v j = w.dualBasis (Fin.rev j) (w i)`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ (w.dualBasis (Fin.rev j)) (w i)]`.

Simplify using `[dotProduct, hv, smul_eq_mul]`. Rewrite using `[h1, Module.Basis.dualBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Establish `hli : LinearIndependent Ω v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j0`.

Use `congrArg (fun x => w (Fin.rev j0) ⬝ᵥ x) hg` as an intermediate fact. Simplify using `only [dotProduct_sum, dotProduct_smul, key, smul_eq_mul, dotProduct_zero] at this`. Simplify `this` using `[Fin.rev_inj, eq_comm]`. Establish `hcard : Fintype.card (Fin r) = Module.finrank Ω (Fin r → Ω)`. Rewrite using `[Fintype.card_fin, Module.finrank_fin_fun]`.

Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality. Conclude with `⟨w, fun i => i.elim0⟩`. Use `haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩`. Use `⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩` and prove the remaining obligations.

Introduce `i j`. Rewrite using `[coe_basisOfLinearIndependentOfCardEqFinrank]`. Conclude with `key i j`.
-/
theorem dotDualRevBasis (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)) :
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  classical
  set v : Fin r → Fin r → Ω := fun j t => w.dualBasis (Fin.rev j) (fun s => if t = s then 1 else 0) with hv
  have key : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
    intro i j
    have h1 : w i ⬝ᵥ v j = w.dualBasis (Fin.rev j) (w i) := by
      rw [LinearMap.pi_apply_eq_sum_univ (w.dualBasis (Fin.rev j)) (w i)]
      simp [dotProduct, hv, smul_eq_mul]
    rw [h1, Module.Basis.dualBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hli : LinearIndependent Ω v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j0
    have := congrArg (fun x => w (Fin.rev j0) ⬝ᵥ x) hg
    simp only [dotProduct_sum, dotProduct_smul, key, smul_eq_mul, dotProduct_zero] at this
    simpa [Fin.rev_inj, eq_comm] using this
  have hcard : Fintype.card (Fin r) = Module.finrank Ω (Fin r → Ω) := by
    rw [Fintype.card_fin, Module.finrank_fin_fun]
  by_cases hr : r = 0
  · subst hr
    exact ⟨w, fun i => i.elim0⟩
  haveI : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
  intro i j
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact key i j

end GlobalTheory.CompanionTheory.Ar.DualRev
