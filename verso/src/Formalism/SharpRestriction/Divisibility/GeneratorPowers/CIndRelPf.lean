import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

namespace CIndRelPf

/- English proof (translation)
Set `f : (ι → S) →ₗ[S] (Fin d → S)` to `{ toFun := fun a j => ∑ ℓ, a ℓ * u ℓ j map_add' := by`. Introduce `a b`. Use function extensionality and compare the values at `j`. Simplify using `[add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`.

Introduce `c a`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.mul_sum, mul_assoc] }`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion.

Introduce `a b hab`. Take `⟨c, -, hc⟩` from `h (f a)`. Establish `ha : a = c` using `hc a (fun j => rfl)`. Establish `hb : b = c` using `hc b (fun j => congrFun hab.symm j)`. Rewrite using `[ha, hb]`.

Introduce `v`. Take `⟨a, ha, -⟩` from `h v`. Conclude with `⟨a, funext ha⟩`. Establish `hr` using `(LinearEquiv.ofBijective f hf).finrank_eq`. Rewrite `hr` using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun]`.

Conclude with `hr.symm`.
-/
theorem dim_eq_card {S : Type} [CommRing S] [Nontrivial S] {ι : Type} [Fintype ι] {d : ℕ}
    (u : ι → Fin d → S) (h : ∀ v : Fin d → S, ∃! a : ι → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    d = Fintype.card ι := by
  let f : (ι → S) →ₗ[S] (Fin d → S) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * u ℓ j
      map_add' := by
        intro a b
        funext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext j
        simp [Finset.mul_sum, mul_assoc] }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨c, -, hc⟩ := h (f a)
      have ha : a = c := hc a (fun j => rfl)
      have hb : b = c := hc b (fun j => congrFun hab.symm j)
      rw [ha, hb]
    · intro v
      obtain ⟨a, ha, -⟩ := h v
      exact ⟨a, funext ha⟩
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun] at hr
  exact hr.symm

end CIndRelPf

end Formalism.MainNotions.ModuliIntegralCharts.H1
