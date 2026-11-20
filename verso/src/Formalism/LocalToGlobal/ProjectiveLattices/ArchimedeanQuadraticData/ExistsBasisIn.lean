import Mathlib

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

/- English proof (translation)
Take `⟨b, hbS, hspan, hli⟩` from `exists_linearIndependent K S`. Establish `htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin r → K))`. Rewrite using `[Subtype.range_coe, hspan, hS]`. Set `B` to `Module.Basis.mk hli htop`. Set `e` to `B.indexEquiv (Pi.basisFun K (Fin r))`.

Use `⟨fun j => (e.symm j : Fin r → K), fun j => hbS (e.symm j).2, ?_⟩` and prove the remaining obligations. Conclude with `hli.comp e.symm e.symm.injective`.
-/
theorem exists_basis_in {K : Type} [Field K] {r : ℕ} (S : Set (Fin r → K))
    (hS : Submodule.span K S = ⊤) :
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ S) ∧ LinearIndependent K v := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent K S
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin r → K)) := by
    rw [Subtype.range_coe, hspan, hS]
  let B := Module.Basis.mk hli htop
  let e := B.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨fun j => (e.symm j : Fin r → K), fun j => hbS (e.symm j).2, ?_⟩
  exact hli.comp e.symm e.symm.injective

end Formalism.L2.Pj.FundamentalDomainD5
