import Mathlib

noncomputable section

namespace MassDataIdxCore

open Matrix

/- English proof (translation)
Set `φ : GL n R ≃* GL ι R` to `Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv`. Use `⟨φ.toMonoidHom.comp ψ, φ.surjective.comp hψ, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[← hQ h]`. Establish `key : ∀ i j, (((φ.toMonoidHom.comp ψ h : GL ι R) : Matrix ι ι R) - 1) i j = (((ψ h : GL n R) : Matrix n n R) - 1) (e.symm i) (e.symm j)`. Introduce `i j`.

Simplify using `[φ, Matrix.sub_apply, Matrix.one_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]`. Simplify using `only [key]`. Prove the components needed by the constructor for the conclusion. Introduce `H i j`. Simplify using `using H (e i) (e j)`.

Introduce `H i j`. Conclude with `H _ _`.
-/
theorem reindex_gl {H R : Type} [Group H] [CommRing R] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : n ≃ ι) (I : Ideal R) (Q : H → Prop) (ψ : H →* GL n R) (hψ : Function.Surjective ψ)
    (hQ : ∀ h, (∀ i j, (((ψ h : GL n R) : Matrix n n R) - 1) i j ∈ I) ↔ Q h) :
    ∃ ψ' : H →* GL ι R, Function.Surjective ψ' ∧
      ∀ h, (∀ i j, (((ψ' h : GL ι R) : Matrix ι ι R) - 1) i j ∈ I) ↔ Q h := by
  classical
  let φ : GL n R ≃* GL ι R := Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv
  refine ⟨φ.toMonoidHom.comp ψ, φ.surjective.comp hψ, fun h => ?_⟩
  rw [← hQ h]
  have key : ∀ i j, (((φ.toMonoidHom.comp ψ h : GL ι R) : Matrix ι ι R) - 1) i j =
      (((ψ h : GL n R) : Matrix n n R) - 1) (e.symm i) (e.symm j) := by
    intro i j
    simp [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  simp only [key]
  constructor
  · intro H i j
    simpa using H (e i) (e j)
  · intro H i j
    exact H _ _

end MassDataIdxCore
