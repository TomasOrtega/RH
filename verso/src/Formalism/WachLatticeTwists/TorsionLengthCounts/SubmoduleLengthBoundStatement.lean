import Formalism.WachLatticeTwists.Statement
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero

open Module IsDiscreteValuationRing Matrix

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

/- English proof (translation)
Introduce `O _ _ _ d _ N ℓ c hN`. Set `e : d ≃ Fin (Fintype.card d)` to `Fintype.equivFin d`. Set `A : Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) O` to `Matrix.diagonal (fun _ => (ℓ : O) ^ c)`. Establish `hA : ∀ v : Fin (Fintype.card d) → Formalism.NG.KO O, Formalism.NG.matQ O A v = ((ℓ : O) ^ c) • v`. Introduce `v`.

Use function extensionality and compare the values at `i`. Simplify using `[Formalism.NG.matQ, Formalism.NG.relMap, A, Matrix.diagonal_apply, ite_smul]`. Set `g : (d → Formalism.NG.KO O) →ₗ[O] (Fin (Fintype.card d) → Formalism.NG.KO O)` to `LinearMap.funLeft O (Formalism.NG.KO O) e.symm`. Establish `hg : Function.Injective g` using `LinearMap.funLeft_injective_of_surjective _ _ _ e.symm.surjective`. Set `f : N →ₗ[O] LinearMap.ker (Formalism.NG.matQ O A)` to `LinearMap.codRestrict _ (g.comp N.subtype) (by`.

Introduce `x`. Rewrite using `[LinearMap.mem_ker, hA]`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply]`. Rewrite using `[← map_smul, hN x x.2, map_zero])`. Establish `hf : Function.Injective f`.

Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hg` to reduce the goal to its premises. Use `congrArg Subtype.val hxy` as an intermediate fact. Simplify `this` using `[f]`.

Establish `h1` using `Module.length_le_of_injective f hf`. Rewrite `h1` using `[Formalism.NG.lenKer O (Fin (Fintype.card d)) A]`. Establish `hdet : A.det = ((ℓ : O) ^ c) ^ Fintype.card d`. Simplify using `[A, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]`. Rewrite `h1` using `[hdet, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow]`.

Rewrite using `[Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]`. Simplify `h1` using `[nsmul_eq_mul]`.
-/
theorem submoduleLengthBound_statement : Formalism.RepresentationBoundsCohomology.SubmoduleLengthBound := by
  intro O _ _ _ d _ N ℓ c hN
  classical

  let e : d ≃ Fin (Fintype.card d) := Fintype.equivFin d
  let A : Matrix (Fin (Fintype.card d)) (Fin (Fintype.card d)) O :=
    Matrix.diagonal (fun _ => (ℓ : O) ^ c)
  have hA : ∀ v : Fin (Fintype.card d) → Formalism.NG.KO O,
      Formalism.NG.matQ O A v = ((ℓ : O) ^ c) • v := by
    intro v
    funext i
    simp [Formalism.NG.matQ, Formalism.NG.relMap, A, Matrix.diagonal_apply, ite_smul]
  let g : (d → Formalism.NG.KO O) →ₗ[O] (Fin (Fintype.card d) → Formalism.NG.KO O) :=
    LinearMap.funLeft O (Formalism.NG.KO O) e.symm
  have hg : Function.Injective g :=
    LinearMap.funLeft_injective_of_surjective _ _ _ e.symm.surjective
  let f : N →ₗ[O] LinearMap.ker (Formalism.NG.matQ O A) :=
    LinearMap.codRestrict _ (g.comp N.subtype) (by
      intro x
      rw [LinearMap.mem_ker, hA]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← map_smul, hN x x.2, map_zero])
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply hg
    have := congrArg Subtype.val hxy
    simpa [f] using this
  have h1 := Module.length_le_of_injective f hf
  rw [Formalism.NG.lenKer O (Fin (Fintype.card d)) A] at h1
  have hdet : A.det = ((ℓ : O) ^ c) ^ Fintype.card d := by
    simp [A, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
  rw [hdet, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_pow] at h1
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
  simpa [nsmul_eq_mul] using h1

end Formalism.RepresentationBoundsCohomology
