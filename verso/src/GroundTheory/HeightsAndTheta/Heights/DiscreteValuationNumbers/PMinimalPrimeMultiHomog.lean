import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

section Regrading

variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']

/- English proof (translation)
Simplify using `[Finsupp.weight_apply, map_finsuppSum, map_nsmul]`.
-/
theorem weight_comp_addMonoidHom (φ : M →+ M') (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun v => φ (w v)) d = φ (Finsupp.weight w d) := by
  simp [Finsupp.weight_apply, map_finsuppSum, map_nsmul]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_comp_addMonoidHom, hφ.eq_iff]`.
-/
theorem weightedHomogeneousComponent_comp_addMonoidHom (φ : M →+ M') (hφ : Function.Injective φ)
    (w : σ → M) (b : M) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun v => φ (w v)) (φ b) f = weightedHomogeneousComponent w b f := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent,
    weight_comp_addMonoidHom, hφ.eq_iff]

end Regrading

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]

def lexRelabel (e : K ≃ Fin (Fintype.card K)) : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun j => b (e.symm j))
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Introduce `i` and use `⟨fun k => ofLex i (e k), by change toLex (fun j => ofLex i (e (e.symm j))) = i simp only [Equiv.apply_symm_apply] rfl⟩`.
-/
theorem lexRelabel_surjective (e : K ≃ Fin (Fintype.card K)) : Function.Surjective (lexRelabel e) :=
  fun i => ⟨fun k => ofLex i (e k), by
    change toLex (fun j => ofLex i (e (e.symm j))) = i
    simp only [Equiv.apply_symm_apply]
    rfl⟩

/- English proof (translation)
Introduce `a b h`. Establish `h' : (fun j => a (e.symm j)) = fun j => b (e.symm j)` using `toLex.injective h`. Use function extensionality and compare the values at `k`. Simplify using `using congrFun h' (e k)`.
-/
theorem lexRelabel_injective (e : K ≃ Fin (Fintype.card K)) : Function.Injective (lexRelabel e) := by
  intro a b h
  have h' : (fun j => a (e.symm j)) = fun j => b (e.symm j) := toLex.injective h
  funext k
  simpa using congrFun h' (e k)

variable [DecidableEq K] [DecidableEq (Lex (Fin (Fintype.card K) → ℕ))]

/- English proof (translation)
Use `letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))`. Introduce `i r hr`. Express the relevant statement in the definitionally equal form `((weightedDecomposition R (fun v => lexRelabel e (blockWeight ι v))).decompose' r i : MRing ι R) ∈ I`. Rewrite using `[weightedDecomposition.decompose'_apply]`. Take `⟨b, rfl⟩` from `lexRelabel_surjective e i`.

Rewrite using `[weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]`. Conclude with `hI r hr b`.
-/
theorem isHomogeneous_lex_of_isMultiHomogIdeal (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
    I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro i r hr
  change ((weightedDecomposition R (fun v => lexRelabel e (blockWeight ι v))).decompose' r i :
    MRing ι R) ∈ I
  rw [weightedDecomposition.decompose'_apply]
  obtain ⟨b, rfl⟩ := lexRelabel_surjective e i
  rw [weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact hI r hr b

/- English proof (translation)
Use `letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))`. Introduce `f hf b`. Rewrite using `[← weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]`. Conclude with `weightedHomogeneousComponent_mem_of_mem R _ hI hf _`.
-/
theorem isMultiHomogIdeal_of_isHomogeneous_lex (e : K ≃ Fin (Fintype.card K))
    {I : Ideal (MRing ι R)}
    (hI : letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
      I.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))) :
    IsMultiHomogIdeal I := by
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  intro f hf b
  rw [← weightedHomogeneousComponent_comp_addMonoidHom _ (lexRelabel_injective e)]
  exact weightedHomogeneousComponent_mem_of_mem R _ hI hf _

end Lex

/- English proof (translation)
Introduce `R _ K _ _ ι J W hJ hW`. Set `e : K ≃ Fin (Fintype.card K)` to `Fintype.equivFin K`. Use `letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq`. Use `letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))`. Establish `hJh : J.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))` using `isHomogeneous_lex_of_isMultiHomogIdeal e hJ`.

Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hcore : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal.IsPrime` using `hWp.homogeneousCore`. Establish `hJle : J ≤ (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal`. Rewrite using `[← hJh.toIdeal_homogeneousCore_eq_self]`. Conclude with `Ideal.homogeneousCore_mono (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) hW.1.2`.

Establish `hle : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal ≤ W` using `Ideal.toIdeal_homogeneousCore_le (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) W`. Establish `heq : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal = W` using `le_antisymm hle (hW.2 ⟨hcore, hJle⟩ hle)`. Apply `isMultiHomogIdeal_of_isHomogeneous_lex e` to reduce the goal to its premises. Rewrite using `[← heq]`. Conclude with `(W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).isHomogeneous`.
-/
theorem MinimalPrimeMultiHomog.proof : MinimalPrimeMultiHomog.Statement := by
  intro R _ K _ _ ι J W hJ hW
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  letI : DecidableEq (Lex (Fin (Fintype.card K) → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra R (fun v => lexRelabel e (blockWeight ι v))
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) := isHomogeneous_lex_of_isMultiHomogIdeal e hJ
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal.IsPrime := hWp.homogeneousCore
  have hJle : J ≤ (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) hW.1.2
  have hle : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal ≤ W := Ideal.toIdeal_homogeneousCore_le (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v))) W
  have heq : (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).toIdeal = W := le_antisymm hle (hW.2 ⟨hcore, hJle⟩ hle)
  apply isMultiHomogIdeal_of_isHomogeneous_lex e
  rw [← heq]
  exact (W.homogeneousCore (weightedHomogeneousSubmodule R (fun v => lexRelabel e (blockWeight ι v)))).isHomogeneous

end GroundTheory.Heights₂.Heights.NumbersDVR
