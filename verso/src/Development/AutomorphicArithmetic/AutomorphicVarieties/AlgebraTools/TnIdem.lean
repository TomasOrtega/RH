import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnAlgMapSmulMem

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `R _ _ _ _ κ M _ _ _ T hT`. Set `S` to `Algebra.adjoin R (Set.range T)`. Use `haveI : Module.Finite R S := by haveI : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance`. Conclude with `(inferInstance : Module.Finite R (Subalgebra.toSubmodule S))`. Use `letI : CommRing S := Algebra.adjoinCommRingOfComm R (by`.

Introduce and unpack `_ ⟨i, rfl⟩ _ ⟨j, rfl⟩`. Conclude with `hT i j)`. Set `t : κ → S` to `fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩`. Take `⟨e, he, -, hx⟩` from `topNil_eq_idem R S κ t`. Establish `hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T`.

Use function extensionality and compare the values at `i`. Both sides reduce to the same expression. Establish `he' : IsIdempotentElem (e : Module.End R M)` using `congrArg Subtype.val he`. Use `⟨(e : Module.End R M), e.2, he', ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Establish `h` using `hx M x`. Rewrite `h` using `[hfun]`. Rewrite using `[h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `LinearMap.congr_fun he' y`. Introduce `h2`. Conclude with `⟨x, h2⟩`.
-/
theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  haveI : Module.Finite R S := by
    haveI : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  letI : CommRing S := Algebra.adjoinCommRingOfComm R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hT i j)
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
