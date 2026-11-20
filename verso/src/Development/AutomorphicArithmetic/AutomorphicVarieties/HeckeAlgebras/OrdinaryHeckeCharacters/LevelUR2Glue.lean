import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Introduce `A R P κ _ _ _ _ _ N μ hcov hdir hcomp`. Establish `key : ∀ t (z : P) k k' (hk : z ∈ N k) (hk' : z ∈ N k'), ((μ k t ⟨z, hk⟩ : N k) : P) = ((μ k' t ⟨z, hk'⟩ : N k') : P)`. Introduce `t z k k' hk hk'`. Take `⟨k'', h1, h2⟩` from `hdir k k'`. Establish `e1` using `hcomp k k'' h1 t ⟨z, hk⟩`.

Establish `e2` using `hcomp k' k'' h2 t ⟨z, hk'⟩`. Establish `e3 : Submodule.inclusion h1 ⟨z, hk⟩ = Submodule.inclusion h2 ⟨z, hk'⟩` using `Subtype.ext rfl`. Rewrite using `[← e1, ← e2, e3]`. Set `f : R → P → P` to `fun t z => ((μ (hcov z).choose t ⟨z, (hcov z).choose_spec⟩ : N _) : P)`. Establish `hf : ∀ t k (y : N k), f t y = ((μ k t y : N k) : P)` using `fun t k y => key t y _ k _ y.2`.

Establish `two : ∀ z w : P, ∃ k, z ∈ N k ∧ w ∈ N k`. Introduce `z w`. Take `⟨k1, h1⟩` from `hcov z`. Take `⟨k2, h2⟩` from `hcov w`. Take `⟨k, hk1, hk2⟩` from `hdir k1 k2`.

Conclude with `⟨k, hk1 h1, hk2 h2⟩`. Set `L : R → Module.End A P` to `fun t => { toFun := f t map_add' := by`. Introduce `z w`. Take `⟨k, hz, hw⟩` from `two z w`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_add, Submodule.coe_add]`. Use `_ = f t z + f t w := by rw [← hf t k ⟨z, hz⟩, ← hf t k ⟨w, hw⟩]`. Use the proof step `map_smul' := by`. Introduce `a z`. Take `⟨k, hz⟩` from `hcov z`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨k, hz⟩` from `hcov z`. Use `show f 1 z = z`.

Conclude with `(hf 1 k ⟨z, hz⟩).trans (by simp)`. Introduce `s t`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨k, hz⟩` from `hcov z`. Use `show f (s * t) z = f s (f t z)`.

Combine the equalities or inequalities in the displayed calculation. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨k, hz⟩` from `hcov z`. Use `show f 0 z = 0`. Conclude with `(hf 0 k ⟨z, hz⟩).trans (by simp)`.

Introduce `s t`. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨k, hz⟩` from `hcov z`. Use `show f (s + t) z = f s z + f t z`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_add, LinearMap.add_apply, Submodule.coe_add]`. Use `_ = f s z + f t z := by rw [← hf s k ⟨z, hz⟩, ← hf t k ⟨z, hz⟩]`. Introduce `k t y`. Conclude with `hf t k y`.
-/
theorem UpperTheory.V.Hi.levelUR2Glue :
    ∀ (A R P κ : Type) [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty κ] (N : κ → Submodule A P) (μ : ∀ k, R →+* Module.End A (N k)), (∀ z, ∃ k, z ∈ N k) → (∀ k k', ∃ k'', N k ≤ N k'' ∧ N k' ≤ N k'') → (∀ k k' (h : N k ≤ N k') t (y : N k), ((μ k' t (Submodule.inclusion h y) : N k') : P) = (μ k t y : N k)) → ∃ α : R →+* Module.End A P, ∀ k t (y : N k), α t y = (μ k t y : N k) := by
  intro A R P κ _ _ _ _ _ N μ hcov hdir hcomp
  have key : ∀ t (z : P) k k' (hk : z ∈ N k) (hk' : z ∈ N k'),
      ((μ k t ⟨z, hk⟩ : N k) : P) = ((μ k' t ⟨z, hk'⟩ : N k') : P) := by
    intro t z k k' hk hk'
    obtain ⟨k'', h1, h2⟩ := hdir k k'
    have e1 := hcomp k k'' h1 t ⟨z, hk⟩
    have e2 := hcomp k' k'' h2 t ⟨z, hk'⟩
    have e3 : Submodule.inclusion h1 ⟨z, hk⟩ = Submodule.inclusion h2 ⟨z, hk'⟩ := Subtype.ext rfl
    rw [← e1, ← e2, e3]
  let f : R → P → P := fun t z => ((μ (hcov z).choose t ⟨z, (hcov z).choose_spec⟩ : N _) : P)
  have hf : ∀ t k (y : N k), f t y = ((μ k t y : N k) : P) := fun t k y => key t y _ k _ y.2
  have two : ∀ z w : P, ∃ k, z ∈ N k ∧ w ∈ N k := by
    intro z w
    obtain ⟨k1, h1⟩ := hcov z
    obtain ⟨k2, h2⟩ := hcov w
    obtain ⟨k, hk1, hk2⟩ := hdir k1 k2
    exact ⟨k, hk1 h1, hk2 h2⟩
  let L : R → Module.End A P := fun t =>
    { toFun := f t
      map_add' := by
        intro z w
        obtain ⟨k, hz, hw⟩ := two z w
        calc f t (z + w) = f t ((⟨z, hz⟩ + ⟨w, hw⟩ : N k) : P) := rfl
          _ = ((μ k t (⟨z, hz⟩ + ⟨w, hw⟩) : N k) : P) := hf t k _
          _ = ((μ k t ⟨z, hz⟩ : N k) : P) + ((μ k t ⟨w, hw⟩ : N k) : P) := by
            rw [map_add, Submodule.coe_add]
          _ = f t z + f t w := by rw [← hf t k ⟨z, hz⟩, ← hf t k ⟨w, hw⟩]
      map_smul' := by
        intro a z
        obtain ⟨k, hz⟩ := hcov z
        calc f t (a • z) = f t ((a • ⟨z, hz⟩ : N k) : P) := rfl
          _ = ((μ k t (a • ⟨z, hz⟩) : N k) : P) := hf t k _
          _ = a • ((μ k t ⟨z, hz⟩ : N k) : P) := by rw [map_smul, Submodule.coe_smul]
          _ = (RingHom.id A) a • f t z := by rw [RingHom.id_apply, ← hf t k ⟨z, hz⟩] }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f 1 z = z
    exact (hf 1 k ⟨z, hz⟩).trans (by simp)
  · intro s t
    refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f (s * t) z = f s (f t z)
    calc f (s * t) z = ((μ k (s * t) ⟨z, hz⟩ : N k) : P) := hf _ k ⟨z, hz⟩
      _ = ((μ k s (μ k t ⟨z, hz⟩) : N k) : P) := by rw [map_mul]; rfl
      _ = f s ((μ k t ⟨z, hz⟩ : N k) : P) := (hf s k _).symm
      _ = f s (f t z) := congrArg (f s) (hf t k ⟨z, hz⟩).symm
  · refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f 0 z = 0
    exact (hf 0 k ⟨z, hz⟩).trans (by simp)
  · intro s t
    refine LinearMap.ext fun z => ?_
    obtain ⟨k, hz⟩ := hcov z
    show f (s + t) z = f s z + f t z
    calc f (s + t) z = ((μ k (s + t) ⟨z, hz⟩ : N k) : P) := hf _ k ⟨z, hz⟩
      _ = ((μ k s ⟨z, hz⟩ : N k) : P) + ((μ k t ⟨z, hz⟩ : N k) : P) := by
        rw [map_add, LinearMap.add_apply, Submodule.coe_add]
      _ = f s z + f t z := by rw [← hf s k ⟨z, hz⟩, ← hf t k ⟨z, hz⟩]
  · intro k t y
    exact hf t k y
