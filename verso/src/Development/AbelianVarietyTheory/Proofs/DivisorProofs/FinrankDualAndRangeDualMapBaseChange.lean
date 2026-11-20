import Mathlib

open TensorProduct

namespace GlobalTheory.DualFibreRank

section
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]

noncomputable def cmp (M : Type) [AddCommGroup M] [Module O M] :
    A ⊗[O] Module.Dual O M →ₗ[A] Module.Dual A (A ⊗[O] M) :=
  LinearMap.liftBaseChange A (Module.Dual.baseChange A)

variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]

/- English proof (translation)
Use extensionality with `g x`. Simplify using `[cmp]`.
-/
theorem cmp_natural (f : M →ₗ[O] N) :
    cmp A M ∘ₗ f.dualMap.baseChange A = (f.baseChange A).dualMap ∘ₗ cmp A N := by
  ext g x
  simp [cmp]

/- English proof (translation)
The claim follows from `LinearMap.congr_fun (cmp_natural A f) x`.
-/
theorem cmp_natural_apply (f : M →ₗ[O] N) (x : A ⊗[O] Module.Dual O N) :
    cmp A M (f.dualMap.baseChange A x) = (f.baseChange A).dualMap (cmp A N x) :=
  LinearMap.congr_fun (cmp_natural A f) x

/- English proof (translation)
Establish `h` using `(TensorProduct.isBaseChange O M A)`. Establish `: cmp A M (O` using `O) = h.toDualBaseChange.toLinearMap := by`. Use extensionality with `g x`. Use `h.toDualBaseChange_tmul 1 g x` as an intermediate fact. Simplify using `only [TensorProduct.mk_apply] at this`.

Simplify using `[cmp, this, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[this]`. Conclude with `h.toDualBaseChange.bijective`.
-/
theorem cmp_bijective_of_free [Module.Free O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  have h := (TensorProduct.isBaseChange O M A)
  have : cmp A M (O := O) = h.toDualBaseChange.toLinearMap := by
    ext g x
    have := h.toDualBaseChange_tmul 1 g x
    simp only [TensorProduct.mk_apply] at this
    simp [cmp, this, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact h.toDualBaseChange.bijective

/- English proof (translation)
Take `⟨n, p, i, -, -, hpi⟩` from `Module.Finite.exists_comp_eq_id_of_projective O M`. Establish `hF` using `cmp_bijective_of_free A (O := O) (M := Fin n → O)`. Establish `h1 : ∀ x, i.dualMap.baseChange A (p.dualMap.baseChange A x) = x`. Introduce `x`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi]`.

Simplify using `[LinearMap.dualMap_id]`. Establish `h2 : ∀ y, (i.baseChange A).dualMap ((p.baseChange A).dualMap y) = y`. Introduce `y`. Rewrite using `[← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi]`. Simplify using `[LinearMap.dualMap_id]`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Rewrite using `[← h1 x, ← h1 y]`. Use `congr 1`. Apply `hF.1` to reduce the goal to its premises.

Rewrite using `[cmp_natural_apply, cmp_natural_apply, hxy]`. Introduce `y`. Take `⟨z, hz⟩` from `hF.2 ((p.baseChange A).dualMap y)`. Conclude with `⟨i.dualMap.baseChange A z, by rw [cmp_natural_apply, hz, h2]⟩`.
-/
theorem cmp_bijective [Module.Projective O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
  have hF := cmp_bijective_of_free A (O := O) (M := Fin n → O)
  have h1 : ∀ x, i.dualMap.baseChange A (p.dualMap.baseChange A x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi]
    simp [LinearMap.dualMap_id]
  have h2 : ∀ y, (i.baseChange A).dualMap ((p.baseChange A).dualMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi]
    simp [LinearMap.dualMap_id]
  constructor
  · intro x y hxy
    rw [← h1 x, ← h1 y]
    congr 1
    apply hF.1
    rw [cmp_natural_apply, cmp_natural_apply, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hF.2 ((p.baseChange A).dualMap y)
    exact ⟨i.dualMap.baseChange A z, by rw [cmp_natural_apply, hz, h2]⟩

end

/- English proof (translation)
Introduce `O M N κ _ _ _ _ _ _ _ _ _ _ _ f`. Set `eM` to `LinearEquiv.ofBijective (cmp κ M (O := O)) (cmp_bijective κ)`. Use `⟨by rw [eM.finrank_eq, Subspace.dual_finrank_eq], ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.finrank_range_dualMap_eq_finrank_range (f.baseChange κ), ← LinearEquiv.finrank_map_eq eM]`. Establish `: (LinearMap.range (f.dualMap.baseChange κ)).map (eM : _ →ₗ[κ] _) = LinearMap.range (f.baseChange κ).dualMap`.

Rewrite using `[← LinearMap.range_comp]`. Express the relevant statement in the definitionally equal form `LinearMap.range (cmp κ M ∘ₗ f.dualMap.baseChange κ) = _`. Rewrite using `[cmp_natural, LinearMap.range_comp_of_range_eq_top]`. Conclude with `LinearMap.range_eq_top.2 (cmp_bijective κ).2`. Rewrite using `[this]`.
-/
theorem finrank_dual_and_range_dualMap_baseChange :
    ∀ (O M N κ : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
      [Field κ] [Algebra O κ] (f : M →ₗ[O] N),
      Module.finrank κ (TensorProduct O κ (Module.Dual O M)) =
          Module.finrank κ (TensorProduct O κ M) ∧
        Module.finrank κ (LinearMap.range (f.dualMap.baseChange κ)) =
          Module.finrank κ (LinearMap.range (f.baseChange κ)) := by
  intro O M N κ _ _ _ _ _ _ _ _ _ _ _ f
  let eM := LinearEquiv.ofBijective (cmp κ M (O := O)) (cmp_bijective κ)
  refine ⟨by rw [eM.finrank_eq, Subspace.dual_finrank_eq], ?_⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (f.baseChange κ),
    ← LinearEquiv.finrank_map_eq eM]
  have : (LinearMap.range (f.dualMap.baseChange κ)).map (eM : _ →ₗ[κ] _) =
      LinearMap.range (f.baseChange κ).dualMap := by
    rw [← LinearMap.range_comp]
    change LinearMap.range (cmp κ M ∘ₗ f.dualMap.baseChange κ) = _
    rw [cmp_natural, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (cmp_bijective κ).2
  rw [this]

end GlobalTheory.DualFibreRank
