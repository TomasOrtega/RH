import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

/- English proof (translation)
Introduce `L _ _ _ n a ι _ _ b P hA v hv w`. Use `set x : a.W := b.equivFun.symm v with hx`. Establish `hxv : b.repr x = v`. Rewrite using `[← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]`. Establish `hx0 : x ≠ 0`.

Introduce `h`. Apply `hv` to reduce the goal to its premises. Rewrite using `[← hxv, h, map_zero]`. Both sides reduce to the same expression. Set `S0 : Submodule ℂ a.W` to `Submodule.span ℂ (Set.range fun γ : GQ L n => a.ρ γ x)`.

Establish `hinv : ∀ (g : GQ L n) (y : a.W), y ∈ S0 → a.ρ g y ∈ S0`. Introduce `g y hy`. Establish `hle : S0 ≤ S0.comap (a.ρ g)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨γ, rfl⟩`.

Use `show a.ρ g (a.ρ γ x) ∈ S0`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `Submodule.subset_span ⟨g * γ, rfl⟩`. Conclude with `hle hy`. Set `S : Subrepresentation a.ρ` to `⟨S0, hinv⟩`.

Establish `hxS : x ∈ S0` using `Submodule.subset_span ⟨1, by simp⟩`. Establish `hS0 : S0 = ⊤` using `by haveI := a.irr`. Break down `IsSimpleOrder.eq_bot_or_eq_top S with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hx0` to reduce the goal to its premises.

Establish `h2 : S.toSubmodule = (⊥ : Subrepresentation a.ρ).toSubmodule` using `congrArg _ h`. Establish `h3 : x ∈ (⊥ : Subrepresentation a.ρ).toSubmodule` using `h2 ▸ hxS`. Express the relevant statement in the definitionally equal form `x ∈ (⊥ : Submodule ℂ a.W) at h3`. Conclude with `(Submodule.mem_bot ℂ).1 h3`. Establish `h2 : S.toSubmodule = (⊤ : Subrepresentation a.ρ).toSubmodule` using `congrArg _ h`.

Conclude with `h2`. Establish `hw : w = b.equivFun.toLinearMap (b.equivFun.symm w)` using `(b.equivFun.apply_symm_apply w).symm`. Establish `hmem : b.equivFun.symm w ∈ S0` using `by rw [hS0]; trivial`. Rewrite using `[hw]`. Establish `hmap : Submodule.map b.equivFun.toLinearMap S0 ≤ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v}`.

Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨γ, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Establish `hγ : (γ : GA L n) ∈ ((GQ0 L n).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n)` using `γ.2`. Rewrite `hγ` using `[Subgroup.mem_subgroupOf, Subgroup.mem_map]`.

Take `⟨γ₀, hγ₀, he⟩` from `hγ`. Use `⟨γ₀, hγ₀, ?_⟩` and prove the remaining obligations. Establish `hE : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)`. Rewrite using `[← he]`. Both sides reduce to the same expression.

Establish `hM` using `hA γ γ₀ hE`. Use `show b.equivFun (a.ρ γ x) = _`. Rewrite using `[Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hxv, hM]`. Both sides reduce to the same expression. Conclude with `hmap (Submodule.mem_map_of_mem hmem)`.
-/
theorem span_ratPt_orbit : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  intro L _ _ _ n a ι _ _ b P hA v hv w
  classical
  set x : a.W := b.equivFun.symm v with hx
  have hxv : b.repr x = v := by
    rw [← Module.Basis.equivFun_apply, hx, LinearEquiv.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    intro h
    apply hv
    rw [← hxv, h, map_zero]
    rfl
  let S0 : Submodule ℂ a.W := Submodule.span ℂ (Set.range fun γ : GQ L n => a.ρ γ x)
  have hinv : ∀ (g : GQ L n) (y : a.W), y ∈ S0 → a.ρ g y ∈ S0 := by
    intro g y hy
    have hle : S0 ≤ S0.comap (a.ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      show a.ρ g (a.ρ γ x) ∈ S0
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * γ, rfl⟩
    exact hle hy
  let S : Subrepresentation a.ρ := ⟨S0, hinv⟩
  have hxS : x ∈ S0 := Submodule.subset_span ⟨1, by simp⟩
  have hS0 : S0 = ⊤ := by
    haveI := a.irr
    rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hx0
      have h2 : S.toSubmodule = (⊥ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      have h3 : x ∈ (⊥ : Subrepresentation a.ρ).toSubmodule := h2 ▸ hxS
      change x ∈ (⊥ : Submodule ℂ a.W) at h3
      exact (Submodule.mem_bot ℂ).1 h3
    · have h2 : S.toSubmodule = (⊤ : Subrepresentation a.ρ).toSubmodule := congrArg _ h
      exact h2
  have hw : w = b.equivFun.toLinearMap (b.equivFun.symm w) := (b.equivFun.apply_symm_apply w).symm
  have hmem : b.equivFun.symm w ∈ S0 := by rw [hS0]; trivial
  rw [hw]
  have hmap : Submodule.map b.equivFun.toLinearMap S0 ≤ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
    rw [Submodule.map_span_le]
    rintro _ ⟨γ, rfl⟩
    apply Submodule.subset_span
    have hγ : (γ : GA L n) ∈ ((GQ0 L n).map (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))).subgroupOf (GA L n) := γ.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
    obtain ⟨γ₀, hγ₀, he⟩ := hγ
    refine ⟨γ₀, hγ₀, ?_⟩
    have hE : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      rw [← he]; rfl
    have hM := hA γ γ₀ hE
    show b.equivFun (a.ρ γ x) = _
    rw [Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b, hxv, hM]
    rfl
  exact hmap (Submodule.mem_map_of_mem hmem)

end GlobalTheory.AlgWtHW
