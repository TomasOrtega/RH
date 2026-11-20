import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ _ A _ _ _ B _ _ φ ρ hspan hdim`. Set `b` to `Module.Free.chooseBasis ℤ O`. Set `v : Module.Free.ChooseBasisIndex ℤ O → A` to `fun i => φ (b i)`. Establish `hle : ⊤ ≤ Submodule.span ℂ (Set.range v)`. Rewrite using `[← hspan]`.

Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : x = ∑ i, b.repr x i • b i` using `(b.sum_repr x).symm`. Rewrite using `[hx, map_sum]`. Apply `Submodule.sum_mem` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℂ A`. Rewrite using `[hdim, Module.finrank_eq_card_chooseBasisIndex]`.

Set `bA` to `basisOfTopLeSpanOfCardEqFinrank v hle hcard`. Establish `hbA : ∀ i, bA i = φ (b i)` using `fun i => by`. Simplify using `only [bA, coe_basisOfTopLeSpanOfCardEqFinrank, v]`. Set `L : A →ₗ[ℂ] B` to `bA.constr ℂ (fun i => ρ (b i))`. Establish `hLb : ∀ i, L (φ (b i)) = ρ (b i)`.

Introduce `i`. Rewrite using `[← hbA]`. Conclude with `bA.constr_basis ℂ _ i`. Establish `hLφ : ∀ x, L (φ x) = ρ x`. Establish `h : (L.restrictScalars ℤ).comp φ.toAddMonoidHom.toIntLinearMap = ρ.toAddMonoidHom.toIntLinearMap` using `b.ext (fun i => hLb i)`.

Introduce `x`. Conclude with `LinearMap.congr_fun h x`. Establish `hmul : ∀ u w : A, L (u * w) = L u * L w`. Establish `h : (LinearMap.mul ℂ A).compr₂ L = (LinearMap.mul ℂ B).compl₁₂ L L`. Use `bA.ext (fun i => bA.ext (fun j => ?_))` and prove the remaining obligations.

Simplify using `only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', hbA]`. Rewrite using `[← map_mul, hLφ, hLφ, hLφ, map_mul]`. Introduce `u w`. Conclude with `LinearMap.congr_fun₂ h u w`. Establish `hone : L 1 = 1`.

Rewrite using `[← map_one φ, hLφ, map_one]`. Conclude with `⟨AlgHom.ofLinearMap L hone hmul, fun x => by`. Simplify using `only [AlgHom.ofLinearMap_apply]`. Conclude with `hLφ x⟩`.
-/
theorem ringHom_extends_algHom_of_span_of_finrank_eq :
    ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A]
      [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B),
      Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O →
      ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  intro O _ _ _ A _ _ _ B _ _ φ ρ hspan hdim
  classical
  let b := Module.Free.chooseBasis ℤ O
  let v : Module.Free.ChooseBasisIndex ℤ O → A := fun i => φ (b i)
  have hle : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    rw [hx, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℂ A := by
    rw [hdim, Module.finrank_eq_card_chooseBasisIndex]
  let bA := basisOfTopLeSpanOfCardEqFinrank v hle hcard
  have hbA : ∀ i, bA i = φ (b i) := fun i => by
    simp only [bA, coe_basisOfTopLeSpanOfCardEqFinrank, v]
  let L : A →ₗ[ℂ] B := bA.constr ℂ (fun i => ρ (b i))
  have hLb : ∀ i, L (φ (b i)) = ρ (b i) := by
    intro i
    rw [← hbA]
    exact bA.constr_basis ℂ _ i
  have hLφ : ∀ x, L (φ x) = ρ x := by
    have h : (L.restrictScalars ℤ).comp φ.toAddMonoidHom.toIntLinearMap
        = ρ.toAddMonoidHom.toIntLinearMap := b.ext (fun i => hLb i)
    intro x
    exact LinearMap.congr_fun h x
  have hmul : ∀ u w : A, L (u * w) = L u * L w := by
    have h : (LinearMap.mul ℂ A).compr₂ L = (LinearMap.mul ℂ B).compl₁₂ L L := by
      refine bA.ext (fun i => bA.ext (fun j => ?_))
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', hbA]
      rw [← map_mul, hLφ, hLφ, hLφ, map_mul]
    intro u w
    exact LinearMap.congr_fun₂ h u w
  have hone : L 1 = 1 := by
    rw [← map_one φ, hLφ, map_one]
  exact ⟨AlgHom.ofLinearMap L hone hmul, fun x => by
    simp only [AlgHom.ofLinearMap_apply]; exact hLφ x⟩

end GlobalTheory
