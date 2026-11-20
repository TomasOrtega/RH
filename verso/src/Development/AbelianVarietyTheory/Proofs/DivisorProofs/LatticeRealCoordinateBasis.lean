import Mathlib

open Module

/- English proof (translation)
Introduce `g Λ hd hs`. Use `haveI := hd`. Use `haveI : IsZLattice ℝ Λ := ⟨hs⟩`. Set `bZ0` to `Module.Free.chooseBasis ℤ Λ`. Set `bZ` to `bZ0.reindex (Fintype.equivFin _)`.

Set `bR` to `bZ.ofZLatticeBasis ℝ Λ`. Use `⟨_, fun i => bZ i, fun i => bR.coord i, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Establish `h` using `bR.sum_repr v`. Use `conv_rhs => rw [← h]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[bR]`. Introduce `φ x`. Establish `hx : ∀ i, bR.coord i (x : Fin g → ℂ) = ((bZ.repr x i : ℤ) : ℝ)`. Introduce `i`.

Simplify using `[bR, Module.Basis.ofZLatticeBasis_repr_apply]`. Repeatedly rewrite using `[hx]`. Use `conv_rhs => rw [← bZ.sum_repr x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Int.cast_smul_eq_zsmul, map_zsmul]`.
-/
theorem GlobalTheory.exists_zlattice_basis_realCoord_integral : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  intro g Λ hd hs
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let bZ0 := Module.Free.chooseBasis ℤ Λ
  let bZ := bZ0.reindex (Fintype.equivFin _)
  let bR := bZ.ofZLatticeBasis ℝ Λ
  refine ⟨_, fun i => bZ i, fun i => bR.coord i, ?_, ?_⟩
  · intro v
    have h := bR.sum_repr v
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [bR]
  · intro φ x
    have hx : ∀ i, bR.coord i (x : Fin g → ℂ) = ((bZ.repr x i : ℤ) : ℝ) := by
      intro i
      simp [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    simp_rw [hx]
    conv_rhs => rw [← bZ.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul, map_zsmul]
