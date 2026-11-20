import Mathlib

namespace GlobalTheory

open WeierstrassCurve

/- English proof (translation)
Use `letI : Algebra F K := i.toAlgebra`. Set `φ : W.toAffine.Point →+ (W.map i).toAffine.Point` to `Affine.Point.map (W' := W.toAffine) (Algebra.ofId F K)`. Establish `hφ : Function.Injective φ` using `Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId F K)`. Establish `e : φ (Affine.Point.some x y h₀) = Affine.Point.some (i x) (i y) h` using `rfl`. Rewrite using `[← e, ← map_nsmul, map_eq_zero_iff φ hφ]`.
-/
theorem nsmul_some_map_eq_zero_iff {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (i : F →+* K) (W : WeierstrassCurve F) (x y : F) (N : ℕ)
    (h₀ : W.toAffine.Nonsingular x y) (h : (W.map i).toAffine.Nonsingular (i x) (i y)) :
    N • (Affine.Point.some (i x) (i y) h) = 0 ↔ N • (Affine.Point.some x y h₀) = 0 := by
  letI : Algebra F K := i.toAlgebra
  let φ : W.toAffine.Point →+ (W.map i).toAffine.Point :=
    Affine.Point.map (W' := W.toAffine) (Algebra.ofId F K)
  have hφ : Function.Injective φ := Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId F K)
  have e : φ (Affine.Point.some x y h₀) = Affine.Point.some (i x) (i y) h := rfl
  rw [← e, ← map_nsmul, map_eq_zero_iff φ hφ]

/- English proof (translation)
Introduce `F K K' _ _ _ _ _ i j A B x y N`. Set `W : WeierstrassCurve F` to `⟨0, 0, 0, A, B⟩`. Establish `ei : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K) = W.map i`. Apply the tactic sequence `ext <;> simp [W, WeierstrassCurve.map]`. Establish `ej : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K') = W.map j`.

Apply the tactic sequence `ext <;> simp [W, WeierstrassCurve.map]`. Rewrite using `[ei, ej]`. Introduce `h hN`. Establish `h₀ : W.toAffine.Nonsingular x y` using `(W.toAffine.map_nonsingular i.injective x y).mp h`. Establish `h' : (W.map j).toAffine.Nonsingular (j x) (j y)` using `(W.toAffine.map_nonsingular j.injective x y).mpr h₀`.

Conclude with `⟨h', (nsmul_some_map_eq_zero_iff j W x y N h₀ h').mpr ((nsmul_some_map_eq_zero_iff i W x y N h₀ h).mp hN)⟩`.
-/
theorem torsion_point_transport_embedding :
    ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [DecidableEq K] [DecidableEq K'] (i : F →+* K) (j : F →+* K') (A B x y : F) (N : ℕ) (h : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K).toAffine.Nonsingular (i x) (i y)), N • (WeierstrassCurve.Affine.Point.some (i x) (i y) h) = 0 → ∃ h' : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K').toAffine.Nonsingular (j x) (j y), N • (WeierstrassCurve.Affine.Point.some (j x) (j y) h') = 0 := by
  intro F K K' _ _ _ _ _ i j A B x y N
  classical
  let W : WeierstrassCurve F := ⟨0, 0, 0, A, B⟩
  have ei : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K) = W.map i := by
    ext <;> simp [W, WeierstrassCurve.map]
  have ej : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K') = W.map j := by
    ext <;> simp [W, WeierstrassCurve.map]
  rw [ei, ej]
  intro h hN
  have h₀ : W.toAffine.Nonsingular x y := (W.toAffine.map_nonsingular i.injective x y).mp h
  have h' : (W.map j).toAffine.Nonsingular (j x) (j y) :=
    (W.toAffine.map_nonsingular j.injective x y).mpr h₀
  exact ⟨h', (nsmul_some_map_eq_zero_iff j W x y N h₀ h').mpr
    ((nsmul_some_map_eq_zero_iff i W x y N h₀ h).mp hN)⟩

end GlobalTheory
