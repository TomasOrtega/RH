import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ r n β U`. Establish `hrn : r ≤ n` using `by have := U.2; omega`. Set `b` to `Module.finBasisOfFinrankEq k _ (finrank_quot U)`. Establish `hU : Module.finrank k U.1 = n - r` using `by have := U.2; omega`. Set `bU` to `Module.finBasisOfFinrankEq k U.1 hU`.

Take `⟨lam, hlam⟩` from `LinearMap.exists_extend (bU.equivFun.toLinearMap)`. Set `φ : (Fin n → k) →ₗ[k] (Fin n → k)` to `LinearMap.pi fun j => if h : j.val < r then (LinearMap.proj (⟨j.val, h⟩ : Fin r)) ∘ₗ b.equivFun.toLinearMap ∘ₗ U.1.mkQ else (LinearMap.proj (⟨j.val - r, by have := j.2; omega⟩ : Fin (n - r))) ∘ₗ lam`. Establish `hφ1 : ∀ v (i : Fin r), φ v ⟨i.val, by omega⟩ = b.repr (U.1.mkQ v) i`. Introduce `v i`. Simplify using `[φ, i.2]`.

Establish `hφ2 : ∀ v (i : Fin (n - r)), φ v ⟨r + i.val, by omega⟩ = lam v i`. Introduce `v i`. Simplify using `[φ]`. Establish `hφ : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `v hv`. Establish `h1 : U.1.mkQ v = 0`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Use `hφ1 v i` as an intermediate fact.

Rewrite `this` using `[hv]`. Simplify using `using this.symm`. Establish `hvU : v ∈ U.1` using `by simpa using h1`. Establish `h2 : bU.equivFun ⟨v, hvU⟩ = 0`. Establish `e : lam v = bU.equivFun ⟨v, hvU⟩`.

Use `LinearMap.congr_fun hlam ⟨v, hvU⟩` as an intermediate fact. Simplify using `using this`. Rewrite using `[← e]`. Use extensionality with `i`. Use `hφ2 v i` as an intermediate fact.

Rewrite `this` using `[hv]`. Simplify using `using this.symm`. Establish `: (⟨v, hvU⟩ : U.1) = 0` using `bU.equivFun.injective (by rw [h2, map_zero])`. Simplify using `using congrArg Subtype.val this`. Set `ψ` to `LinearEquiv.ofInjectiveEndo φ hφ`.

Set `A : Matrix (Fin n) (Fin n) k` to `(LinearMap.toMatrix' φ)ᵀ`. Set `B : Matrix (Fin n) (Fin n) k` to `(LinearMap.toMatrix' ψ.symm.toLinearMap)ᵀ`. Establish `hAB : A * B = 1`. Establish `hc : ψ.symm.toLinearMap ∘ₗ φ = LinearMap.id`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Use `show ψ.symm (ψ v) = v`. Conclude with `ψ.symm_apply_apply v`. Simplify using `only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]`. Establish `hBA : B * A = 1`. Establish `hc : φ ∘ₗ ψ.symm.toLinearMap = LinearMap.id`.

Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use `show ψ (ψ.symm v) = v`. Conclude with `ψ.apply_symm_apply v`. Simplify using `only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]`. Set `g : GL (Fin n) k` to `⟨A, B, hAB, hBA⟩`.

Establish `hb : β.form U b ≠ 0` using `fun h0 => β.ne U (by rw [(β.form U).eq_smul_basis_det b, h0, zero_smul])`. Use `⟨g, Units.mk0 _ hb, fun y => ?_⟩` and prove the remaining obligations. Establish `key : ∀ i j, (y * A) i j = φ (y.row i) j`. Introduce `i j`. Rewrite using `[← congrFun (LinearMap.toMatrix'_mulVec φ (y.row i)) j]`.

Simplify using `[A, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.row]`. Establish `ht : topL r (y * (g : Matrix (Fin n) (Fin n) k)) = (b.toMatrix fun i => U.1.mkQ (y.row i))ᵀ`. Use extensionality with `i j`. Establish `hj : j.val < n` using `by omega`. Establish `e1 : topL r (y * (g : Matrix (Fin n) (Fin n) k)) i j = (y * A) i ⟨j.val, hj⟩`.

Simplify using `[topL, hj, g]`. Rewrite using `[e1, key, hφ1 (y.row i) j, transpose_apply, Module.Basis.toMatrix_apply]`. Rewrite using `[ht, det_transpose, ← Module.Basis.det_apply, dU]`. Use `conv_lhs => rw [(β.form U).eq_smul_basis_det b]`. Both sides reduce to the same expression.
-/
theorem dU_eq_const_mul_det_topL_translate :
  ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  intro k _ r n β U
  have hrn : r ≤ n := by have := U.2; omega
  let b := Module.finBasisOfFinrankEq k _ (finrank_quot U)
  have hU : Module.finrank k U.1 = n - r := by have := U.2; omega
  let bU := Module.finBasisOfFinrankEq k U.1 hU
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend (bU.equivFun.toLinearMap)
  let φ : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.pi fun j =>
    if h : j.val < r then (LinearMap.proj (⟨j.val, h⟩ : Fin r)) ∘ₗ b.equivFun.toLinearMap ∘ₗ U.1.mkQ
    else (LinearMap.proj (⟨j.val - r, by have := j.2; omega⟩ : Fin (n - r))) ∘ₗ lam
  have hφ1 : ∀ v (i : Fin r), φ v ⟨i.val, by omega⟩ = b.repr (U.1.mkQ v) i := by
    intro v i
    simp [φ, i.2]
  have hφ2 : ∀ v (i : Fin (n - r)), φ v ⟨r + i.val, by omega⟩ = lam v i := by
    intro v i
    simp [φ]
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : U.1.mkQ v = 0 := by
      apply b.repr.injective
      ext i
      have := hφ1 v i
      rw [hv] at this
      simpa using this.symm
    have hvU : v ∈ U.1 := by simpa using h1
    have h2 : bU.equivFun ⟨v, hvU⟩ = 0 := by
      have e : lam v = bU.equivFun ⟨v, hvU⟩ := by
        have := LinearMap.congr_fun hlam ⟨v, hvU⟩
        simpa using this
      rw [← e]
      ext i
      have := hφ2 v i
      rw [hv] at this
      simpa using this.symm
    have : (⟨v, hvU⟩ : U.1) = 0 := bU.equivFun.injective (by rw [h2, map_zero])
    simpa using congrArg Subtype.val this

  let ψ := LinearEquiv.ofInjectiveEndo φ hφ
  let A : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' φ)ᵀ
  let B : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' ψ.symm.toLinearMap)ᵀ
  have hAB : A * B = 1 := by
    have hc : ψ.symm.toLinearMap ∘ₗ φ = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ.symm (ψ v) = v
      exact ψ.symm_apply_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  have hBA : B * A = 1 := by
    have hc : φ ∘ₗ ψ.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ (ψ.symm v) = v
      exact ψ.apply_symm_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩
  have hb : β.form U b ≠ 0 := fun h0 => β.ne U (by rw [(β.form U).eq_smul_basis_det b, h0, zero_smul])
  refine ⟨g, Units.mk0 _ hb, fun y => ?_⟩
  have key : ∀ i j, (y * A) i j = φ (y.row i) j := by
    intro i j
    rw [← congrFun (LinearMap.toMatrix'_mulVec φ (y.row i)) j]
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.row]
  have ht : topL r (y * (g : Matrix (Fin n) (Fin n) k)) = (b.toMatrix fun i => U.1.mkQ (y.row i))ᵀ := by
    ext i j
    have hj : j.val < n := by omega
    have e1 : topL r (y * (g : Matrix (Fin n) (Fin n) k)) i j = (y * A) i ⟨j.val, hj⟩ := by
      simp [topL, hj, g]
    rw [e1, key, hφ1 (y.row i) j, transpose_apply, Module.Basis.toMatrix_apply]
  rw [ht, det_transpose, ← Module.Basis.det_apply, dU]
  conv_lhs => rw [(β.form U).eq_smul_basis_det b]
  rfl

end GlobalTheory
