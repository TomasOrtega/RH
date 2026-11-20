import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntCols

variable {k : Type} [Field k]

/- English proof (translation)
Establish `h1 : (Matrix.fromCols C D).rank = Module.finrank k (LinearMap.range (Matrix.fromCols C D)ᵀ.mulVecLin)`. Rewrite using `[← Matrix.rank_transpose]`. Both sides reduce to the same expression. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker (Matrix.fromCols C D)ᵀ.mulVecLin`. Rewrite `h2` using `[← h1, Module.finrank_fin_fun]`.

Prove the components needed by the constructor for the conclusion. Introduce `h y hC hD`. Establish `h3 : Module.finrank k (LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin) = 0` using `by omega`. Establish `h4` using `Submodule.finrank_eq_zero.mp h3`. Establish `h5 : y ∈ LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin`.

Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols, hC, hD]`. Apply the tactic sequence `ext i; cases i <;> simp`. Rewrite `h5` using `[h4]`. Simplify using `using h5`. Introduce `h`.

Establish `h3 : LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `y hy`. Rewrite `hy` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols]`. Use `h y ?_ ?_` and prove the remaining obligations.

Use extensionality with `i`. Simplify using `using congrFun hy (Sum.inl i)`. Use extensionality with `i`. Simplify using `using congrFun hy (Sum.inr i)`. Rewrite `h2` using `[h3]`.

Simplify using `using h2`.
-/
theorem rank_fromCols_eq_iff {n : ℕ} (C D : Matrix (Fin n) (Fin n) k) :
    (Matrix.fromCols C D).rank = n ↔ ∀ y : Fin n → k, y ᵥ* C = 0 → y ᵥ* D = 0 → y = 0 := by
  have h1 : (Matrix.fromCols C D).rank = Module.finrank k (LinearMap.range (Matrix.fromCols C D)ᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose]; rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.fromCols C D)ᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  constructor
  · intro h y hC hD
    have h3 : Module.finrank k (LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin) = 0 := by omega
    have h4 := Submodule.finrank_eq_zero.mp h3
    have h5 : y ∈ LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols, hC, hD]
      ext i; cases i <;> simp
    rw [h4] at h5
    simpa using h5
  · intro h
    have h3 : LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols] at hy
      refine h y ?_ ?_
      · ext i; simpa using congrFun hy (Sum.inl i)
      · ext i; simpa using congrFun hy (Sum.inr i)
    rw [h3] at h2
    simpa using h2

/- English proof (translation)
Establish `h1 : D.rank = Module.finrank k (LinearMap.range Dᵀ.mulVecLin)`. Rewrite using `[← Matrix.rank_transpose]`. Both sides reduce to the same expression. Establish `h2` using `LinearMap.finrank_range_add_finrank_ker Dᵀ.mulVecLin`. Rewrite `h2` using `[← h1, Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_leftKer {n : ℕ} (D : Matrix (Fin n) (Fin n) k) :
    Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - D.rank := by
  have h1 : D.rank = Module.finrank k (LinearMap.range Dᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose]; rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker Dᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `h1` using `Fintype.linearIndependent_iff.mp h (fun i => b.repr y i) (by`. Use `congrArg g (b.sum_repr y)` as an intermediate fact. Rewrite `this` using `[map_sum, hy]`.

Simplify using `using this)`. Rewrite using `[← b.sum_repr y]`. Simplify using `[h1]`. Introduce `h`. Establish `: LinearMap.ker g = ⊥`.

Rewrite using `[Submodule.eq_bot_iff]`. Introduce `y hy`. Conclude with `h y hy`. Conclude with `b.linearIndependent.map' g this`.
-/
theorem li_iff {V Z ι : Type} [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z] [Fintype ι]
    (b : Module.Basis ι k Z) (g : Z →ₗ[k] V) :
    LinearIndependent k (fun i => g (b i)) ↔ ∀ y, g y = 0 → y = 0 := by
  constructor
  · intro h y hy
    have h1 := Fintype.linearIndependent_iff.mp h (fun i => b.repr y i) (by
      have := congrArg g (b.sum_repr y)
      rw [map_sum, hy] at this
      simpa using this)
    rw [← b.sum_repr y]
    simp [h1]
  · intro h
    have : LinearMap.ker g = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro y hy; exact h y hy
    exact b.linearIndependent.map' g this

/- English proof (translation)
Introduce `k _ _ n ρ D hD`. Establish `hρ : ρ ≤ n` using `by simpa [hD] using D.rank_le_width`. Establish `hZ : Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - ρ` using `by rw [finrank_leftKer, hD]`. Take `⟨W, hW⟩` from `Submodule.exists_isCompl (LinearMap.ker Dᵀ.mulVecLin)`. Establish `hWf : Module.finrank k W = ρ`.

Use `Submodule.finrank_add_eq_of_isCompl hW` as an intermediate fact. Rewrite `this` using `[hZ, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Set `bZ` to `Module.finBasisOfFinrankEq k _ hZ`. Set `bW` to `Module.finBasisOfFinrankEq k _ hWf`.

Set `bV` to `(bZ.prod bW).map (Submodule.prodEquivOfIsCompl _ W hW)`. Set `E : Matrix (Fin n) (Fin n) k ≃ (Fin (n - ρ) → Fin n → k) × (Fin ρ → Fin n → k)` to `((Matrix.transposeLinearEquiv (Fin n) (Fin n) k k).toEquiv.trans (Matrix.toLin' (R := k) (m := Fin n) (n := Fin n)).toEquiv).trans ((bV.constr k).symm.toEquiv.trans (Equiv.sumArrowEquivProdArrow _ _ _))`. Establish `hE : ∀ C i, (E C).1 i = (bZ i : Fin n → k) ᵥ* C`. Introduce `C i`. Simplify using `[E, bV, Equiv.sumArrowEquivProdArrow, Module.Basis.constr, Matrix.mulVec_transpose]`.

Establish `hp : ∀ C, (Matrix.fromCols C D).rank = n ↔ LinearIndependent k (E C).1`. Introduce `C`. Establish `h1 : (E C).1 = fun i => (Cᵀ.mulVecLin ∘ₗ (LinearMap.ker Dᵀ.mulVecLin).subtype) (bZ i)`. Use function extensionality and compare the values at `i`. Rewrite using `[hE]`.

Simplify using `[Matrix.mulVec_transpose]`. Rewrite using `[h1, li_iff, rank_fromCols_eq_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `h2 : (y : Fin n → k) ᵥ* D = 0`.

Use `y.2` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]`. Then use the resulting hypothesis. Establish `h3 : (y : Fin n → k) ᵥ* C = 0` using `by simpa [Matrix.mulVec_transpose] using hy`. Conclude with `Subtype.ext (h _ h3 h2)`. Introduce `h y hC hD'`.

Establish `hy : y ∈ LinearMap.ker Dᵀ.mulVecLin`. Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]` and apply the resulting hypothesis. Use `h ⟨y, hy⟩ (by simpa [Matrix.mulVec_transpose] using hC)` as an intermediate fact. Simplify using `using congrArg Subtype.val this`. Rewrite using `[Nat.card_congr ((Equiv.subtypeEquiv (q := fun x => LinearIndependent k x.1) E hp).trans (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun s : Fin (n - ρ) → Fin n → k => LinearIndependent k s))), Nat.card_prod, card_linearIndependent (K := k) (V := Fin n → k) (by rw [Module.finrank …`.

Use `congr 1`. Simplify using `[Nat.card_fun, pow_mul]`.
-/
theorem card_completions : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  intro k _ _ n ρ D hD
  have hρ : ρ ≤ n := by simpa [hD] using D.rank_le_width
  have hZ : Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - ρ := by rw [finrank_leftKer, hD]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker Dᵀ.mulVecLin)
  have hWf : Module.finrank k W = ρ := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [hZ, Module.finrank_fin_fun] at this
    omega
  let bZ := Module.finBasisOfFinrankEq k _ hZ
  let bW := Module.finBasisOfFinrankEq k _ hWf
  let bV := (bZ.prod bW).map (Submodule.prodEquivOfIsCompl _ W hW)
  let E : Matrix (Fin n) (Fin n) k ≃ (Fin (n - ρ) → Fin n → k) × (Fin ρ → Fin n → k) :=
    ((Matrix.transposeLinearEquiv (Fin n) (Fin n) k k).toEquiv.trans
      (Matrix.toLin' (R := k) (m := Fin n) (n := Fin n)).toEquiv).trans
      ((bV.constr k).symm.toEquiv.trans (Equiv.sumArrowEquivProdArrow _ _ _))
  have hE : ∀ C i, (E C).1 i = (bZ i : Fin n → k) ᵥ* C := by
    intro C i
    simp [E, bV, Equiv.sumArrowEquivProdArrow, Module.Basis.constr, Matrix.mulVec_transpose]
  have hp : ∀ C, (Matrix.fromCols C D).rank = n ↔ LinearIndependent k (E C).1 := by
    intro C
    have h1 : (E C).1 = fun i => (Cᵀ.mulVecLin ∘ₗ (LinearMap.ker Dᵀ.mulVecLin).subtype) (bZ i) := by
      funext i
      rw [hE]
      simp [Matrix.mulVec_transpose]
    rw [h1, li_iff, rank_fromCols_eq_iff]
    constructor
    · intro h y hy
      have h2 : (y : Fin n → k) ᵥ* D = 0 := by
        have := y.2
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at this
      have h3 : (y : Fin n → k) ᵥ* C = 0 := by simpa [Matrix.mulVec_transpose] using hy
      exact Subtype.ext (h _ h3 h2)
    · intro h y hC hD'
      have hy : y ∈ LinearMap.ker Dᵀ.mulVecLin := by
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
      have := h ⟨y, hy⟩ (by simpa [Matrix.mulVec_transpose] using hC)
      simpa using congrArg Subtype.val this
  rw [Nat.card_congr ((Equiv.subtypeEquiv (q := fun x => LinearIndependent k x.1) E hp).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun s : Fin (n - ρ) → Fin n → k => LinearIndependent k s))), Nat.card_prod,
    card_linearIndependent (K := k) (V := Fin n → k) (by rw [Module.finrank_fin_fun]; omega), Module.finrank_fin_fun,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j), mul_comm]
  congr 1
  simp [Nat.card_fun, pow_mul]

end GlobalTheory.CompanionTheory.Jp.CntCols
