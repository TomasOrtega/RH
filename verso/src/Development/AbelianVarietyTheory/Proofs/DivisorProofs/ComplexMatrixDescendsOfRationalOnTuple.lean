import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ σ T n D dQ nV ι Pq V r U t0 Ψc ht0 hι hP h`. Establish `hσ : Function.Injective σ` using `σ.injective`. Establish `hsurj : Function.Surjective (ι t0 * Pq t0).mulVec`. Introduce `y`. Take `⟨x, rfl⟩` from `hι.2 y`.

Take `⟨z, rfl⟩` from `hP x`. Conclude with `⟨z, (Matrix.mulVec_mulVec _ _ _).symm⟩`. Take `⟨R, hR⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj`. Take `⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ = ((r t0)⁻¹ • V t0) * R` from `⟨_, rfl⟩`. Establish `hΨc : Ψ.map σ = Ψc`.

Combine the equalities or inequalities in the displayed calculation. Establish `hall : ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t`. Introduce `t ht`. Apply `Matrix.map_injective hσ` to reduce the goal to its premises. Use `show (Ψ * ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ`.

Rewrite using `[Matrix.mul_assoc, Matrix.map_mul, hΨc, h t ht]`. Use `⟨⟨Ψ, hΨc, hall⟩, fun hinj hr => ?_⟩` and prove the remaining obligations. Establish `key : Ψ * ι t0 * Pq t0 = V t0`. Rewrite using `[hall t0 ht0, hr, inv_one, one_smul]`. Establish `hΨinj : Function.Injective Ψ.mulVec`.

Introduce `x y hxy`. Establish `hc : Ψc.mulVec (fun j => σ (x j)) = Ψc.mulVec (fun j => σ (y j))`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(Ψc).mulVec (σ ∘ x) i = (Ψc).mulVec (σ ∘ y) i`. Rewrite using `[← hΨc, ← RingHom.map_mulVec, ← RingHom.map_mulVec, hxy]`.

Use function extensionality and compare the values at `j`. Conclude with `hσ (congrFun (hinj hc) j)`. Use extensionality with `v`. Simplify using `only [LinearMap.mem_ker, Matrix.mulVecLin_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hv`. Rewrite `hv` using `[← key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `h1 : (ι t0).mulVec ((Pq t0).mulVec v) = 0` using `hΨinj (hv.trans (Matrix.mulVec_zero Ψ).symm)`. Conclude with `hι.1 (h1.trans (Matrix.mulVec_zero (ι t0)).symm)`. Introduce `hv`.

Rewrite using `[← key, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]`.
-/
theorem complex_matrix_descends_of_rational_on_tuple : ∀ {K : Type} [Field K] (σ : K →+* ℂ) {T : Type} (n D : ℕ) (dQ nV : T → ℕ) (ι : ∀ t, Matrix (Fin D) (Fin (dQ t)) K) (Pq : ∀ t, Matrix (Fin (dQ t)) (Fin (nV t)) K) (V : ∀ t, Matrix (Fin n) (Fin (nV t)) K) (r : T → K) (U : Set T) (t0 : T) (Ψc : Matrix (Fin n) (Fin D) ℂ), t0 ∈ U → Function.Bijective (ι t0).mulVec → Function.Surjective (Pq t0).mulVec → (∀ t ∈ U, Ψc * (ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ) → (∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ.map σ = Ψc ∧ ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t) ∧ (Function.Injective Ψc.mulVec → r t0 = 1 → LinearMap.ker (V t0).mulVecLin = LinearMap.ker (Pq t0).mulVecLin) := by
  intro K _ σ T n D dQ nV ι Pq V r U t0 Ψc ht0 hι hP h
  have hσ : Function.Injective σ := σ.injective
  have hsurj : Function.Surjective (ι t0 * Pq t0).mulVec := by
    intro y
    obtain ⟨x, rfl⟩ := hι.2 y
    obtain ⟨z, rfl⟩ := hP x
    exact ⟨z, (Matrix.mulVec_mulVec _ _ _).symm⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ = ((r t0)⁻¹ • V t0) * R := ⟨_, rfl⟩
  have hΨc : Ψ.map σ = Ψc := by
    calc Ψ.map σ = ((r t0)⁻¹ • V t0).map σ * R.map σ := by rw [hΨ, Matrix.map_mul]
      _ = Ψc * (ι t0 * Pq t0).map σ * R.map σ := by rw [h t0 ht0]
      _ = Ψc * ((ι t0 * Pq t0) * R).map σ := by rw [Matrix.map_mul (M := R), Matrix.mul_assoc]
      _ = Ψc := by rw [hR, Matrix.map_one σ σ.map_zero σ.map_one, Matrix.mul_one]
  have hall : ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t := by
    intro t ht
    apply Matrix.map_injective hσ
    show (Ψ * ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ
    rw [Matrix.mul_assoc, Matrix.map_mul, hΨc, h t ht]
  refine ⟨⟨Ψ, hΨc, hall⟩, fun hinj hr => ?_⟩
  have key : Ψ * ι t0 * Pq t0 = V t0 := by
    rw [hall t0 ht0, hr, inv_one, one_smul]
  have hΨinj : Function.Injective Ψ.mulVec := by
    intro x y hxy
    have hc : Ψc.mulVec (fun j => σ (x j)) = Ψc.mulVec (fun j => σ (y j)) := by
      funext i
      change (Ψc).mulVec (σ ∘ x) i = (Ψc).mulVec (σ ∘ y) i
      rw [← hΨc, ← RingHom.map_mulVec, ← RingHom.map_mulVec, hxy]
    funext j
    exact hσ (congrFun (hinj hc) j)
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    have h1 : (ι t0).mulVec ((Pq t0).mulVec v) = 0 := hΨinj (hv.trans (Matrix.mulVec_zero Ψ).symm)
    exact hι.1 (h1.trans (Matrix.mulVec_zero (ι t0)).symm)
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end GlobalTheory
