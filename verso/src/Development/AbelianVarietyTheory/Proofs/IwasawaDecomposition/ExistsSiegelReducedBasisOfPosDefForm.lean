import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsHermiteReducedLatticeBasis

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped MatrixOrder

namespace GlobalTheory.RedTh.RedBasis

/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem sum_sum_eq_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * G i j = c ⬝ᵥ (G *ᵥ c) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `hT : G.PosSemidef`. Rewrite using `[posSemidef_iff_dotProduct_mulVec]`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Use `show Gᴴ = G`. Rewrite using `[conjTranspose_eq_transpose_of_trivial, hs]`.

Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Use `(hp x hx).le` as an intermediate fact. Rewrite `this` using `[sum_sum_eq_dotProduct]`. Simplify using `using this`.

Establish `h0 : 0 ≤ G` using `Matrix.nonneg_iff_posSemidef.mpr hT`. Establish `hsq : (CFC.sqrt G).PosSemidef` using `Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)`. Establish `hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G`. Use `hsq.1` as an intermediate fact. Rewrite `this` using `[IsHermitian, conjTranspose_eq_transpose_of_trivial]`.

Conclude with `this`. Establish `hgG : (CFC.sqrt G)ᵀ * CFC.sqrt G = G`. Rewrite using `[hsym, CFC.sqrt_mul_sqrt_self G h0]`. Use `⟨CFC.sqrt G, fun hd => ?_, hgG⟩` and prove the remaining obligations. Take `⟨v, hv, hgv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hd`.

Establish `h` using `hp v hv`. Rewrite `h` using `[sum_sum_eq_dotProduct, ← hgG, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hgv]`. Simplify using `at h`.
-/
theorem exists_transpose_mul_self {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hs : Gᵀ = G)
    (hp : ∀ c : Fin n → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * G i j) :
    ∃ g : Matrix (Fin n) (Fin n) ℝ, g.det ≠ 0 ∧ gᵀ * g = G := by
  have hT : G.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · show Gᴴ = G
      rw [conjTranspose_eq_transpose_of_trivial, hs]
    · by_cases hx : x = 0
      · simp [hx]
      · have := (hp x hx).le
        rw [sum_sum_eq_dotProduct] at this
        simpa using this
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hT
  have hsq : (CFC.sqrt G).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hsym : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsq.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hgG : (CFC.sqrt G)ᵀ * CFC.sqrt G = G := by
    rw [hsym, CFC.sqrt_mul_sqrt_self G h0]
  refine ⟨CFC.sqrt G, fun hd => ?_, hgG⟩
  obtain ⟨v, hv, hgv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h := hp v hv
  rw [sum_sum_eq_dotProduct, ← hgG, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hgv] at h
  simp at h

/- English proof (translation)
Introduce `n Y _ b₀ B hs hB`. Set `G : Matrix (Fin n) (Fin n) ℝ` to `Matrix.of fun i j => B (b₀ i) (b₀ j)`. Take `⟨g, hg, hgG⟩` from `exists_transpose_mul_self G (by ext i j; simp [G, hs]) (by simpa [G] using (isPosDef_iff_basis b₀ B).1 hB)`. Take `⟨γ, k, a, m, hγ, hk, ha, h1, h0, hup, hstep, hdec⟩` from `GlobalTheory.ClassFin.HermiteReduction.exists_reduced n g hg`. Apply the tactic sequence `have hu : IsUnit γ.det := by rcases hγ with h | h <;> rw [h] <;> simp`.

Set `e : Y ≃ₗ[ℤ] Y` to `Matrix.toLinearEquiv b₀ γ hu`. Establish `hbe : ∀ j, b₀.map e j = ∑ i, γ i j • b₀ i` using `fun j => by`. Simplify using `[e, Matrix.toLinearEquiv_apply, Matrix.toLin_self]`. Establish `hM : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = gram (fun i => a i ^ 2) m`. Establish `e1 : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = (g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))`.

Rewrite using `[← hgG, transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Establish `e2 : (k * diagonal a * m)ᵀ * (k * diagonal a * m) = mᵀ * (diagonal a * (kᵀ * k) * diagonal a) * m`. Simplify using `only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]`. Rewrite using `[e1, hdec, e2, hk, Matrix.mul_one, diagonal_mul_diagonal, gram]`.

Simplify using `only [sq]`. Use `⟨b₀.map e, fun i => a i ^ 2, m, ⟨fun i => sq_nonneg _, fun p q hq => ?_, h1, h0, hup⟩, fun i => pow_pos (ha i) 2, fun i j => ?_⟩` and prove the remaining obligations. Establish `h2` using `hstep p q hq`. Establish `h3` using `ha p`. Establish `h4` using `ha q`.

Use `show a p ^ 2 ≤ 4 * a q ^ 2`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← hM, hbe, hbe]`. Simplify using `only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Matrix.mul_apply, transpose_apply, map_apply, G, of_apply, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem exists_siegel_basis : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] (b₀ : Module.Basis (Fin n) ℤ Y)
    (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ), (∀ y z, B y z = B z y) → IsPosDef B → ∃ (b : Module.Basis (Fin n) ℤ Y)
    (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧ (∀ i, 0 < d i) ∧
    ∀ i j, B (b i) (b j) = gram d u i j := by
  intro n Y _ b₀ B hs hB
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => B (b₀ i) (b₀ j)
  obtain ⟨g, hg, hgG⟩ := exists_transpose_mul_self G (by ext i j; simp [G, hs])
    (by simpa [G] using (isPosDef_iff_basis b₀ B).1 hB)
  obtain ⟨γ, k, a, m, hγ, hk, ha, h1, h0, hup, hstep, hdec⟩ :=
    GlobalTheory.ClassFin.HermiteReduction.exists_reduced n g hg
  have hu : IsUnit γ.det := by rcases hγ with h | h <;> rw [h] <;> simp
  let e : Y ≃ₗ[ℤ] Y := Matrix.toLinearEquiv b₀ γ hu
  have hbe : ∀ j, b₀.map e j = ∑ i, γ i j • b₀ i := fun j => by
    simp [e, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hM : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) = gram (fun i => a i ^ 2) m := by
    have e1 : (γ.map (Int.cast : ℤ → ℝ))ᵀ * G * γ.map (Int.cast : ℤ → ℝ) =
        (g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ)) := by
      rw [← hgG, transpose_mul]; simp only [Matrix.mul_assoc]
    have e2 : (k * diagonal a * m)ᵀ * (k * diagonal a * m) = mᵀ * (diagonal a * (kᵀ * k) * diagonal a) * m := by
      simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hdec, e2, hk, Matrix.mul_one, diagonal_mul_diagonal, gram]
    simp only [sq]
  refine ⟨b₀.map e, fun i => a i ^ 2, m, ⟨fun i => sq_nonneg _, fun p q hq => ?_, h1, h0, hup⟩,
    fun i => pow_pos (ha i) 2, fun i j => ?_⟩
  · have h2 := hstep p q hq
    have h3 := ha p
    have h4 := ha q
    show a p ^ 2 ≤ 4 * a q ^ 2
    nlinarith
  · rw [← hM, hbe, hbe]
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Matrix.mul_apply,
      transpose_apply, map_apply, G, of_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.RedTh.RedBasis
