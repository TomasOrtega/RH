import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveEigenvectorOfSimilitudeUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyPsiEqMapMinpoly
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

/- English proof (translation)
Introduce `p _ G v hsig β hsh hR y₀ hdeg hsep z z' hz hz' hf hf'`. Take `⟨_, _, Z, hZ⟩` from `GlobalTheory.LKCx.herm_laws p G v β hsh hR`. Use `set g0 : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) with hg0`. Use `set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := (Z : Matrix (Fin G.n) (Fin G.n) ℂ) with hZm`. Use `set Zi : Matrix (Fin G.n) (Fin G.n) ℂ := ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) with hZi`.

Establish `hZiZ : Zi * Zm = 1` using `by rw [hZi, hZm, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hZZi : Zm * Zi = 1` using `by rw [hZi, hZm, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Use `set s : ℝ := ((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs`. Establish `hspos : 0 < s` using `by rw [hs]; exact_mod_cast y₀.2.2`. Establish `hsim0` using `GlobalTheory.LKCx.grp_similitude_herm p G v β y₀`.

Use `set g : Matrix (Fin G.n) (Fin G.n) ℂ := Zm * g0 * Zi with hg`. Establish `hsim : gᴴ * G.gram v * g = (s : ℂ) • G.gram v`. Establish `e1 : gᴴ * G.gram v * g = Ziᴴ * (g0ᴴ * (Zmᴴ * G.gram v * Zm) * g0) * Zi`. Rewrite using `[hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[e1, ← hZ, hsim0]`. Establish `e2 : Ziᴴ * ((((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β) * Zi = (s : ℂ) • ((Zm * Zi)ᴴ * G.gram v * (Zm * Zi))`. Rewrite using `[hZ, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[e2, hZZi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hcp : g.charpoly.Separable`. Establish `e : g = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * g0 * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ)` using `rfl`. Rewrite using `[e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Conclude with `GlobalTheory.LKMid.charpoly_psi_separable p G v _ hdeg hsep`.

Establish `hpos : ∀ w : Fin G.n → ℂ, star (Zm *ᵥ w) ⬝ᵥ G.gram v *ᵥ (Zm *ᵥ w) = star w ⬝ᵥ (herm G v β *ᵥ w)`. Introduce `w`. Rewrite using `[hZ, GlobalTheory.form_conjTranspose_mul_mul]`. Establish `heig : ∀ w : Fin G.n → ℂ, FixL G v β y₀ w → ∃ μ : ℂ, g *ᵥ (Zm *ᵥ w) = μ • (Zm *ᵥ w)`. Introduce and unpack `w ⟨μ, hμ⟩`.

Use `⟨μ, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZiZ, Matrix.mul_one, ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul]`. Take `⟨c, hc⟩` from `GlobalTheory.eigvec_pos_unique_of_similitude (G.gram v) (G.gram_herm v) (G.gram_det v) hsig g s hspos hsim hcp (Zm *ᵥ z) (Zm *ᵥ z') (by rw [hpos]; exact hz) (by rw [hpos]; exact hz') (heig z hf) (heig z' hf')`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use `congrArg (Zi *ᵥ ·) hc` as an intermediate fact.

Simplify using `only [Matrix.mulVec_mulVec, hZiZ, Matrix.one_mulVec, Matrix.mulVec_smul] at this`. Conclude with `this`.
-/
theorem fixL_pos_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β,
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
    FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  intro p _ G v hsig β hsh hR y₀ hdeg hsep z z' hz hz' hf hf'
  obtain ⟨_, _, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hsh hR
  set g0 : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) with hg0
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := (Z : Matrix (Fin G.n) (Fin G.n) ℂ) with hZm
  set Zi : Matrix (Fin G.n) (Fin G.n) ℂ := ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) with hZi
  have hZiZ : Zi * Zm = 1 := by rw [hZi, hZm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZZi : Zm * Zi = 1 := by rw [hZi, hZm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set s : ℝ := ((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hspos : 0 < s := by rw [hs]; exact_mod_cast y₀.2.2
  have hsim0 := GlobalTheory.LKCx.grp_similitude_herm p G v β y₀
  set g : Matrix (Fin G.n) (Fin G.n) ℂ := Zm * g0 * Zi with hg
  have hsim : gᴴ * G.gram v * g = (s : ℂ) • G.gram v := by
    have e1 : gᴴ * G.gram v * g = Ziᴴ * (g0ᴴ * (Zmᴴ * G.gram v * Zm) * g0) * Zi := by
      rw [hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, ← hZ, hsim0]
    have e2 : Ziᴴ * ((((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β) * Zi =
        (s : ℂ) • ((Zm * Zi)ᴴ * G.gram v * (Zm * Zi)) := by
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [e2, hZZi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcp : g.charpoly.Separable := by
    have e : g = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * g0 * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) := rfl
    rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact GlobalTheory.LKMid.charpoly_psi_separable p G v _ hdeg hsep
  have hpos : ∀ w : Fin G.n → ℂ, star (Zm *ᵥ w) ⬝ᵥ G.gram v *ᵥ (Zm *ᵥ w) = star w ⬝ᵥ (herm G v β *ᵥ w) := by
    intro w; rw [hZ, GlobalTheory.form_conjTranspose_mul_mul]
  have heig : ∀ w : Fin G.n → ℂ, FixL G v β y₀ w → ∃ μ : ℂ, g *ᵥ (Zm *ᵥ w) = μ • (Zm *ᵥ w) := by
    rintro w ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZiZ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := GlobalTheory.eigvec_pos_unique_of_similitude (G.gram v) (G.gram_herm v) (G.gram_det v) hsig g s hspos
    hsim hcp (Zm *ᵥ z) (Zm *ᵥ z') (by rw [hpos]; exact hz) (by rw [hpos]; exact hz') (heig z hf) (heig z' hf')
  refine ⟨c, ?_⟩
  have := congrArg (Zi *ᵥ ·) hc
  simp only [Matrix.mulVec_mulVec, hZiZ, Matrix.one_mulVec, Matrix.mulVec_smul] at this
  exact this

end GlobalTheory.LKCx
