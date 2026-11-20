import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.RealGram

open GlobalTheory.HermFrame Filter

/- English proof (translation)
Introduce `E _ _ _ _ g H z h2 hu hs hh hdd ξ η`. Establish `hsz : (H z)ᵀ = H z` using `hs.self_of_nhds.eq`. Establish `hhz : (H z)ᴴ = H z` using `hh.self_of_nhds.eq`. Establish `he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x)` using `hs.mono fun x hx => by show (H x)⁻¹ = (H x)⁻¹ᵀ`. Rewrite using `[transpose_nonsing_inv, hx.eq]`.

Establish `hbar : (mdbar H z η)ᵀ = mdbar H z η`. Rewrite using `[← mdbar_transpose]`. Conclude with `mdbar_congr (hs.mono fun x hx => hx.eq) η`. Establish `hdel : (mdel H z η)ᴴ = mdbar H z η` using `conjTranspose_mdel hh η`. Establish `key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ`.

Rewrite using `[conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv, transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]`. Rewrite using `[curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero, sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]`.
-/
theorem curv_inv_of_real : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  intro E _ _ _ _ g H z h2 hu hs hh hdd ξ η
  have hsz : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hhz : (H z)ᴴ = H z := hh.self_of_nhds.eq
  have he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x) :=
    hs.mono fun x hx => by
      show (H x)⁻¹ = (H x)⁻¹ᵀ
      rw [transpose_nonsing_inv, hx.eq]
  have hbar : (mdbar H z η)ᵀ = mdbar H z η := by
    rw [← mdbar_transpose]; exact mdbar_congr (hs.mono fun x hx => hx.eq) η
  have hdel : (mdel H z η)ᴴ = mdbar H z η := conjTranspose_mdel hh η
  have key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ := by
    rw [conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv,
      transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]
  rw [curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero,
    sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.RealGram
