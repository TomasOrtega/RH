import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlockStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomainStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermConv

/- English proof (translation)
Introduce `D n ρ p hn M m H hH hC τ hτ`. Establish `hτ0 : 0 ≤ τ` using `le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg ρ) hτ)`. Establish `hadj0 : ∀ k l : ℕ, GlobalTheory.MixModel.adj (0 : Mx D k l) = 0`. Introduce `k l`. Use `show ((0 : Mx D k l).map (cA D)).transpose = 0`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hadj1 : GlobalTheory.MixModel.adj (1 : Mx D ρ ρ) = 1` using `by show ((1 : Mx D ρ ρ).map (cA D)).transpose = 1`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Establish `hadjn1 : GlobalTheory.MixModel.adj (-1 : Mx D ρ ρ) = -1` using `by show ((-1 : Mx D ρ ρ).map (cA D)).transpose = -1`.

Rewrite using `[Matrix.map_neg _ (fun a => map_neg (cA D) a), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_neg, Matrix.transpose_one]`. Establish `hone : GlobalTheory.StdUnn.blk4 (1 : Mx D ρ ρ) 0 0 1 = 1` using `by show (Matrix.fromBlocks (1 : Mx D ρ ρ) 0 0 1).submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm = 1`. Rewrite using `[Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`. Establish `hJ1 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0 * GlobalTheory.StdUnn.blk4 0 (-1) 1 0 = 1`. Rewrite using `[GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]`.

Simplify using `only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]`. Conclude with `hone`. Establish `hJ2 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) (-1) 1 0 * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = 1`. Rewrite using `[GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]`. Simplify using `only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]`.

Conclude with `hone`. Set `u : GL (Fin (ρ + ρ)) (AE D)` to `⟨GlobalTheory.StdUnn.blk4 0 1 (-1) 0, GlobalTheory.StdUnn.blk4 0 (-1) 1 0, hJ1, hJ2⟩`. Establish `hu : GlobalTheory.MixModel.adj (u : Mx D (ρ + ρ) (ρ + ρ)) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * (u : Mx D (ρ + ρ) (ρ + ρ)) = GlobalTheory.StdUnn.blk4 0 1 (-1) 0` using `by show GlobalTheory.MixModel.adj (GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = GlobalTheory.StdUnn.blk4 0 1 (-1) 0`. Rewrite using `[GlobalTheory.CompanionTheory.JacobiMaps.adjoint_symplectic_block_product, hadj0, hadj1, hadjn1]`. Simplify using `only [zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, neg_neg, mul_neg, neg_mul, sub_self, neg_zero]`.

Take `⟨ι, hιc, hιm⟩` from `GlobalTheory.T.exists_first_block_group_embedding D n ρ p hn`. Establish `hH'` using `GlobalTheory.T.height_pullback_first_block D n ρ p hn ι hιc hιm H hH`. Set `w' : G D ρ` to `GlobalTheory.CompanionTheory.JacobiMaps.mkG u hu`. Establish `hw' : GlobalTheory.StdUnn.mat w' = GlobalTheory.StdUnn.blk4 0 1 (-1) 0` using `GlobalTheory.CompanionTheory.JacobiMaps.mat_mkG u hu`. Set `nb : hermA D ρ → G D ρ` to `fun z => GlobalTheory.CompanionTheory.JacobiMaps.nAt (z : Mx D ρ ρ) z.2`.

Establish `hnb : ∀ z : hermA D ρ, GlobalTheory.StdUnn.mat (nb z) = GlobalTheory.StdUnn.blk4 1 (z : Mx D ρ ρ) 0 1` using `fun z => GlobalTheory.CompanionTheory.JacobiMaps.mat_nAt _ _`. Establish `hS` using `GlobalTheory.T.height_power_summable_rational_hermitian D ρ (fun h => H (ι h)) hH' w' nb hw' hnb τ hτ`. Establish `hιw : ι w' = M.w`. Apply `GlobalTheory.CompanionTheory.FourierN.mat_injective` to reduce the goal to its premises. Rewrite using `[hιm w' 0 1 (-1) 0 hw', M.w_mat]`.

Establish `hιn : ∀ z : hermA D ρ, ι (nb z) = M.nzx z 0`. Introduce `z`. Apply `GlobalTheory.CompanionTheory.FourierN.mat_injective` to reduce the goal to its premises. Rewrite using `[hιm (nb z) 1 (z : Mx D ρ ρ) 0 1 (hnb z), M.nzx_mat, hadj0, GlobalTheory.CompanionTheory.PcB.blockMatrix_one, GlobalTheory.CompanionTheory.JacobiMaps.blockMatrix_zero]`. Establish `hf_eq : ∀ z : hermA D ρ, (H (M.w * M.nzx z 0) : ℝ) ^ τ = (H (ι (w' * nb z)) : ℝ) ^ τ`.

Introduce `z`. Rewrite using `[map_mul, hιw, hιn]`. Establish `hSum : Summable (fun ζ : ratHerm D ρ => (H (M.w * M.nzx (ζ : hermA D ρ) 0) : ℝ) ^ τ)`. Simplify `hS` using `only [hf_eq]`. Take `⟨K, hK, hKc⟩` from `GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := ρ)`.

Establish `hNc : Continuous fun z : hermA D ρ => M.nzx z 0` using `GlobalTheory.CompanionTheory.PcB.continuous_nz M`. Take `⟨κ, hκ1, hκ⟩` from `GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC ((fun z => M.nzx z 0) '' K) (hK.image hNc)`. Use `GlobalTheory.T.integrable_of_summable_fundamental_domain D ρ m.lz m.𝓖 m.hz (fun ζ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) ?_ ?_ hSum K hKc (κ ^ τ) (Real.rpow_nonneg (by linarith) τ) ?_` and prove the remaining obligations. Conclude with `(NNReal.continuous_coe.comp (hH.1.comp (continuous_const.mul hNc))).rpow_const fun _ => Or.inr hτ0`. Conclude with `fun z => Real.rpow_nonneg (NNReal.coe_nonneg _) τ`.

Introduce `ζ _ z hz`. Establish `h1 : M.nzx (ζ + z) 0 = M.nzx ζ 0 * M.nzx z 0`. Rewrite using `[GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero]`. Establish `h2` using `hκ (M.nzx z 0) ⟨z, hz, rfl⟩ (M.w * M.nzx ζ 0)`. Use `show (H (M.w * M.nzx (ζ + z) 0) : ℝ) ^ τ ≤ κ ^ τ * (H (M.w * M.nzx ζ 0) : ℝ) ^ τ`.

Rewrite using `[h1, ← mul_assoc, ← Real.mul_rpow (by linarith) (NNReal.coe_nonneg _)]`. Conclude with `Real.rpow_le_rpow (NNReal.coe_nonneg _) h2 hτ0`.
-/
theorem integrable_height_rpow : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (H : G D n → ℝ≥0), IsHt H →
  (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Integrable (fun ζ : hermA D ρ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) m.lz := by
  intro D n ρ p hn M m H hH hC τ hτ
  have hτ0 : 0 ≤ τ := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg ρ) hτ)
  have hadj0 : ∀ k l : ℕ, GlobalTheory.MixModel.adj (0 : Mx D k l) = 0 := by
    intro k l
    show ((0 : Mx D k l).map (cA D)).transpose = 0
    ext i j
    simp
  have hadj1 : GlobalTheory.MixModel.adj (1 : Mx D ρ ρ) = 1 := by
    show ((1 : Mx D ρ ρ).map (cA D)).transpose = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hadjn1 : GlobalTheory.MixModel.adj (-1 : Mx D ρ ρ) = -1 := by
    show ((-1 : Mx D ρ ρ).map (cA D)).transpose = -1
    rw [Matrix.map_neg _ (fun a => map_neg (cA D) a), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_neg, Matrix.transpose_one]
  have hone : GlobalTheory.StdUnn.blk4 (1 : Mx D ρ ρ) 0 0 1 = 1 := by
    show (Matrix.fromBlocks (1 : Mx D ρ ρ) 0 0 1).submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm = 1
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hJ1 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0 * GlobalTheory.StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  have hJ2 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) (-1) 1 0 * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  let u : GL (Fin (ρ + ρ)) (AE D) := ⟨GlobalTheory.StdUnn.blk4 0 1 (-1) 0, GlobalTheory.StdUnn.blk4 0 (-1) 1 0, hJ1, hJ2⟩
  have hu : GlobalTheory.MixModel.adj (u : Mx D (ρ + ρ) (ρ + ρ)) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * (u : Mx D (ρ + ρ) (ρ + ρ)) =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    show GlobalTheory.MixModel.adj (GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 *
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = GlobalTheory.StdUnn.blk4 0 1 (-1) 0
    rw [GlobalTheory.CompanionTheory.JacobiMaps.adjoint_symplectic_block_product, hadj0, hadj1, hadjn1]
    simp only [zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, neg_neg, mul_neg, neg_mul, sub_self, neg_zero]
  obtain ⟨ι, hιc, hιm⟩ := GlobalTheory.T.exists_first_block_group_embedding D n ρ p hn
  have hH' := GlobalTheory.T.height_pullback_first_block D n ρ p hn ι hιc hιm H hH
  let w' : G D ρ := GlobalTheory.CompanionTheory.JacobiMaps.mkG u hu
  have hw' : GlobalTheory.StdUnn.mat w' = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := GlobalTheory.CompanionTheory.JacobiMaps.mat_mkG u hu
  let nb : hermA D ρ → G D ρ := fun z => GlobalTheory.CompanionTheory.JacobiMaps.nAt (z : Mx D ρ ρ) z.2
  have hnb : ∀ z : hermA D ρ, GlobalTheory.StdUnn.mat (nb z) = GlobalTheory.StdUnn.blk4 1 (z : Mx D ρ ρ) 0 1 :=
    fun z => GlobalTheory.CompanionTheory.JacobiMaps.mat_nAt _ _
  have hS := GlobalTheory.T.height_power_summable_rational_hermitian D ρ (fun h => H (ι h)) hH' w' nb hw' hnb τ hτ
  have hιw : ι w' = M.w := by
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm w' 0 1 (-1) 0 hw', M.w_mat]
  have hιn : ∀ z : hermA D ρ, ι (nb z) = M.nzx z 0 := by
    intro z
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm (nb z) 1 (z : Mx D ρ ρ) 0 1 (hnb z), M.nzx_mat, hadj0, GlobalTheory.CompanionTheory.PcB.blockMatrix_one, GlobalTheory.CompanionTheory.JacobiMaps.blockMatrix_zero]
  have hf_eq : ∀ z : hermA D ρ, (H (M.w * M.nzx z 0) : ℝ) ^ τ = (H (ι (w' * nb z)) : ℝ) ^ τ := by
    intro z
    rw [map_mul, hιw, hιn]
  have hSum : Summable (fun ζ : ratHerm D ρ => (H (M.w * M.nzx (ζ : hermA D ρ) 0) : ℝ) ^ τ) := by
    simpa only [hf_eq] using hS
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := ρ)
  have hNc : Continuous fun z : hermA D ρ => M.nzx z 0 := GlobalTheory.CompanionTheory.PcB.continuous_nz M
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC
    ((fun z => M.nzx z 0) '' K) (hK.image hNc)
  refine GlobalTheory.T.integrable_of_summable_fundamental_domain D ρ m.lz m.𝓖 m.hz (fun ζ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) ?_ ?_ hSum K hKc (κ ^ τ)
    (Real.rpow_nonneg (by linarith) τ) ?_
  · exact (NNReal.continuous_coe.comp (hH.1.comp (continuous_const.mul hNc))).rpow_const fun _ => Or.inr hτ0
  · exact fun z => Real.rpow_nonneg (NNReal.coe_nonneg _) τ
  · intro ζ _ z hz
    have h1 : M.nzx (ζ + z) 0 = M.nzx ζ 0 * M.nzx z 0 := by
      rw [GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero]
    have h2 := hκ (M.nzx z 0) ⟨z, hz, rfl⟩ (M.w * M.nzx ζ 0)
    show (H (M.w * M.nzx (ζ + z) 0) : ℝ) ^ τ ≤ κ ^ τ * (H (M.w * M.nzx ζ 0) : ℝ) ^ τ
    rw [h1, ← mul_assoc, ← Real.mul_rpow (by linarith) (NNReal.coe_nonneg _)]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) h2 hτ0

end GlobalTheory.CompanionTheory.HermConv

end
