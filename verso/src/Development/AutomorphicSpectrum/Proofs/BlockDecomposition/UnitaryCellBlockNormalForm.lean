import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

section RowReduce

variable {K : Type} [Field K] {n ρ p : ℕ}

/- English proof (translation)
Establish `hz : Function.Injective (zinc (K` using `K) hn) := by`. Introduce `u v huv`. Use function extensionality and compare the values at `j`. Use `congrFun huv ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))` as an intermediate fact. Simplify `this` using `[zinc]`.

Use `set f : (Fin ρ → K) →ₗ[K] (Fin n → K) := C.mulVecLin ∘ₗ zinc hn with hfdef`. Use `set g : (Fin ρ → K) →ₗ[K] (Fin n → K) := -(zinc hn) with hgdef`. Establish `hf : Function.Injective f` using `LinearMap.ker_eq_bot.mp h`. Establish `hg : Function.Injective g`. Introduce `u v huv`.

Apply `hz` to reduce the goal to its premises. Simplify `huv` using `[hgdef]`. Take `⟨W, hW⟩` from `Submodule.exists_isCompl (LinearMap.range f)`. Take `⟨W', hW'⟩` from `Submodule.exists_isCompl (LinearMap.range g)`. Establish `hfin : Module.finrank K W = Module.finrank K W'`.

Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hW`. Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hW'`. Rewrite `h1` using `[LinearMap.finrank_range_of_inj hf]`. Rewrite `h2` using `[LinearMap.finrank_range_of_inj hg]`. Use linear arithmetic over natural numbers and integers.

Set `ψ : W ≃ₗ[K] W'` to `LinearEquiv.ofFinrankEq W W' hfin`. Set `φ : LinearMap.range f ≃ₗ[K] LinearMap.range g` to `(LinearEquiv.ofInjective f hf).symm.trans (LinearEquiv.ofInjective g hg)`. Set `A : (Fin n → K) ≃ₗ[K] (Fin n → K)` to `(Submodule.prodEquivOfIsCompl _ _ hW).symm.trans ((φ.prodCongr ψ).trans (Submodule.prodEquivOfIsCompl _ _ hW'))`. Establish `hA : ∀ u, A (f u) = g u`. Introduce `u`.

Establish `h0 : (Submodule.prodEquivOfIsCompl _ _ hW).symm (f u) = ((⟨f u, LinearMap.mem_range_self f u⟩ : LinearMap.range f), (0 : W))` using `Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hW ⟨f u, LinearMap.mem_range_self f u⟩`. Establish `h1 : φ ⟨f u, LinearMap.mem_range_self f u⟩ = ⟨g u, LinearMap.mem_range_self g u⟩`. Establish `: (LinearEquiv.ofInjective f hf).symm ⟨f u, LinearMap.mem_range_self f u⟩ = u` using `(LinearEquiv.ofInjective f hf).symm_apply_apply u`. Simplify using `only [φ, LinearEquiv.trans_apply, this]`. Both sides reduce to the same expression.

Simplify using `only [A, LinearEquiv.trans_apply, h0, LinearEquiv.prodCongr_apply, h1, map_zero]`. Simplify using the standard rewrite rules. Use `⟨LinearMap.toMatrix' A.toLinearMap, ?_, ?_⟩` and prove the remaining obligations. Use `Matrix.isUnit_det_of_left_inverse (B := LinearMap.toMatrix' A.symm.toLinearMap) ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp]`.

Simplify using the standard rewrite rules. Introduce `u`. Rewrite using `[← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]`. Conclude with `hA u`.
-/
theorem exists_rowReduce_firstCols (hn : ρ + p = n) (C : Matrix (Fin n) (Fin n) K)
    (h : LinearMap.ker (C.mulVecLin ∘ₗ zinc hn) = ⊥) :
    ∃ T : Matrix (Fin n) (Fin n) K, IsUnit T.det ∧ ∀ u, (T * C).mulVec (zinc hn u) = -(zinc hn u) := by
  have hz : Function.Injective (zinc (K := K) hn) := by
    intro u v huv
    funext j
    have := congrFun huv ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
    simpa [zinc] using this
  set f : (Fin ρ → K) →ₗ[K] (Fin n → K) := C.mulVecLin ∘ₗ zinc hn with hfdef
  set g : (Fin ρ → K) →ₗ[K] (Fin n → K) := -(zinc hn) with hgdef
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp h
  have hg : Function.Injective g := by
    intro u v huv
    apply hz
    simpa [hgdef] using huv
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range g)
  have hfin : Module.finrank K W = Module.finrank K W' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW
    have h2 := Submodule.finrank_add_eq_of_isCompl hW'
    rw [LinearMap.finrank_range_of_inj hf] at h1
    rw [LinearMap.finrank_range_of_inj hg] at h2
    omega
  let ψ : W ≃ₗ[K] W' := LinearEquiv.ofFinrankEq W W' hfin
  let φ : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
    (LinearEquiv.ofInjective f hf).symm.trans (LinearEquiv.ofInjective g hg)
  let A : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Submodule.prodEquivOfIsCompl _ _ hW).symm.trans
      ((φ.prodCongr ψ).trans (Submodule.prodEquivOfIsCompl _ _ hW'))
  have hA : ∀ u, A (f u) = g u := by
    intro u
    have h0 : (Submodule.prodEquivOfIsCompl _ _ hW).symm (f u) =
        ((⟨f u, LinearMap.mem_range_self f u⟩ : LinearMap.range f), (0 : W)) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hW ⟨f u, LinearMap.mem_range_self f u⟩
    have h1 : φ ⟨f u, LinearMap.mem_range_self f u⟩ = ⟨g u, LinearMap.mem_range_self g u⟩ := by
      have : (LinearEquiv.ofInjective f hf).symm ⟨f u, LinearMap.mem_range_self f u⟩ = u :=
        (LinearEquiv.ofInjective f hf).symm_apply_apply u
      simp only [φ, LinearEquiv.trans_apply, this]
      rfl
    simp only [A, LinearEquiv.trans_apply, h0, LinearEquiv.prodCongr_apply, h1, map_zero]
    simp
  refine ⟨LinearMap.toMatrix' A.toLinearMap, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_left_inverse (B := LinearMap.toMatrix' A.symm.toLinearMap) ?_
    rw [← LinearMap.toMatrix'_comp]
    simp
  · intro u
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    exact hA u

/- English proof (translation)
Use `set e := finSumFinEquiv.trans (finCongr hn) with he`. Use `⟨(N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₂, ?_⟩` and prove the remaining obligations. Establish `hcol : ∀ (i : Fin n) (j : Fin ρ), N i (e (Sum.inl j)) = -(zinc hn (Pi.single j 1) i)`. Introduce `i j`. Establish `h1` using `congrFun (h (Pi.single j 1)) i`.

Establish `h2 : zinc hn (Pi.single j (1 : K)) = Pi.single (e (Sum.inl j)) 1`. Use function extensionality and compare the values at `k`. Take `⟨k, rfl⟩` from `e.surjective k`. Break down `k with k | k` into its components or cases. Simplify using `[zinc, he, Pi.single_apply]`.

Establish `hne : e (Sum.inr k) ≠ e (Sum.inl j)` using `fun hh => by simpa using e.injective hh`. Rewrite using `[Pi.single_eq_of_ne hne]`. Simplify using `[zinc, he]`. Rewrite `h1` using `[h2, Matrix.mulVec_single_one]`. Rewrite using `[h2]`.

Simplify using `using h1`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`.

Simplify using `[bl, ← he, hcol, zinc, Matrix.one_apply, Pi.single_apply]`. Simplify using `[bl, ← he, Matrix.toBlocks₁₂]`. Simplify using `[bl, ← he, hcol, zinc]`. Simplify using `[bl, ← he, Matrix.toBlocks₂₂]`.
-/
theorem exists_bl_firstCols (hn : ρ + p = n) (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ u, N.mulVec (zinc hn u) = -(zinc hn u)) :
    ∃ (X : Matrix (Fin ρ) (Fin p) K) (c' : Matrix (Fin p) (Fin p) K), N = bl hn (-1) X 0 c' := by
  classical
  set e := finSumFinEquiv.trans (finCongr hn) with he
  refine ⟨(N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₂, ?_⟩
  have hcol : ∀ (i : Fin n) (j : Fin ρ), N i (e (Sum.inl j)) = -(zinc hn (Pi.single j 1) i) := by
    intro i j
    have h1 := congrFun (h (Pi.single j 1)) i
    have h2 : zinc hn (Pi.single j (1 : K)) = Pi.single (e (Sum.inl j)) 1 := by
      funext k
      obtain ⟨k, rfl⟩ := e.surjective k
      rcases k with k | k
      · simp [zinc, he, Pi.single_apply]
      · have hne : e (Sum.inr k) ≠ e (Sum.inl j) := fun hh => by simpa using e.injective hh
        rw [Pi.single_eq_of_ne hne]
        simp [zinc, he]
    rw [h2, Matrix.mulVec_single_one] at h1
    rw [h2]
    simpa using h1
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [bl, ← he, hcol, zinc, Matrix.one_apply, Pi.single_apply]
  · simp [bl, ← he, Matrix.toBlocks₁₂]
  · simp [bl, ← he, hcol, zinc]
  · simp [bl, ← he, Matrix.toBlocks₂₂]

/- English proof (translation)
Use `set e := finSumFinEquiv.trans (finCongr hn) with he`. Use `⟨(N.submatrix e e).toBlocks₁₁, (N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₁, (N.submatrix e e).toBlocks₂₂, ?_⟩` and prove the remaining obligations. Unfold `bl`. Rewrite using `[Matrix.fromBlocks_toBlocks]`. Use extensionality with `i j`.

Simplify using `[← he]`.
-/
theorem exists_bl_blocks (hn : ρ + p = n) (N : Matrix (Fin n) (Fin n) K) :
    ∃ (a : Matrix (Fin ρ) (Fin ρ) K) (b : Matrix (Fin ρ) (Fin p) K) (c : Matrix (Fin p) (Fin ρ) K)
      (d : Matrix (Fin p) (Fin p) K), N = bl hn a b c d := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  refine ⟨(N.submatrix e e).toBlocks₁₁, (N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₁,
    (N.submatrix e e).toBlocks₂₂, ?_⟩
  unfold bl
  rw [Matrix.fromBlocks_toBlocks]
  ext i j
  simp [← he]

end RowReduce

/- English proof (translation)
Introduce `K _ σ hσ n ρ p hn x hdet hU hker`. Take `⟨T, hT, hTC⟩` from `exists_rowReduce_firstCols hn (lowerC x) hker`. Take `⟨X, c', hN⟩` from `exists_bl_firstCols hn (T * lowerC x) hTC`. Take `⟨a, b, hx⟩` from `GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x`. Establish `hTi : T⁻¹ * T = 1` using `Matrix.nonsing_inv_mul T hT`.

Establish `hiT : T * T⁻¹ = 1` using `Matrix.mul_nonsing_inv T hT`. Establish `hcc : ∀ M : Matrix (Fin n) (Fin n) K, cT σ (cT σ M) = M`. Introduce `M`. Use extensionality with `i j`. Simplify using `[cT, hσ]`.

Establish `hcTi : cT σ T * cT σ T⁻¹ = 1`. Rewrite using `[← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]`. Establish `hcTi' : cT σ T⁻¹ * cT σ T = 1`. Rewrite using `[← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hiT, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]`. Use `set m : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (cT σ T⁻¹) 0 0 T with hm`.

Establish `hmU : cT σ m * blk4 0 1 (-1) 0 * m = blk4 0 1 (-1) 0`. Rewrite using `[hm, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hcc]`. Establish `hc0 : cT σ (0 : Matrix (Fin n) (Fin n) K) = 0`. Use extensionality with `i j`. Simplify using `[cT]`.

Simplify using `[hTi, hcTi, hc0]`. Establish `hmdet : IsUnit m.det`. Use `Matrix.isUnit_det_of_left_inverse (B := blk4 (cT σ T) 0 0 T⁻¹) ?_` and prove the remaining obligations. Rewrite using `[hm, submatrix_fromBlocks_mul]`. Simplify using `[hTi, hcTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]`.

Establish `hmx : m * x = blk4 (cT σ T⁻¹ * a) (cT σ T⁻¹ * b) (T * lowerC x) (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)` using `by conv_lhs => rw [hx, hm, submatrix_fromBlocks_mul]`. Simplify using the standard rewrite rules. Take `⟨a₁, a₂, a₃, a₄, ha⟩` from `exists_bl_blocks hn (cT σ T⁻¹ * a)`. Take `⟨b₁, b₂, b₃, b₄, hb⟩` from `exists_bl_blocks hn (cT σ T⁻¹ * b)`. Take `⟨Z, Y, W, d', hd⟩` from `exists_bl_blocks hn (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)`.

Establish `hfin : blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d') = m * x`. Rewrite using `[hmx, ha, hb, hN, hd]`. Use `⟨T⁻¹, a₁, b₁, Z, a₂, b₂, X, Y, a₃, b₃, W, a₄, b₄, c', d', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfin]`. Unfold `IsUnitary at hU ⊢`.

Establish `hc : cT σ (m * x) = cT σ x * cT σ m`. Unfold `cT`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hfin, Matrix.det_mul]`. Conclude with `hmdet.mul hdet`. Rewrite using `[← hN, ← Matrix.mul_assoc, hTi, Matrix.one_mul]`. Rewrite using `[← hd, ← Matrix.mul_assoc, hTi, Matrix.one_mul]`.
-/
theorem rowReduce_lowerC : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit x.det → IsUnitary σ (blk4 0 1 (-1) 0) x → LinearMap.ker ((lowerC x).mulVecLin ∘ₗ zinc hn) = ⊥ →
    ∃ (T₀ : Matrix (Fin n) (Fin n) K) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
      IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) ∧
      IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det ∧
      lowerC x = T₀ * bl hn (-1) X 0 c' ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T₀ * bl hn Z Y W d' := by
  intro K _ σ hσ n ρ p hn x hdet hU hker
  obtain ⟨T, hT, hTC⟩ := exists_rowReduce_firstCols hn (lowerC x) hker
  obtain ⟨X, c', hN⟩ := exists_bl_firstCols hn (T * lowerC x) hTC
  obtain ⟨a, b, hx⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hiT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have hcc : ∀ M : Matrix (Fin n) (Fin n) K, cT σ (cT σ M) = M := by
    intro M
    ext i j
    simp [cT, hσ]
  have hcTi : cT σ T * cT σ T⁻¹ = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  have hcTi' : cT σ T⁻¹ * cT σ T = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hiT, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  set m : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (cT σ T⁻¹) 0 0 T with hm
  have hmU : cT σ m * blk4 0 1 (-1) 0 * m = blk4 0 1 (-1) 0 := by
    rw [hm, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hcc]
    have hc0 : cT σ (0 : Matrix (Fin n) (Fin n) K) = 0 := by
      ext i j
      simp [cT]
    simp [hTi, hcTi, hc0]
  have hmdet : IsUnit m.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := blk4 (cT σ T) 0 0 T⁻¹) ?_
    rw [hm, submatrix_fromBlocks_mul]
    simp [hTi, hcTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]
  have hmx : m * x = blk4 (cT σ T⁻¹ * a) (cT σ T⁻¹ * b) (T * lowerC x) (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) := by
    conv_lhs => rw [hx, hm, submatrix_fromBlocks_mul]
    simp
  obtain ⟨a₁, a₂, a₃, a₄, ha⟩ := exists_bl_blocks hn (cT σ T⁻¹ * a)
  obtain ⟨b₁, b₂, b₃, b₄, hb⟩ := exists_bl_blocks hn (cT σ T⁻¹ * b)
  obtain ⟨Z, Y, W, d', hd⟩ := exists_bl_blocks hn (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)
  have hfin : blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d') = m * x := by
    rw [hmx, ha, hb, hN, hd]
  refine ⟨T⁻¹, a₁, b₁, Z, a₂, b₂, X, Y, a₃, b₃, W, a₄, b₄, c', d', ?_, ?_, ?_, ?_⟩
  · rw [hfin]
    unfold IsUnitary at hU ⊢
    have hc : cT σ (m * x) = cT σ x * cT σ m := by
      unfold cT
      rw [Matrix.map_mul, Matrix.transpose_mul]
    rw [hc]
    calc cT σ x * cT σ m * blk4 0 1 (-1) 0 * (m * x)
        = cT σ x * (cT σ m * blk4 0 1 (-1) 0 * m) * x := by simp only [Matrix.mul_assoc]
      _ = blk4 0 1 (-1) 0 := by rw [hmU, hU]
  · rw [hfin, Matrix.det_mul]
    exact hmdet.mul hdet
  · rw [← hN, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  · rw [← hd, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
end GlobalTheory.CompanionTheory.ZUnf
