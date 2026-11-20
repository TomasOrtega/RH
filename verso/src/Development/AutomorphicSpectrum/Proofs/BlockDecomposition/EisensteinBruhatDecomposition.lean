import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransformStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatricesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExistsStatement

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[inv_of_unitary σ h, cT_blk4]`. Unfold `Jm`. Rewrite using `[submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, neg_block_matrix]`. Apply the tactic sequence `congr 1 <;> simp`.
-/
theorem inv_block_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) :
    (blk4 A B C D)⁻¹ = blk4 (cT σ D) (-cT σ B) (-cT σ C) (cT σ A) := by
  rw [inv_of_unitary σ h, cT_blk4]
  unfold Jm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, neg_block_matrix]
  congr 1 <;> simp

/- English proof (translation)
Establish `h1 : blk4 A B C D * (blk4 A B C D)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_det_of_unitary σ h)`. Rewrite `h1` using `[inv_block_of_unitary σ h, submatrix_fromBlocks_mul, ← block_matrix_one]`. Use `(blockMatrixTwoByTwoFin_injective h1).2.2.1` as an intermediate fact. Rewrite `this` using `[Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero]`. Conclude with `this`.
-/
theorem isotropic_of_unitary (σ : K →+* K) {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (Jm K n) (blk4 A B C D)) : C * cT σ D = D * cT σ C := by
  have h1 : blk4 A B C D * (blk4 A B C D)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_of_unitary σ h)
  rw [inv_block_of_unitary σ h, submatrix_fromBlocks_mul, ← block_matrix_one] at h1
  have := (blockMatrixTwoByTwoFin_injective h1).2.2.1
  rw [Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero] at this
  exact this

/- English proof (translation)
Establish `hu : IsUnitary σ (Jm K n) (repMat σ b a)`. Unfold `repMat`. Use `unitary_mul σ (unitary_mul σ ?_ ?_) ?_` and prove the remaining obligations. Unfold `IsUnitary wr Jm`. Rewrite using `[cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`.

Establish `e2` using `eId_mul_eId (K := K) n r`. Simplify using `only [cT_sub, cT_one, cT_neg, cT_eId]`. Use `congr 1`. Simplify using `only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]`. Normalize the expressions using the abelian group laws.

Simplify using `only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]`. Normalize the expressions using the abelian group laws. Simplify using `only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]`. Normalize the expressions using the abelian group laws. Simplify using `only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]`.

Normalize the expressions using the abelian group laws. Unfold `IsUnitary nB Jm`. Establish `hB : cT σ (extB (n` using `n) b) = extB b := by rw [cT_extB, hb]`. Rewrite using `[cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]`. Simplify using `[cT_one, cT_zero, hB]`.

Unfold `IsUnitary mA Jm`. Establish `ha'` using `isUnit_det_cT σ ha`. Rewrite using `[cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, cT_inv σ ha', cT_cT σ hσ]`. Simplify using `[cT_zero, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]`. Conclude with `⟨isUnit_det_of_unitary σ hu, hu⟩`.
-/
theorem repMat_unitary (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) :
    IsUnit (repMat σ b a).det ∧ IsUnitary σ (Jm K n) (repMat σ b a) := by
  have hu : IsUnitary σ (Jm K n) (repMat σ b a) := by
    unfold repMat
    refine unitary_mul σ (unitary_mul σ ?_ ?_) ?_
    · unfold IsUnitary wr Jm
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      have e2 := eId_mul_eId (K := K) n r
      simp only [cT_sub, cT_one, cT_neg, cT_eId]
      congr 1
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
      · simp only [mul_zero, zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, neg_neg, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.one_mul, Matrix.neg_mul, e2]; abel
    · unfold IsUnitary nB Jm
      have hB : cT σ (extB (n := n) b) = extB b := by rw [cT_extB, hb]
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
      simp [cT_one, cT_zero, hB]
    · unfold IsUnitary mA Jm
      have ha' := isUnit_det_cT σ ha
      rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, cT_inv σ ha', cT_cT σ hσ]
      simp [cT_zero, Matrix.mul_nonsing_inv _ ha', Matrix.nonsing_inv_mul _ ha]
  exact ⟨isUnit_det_of_unitary σ hu, hu⟩

/- English proof (translation)
Establish `hu` using `(repMat_unitary σ hσ b a hb ha).2`. Rewrite `hu`, the goal using `[repMat_eq]`. Rewrite using `[inv_block_of_unitary σ hu, submatrix_fromBlocks_mul, is_siegel_parabolic_block_iff]`. Simplify using `only [cT_mul, cT_neg, cT_sub, cT_one, cT_eId, cT_extB, hb, cT_inv σ (isUnit_det_cT σ ha), cT_cT σ hσ, neg_neg, Matrix.mul_neg, Matrix.mul_assoc]`.
-/
theorem siegel_rep_iff (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K)
    (a : Matrix (Fin n) (Fin n) K) (hb : cT σ b = b) (ha : IsUnit a.det) (A B C D : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 A B C D * (repMat σ b a)⁻¹) ↔
      C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  have hu := (repMat_unitary σ hσ b a hb ha).2
  rw [repMat_eq] at hu ⊢
  rw [inv_block_of_unitary σ hu, submatrix_fromBlocks_mul, is_siegel_parabolic_block_iff]
  simp only [cT_mul, cT_neg, cT_sub, cT_one, cT_eId, cT_extB, hb, cT_inv σ (isUnit_det_cT σ ha), cT_cT σ hσ,
    neg_neg, Matrix.mul_neg, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨p1, p2, p3, p4, hp'⟩` from `exists_blockMatrixTwoByTwoFin_eq (g * h⁻¹)`. Rewrite `hp` using `[hp', is_siegel_parabolic_block_iff]`. Substitute `hp` using the available equality. Establish `hgp : g = blk4 p1 p2 0 p4 * h`. Rewrite using `[← hp', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.mul_one]`.

Establish `hdet : IsUnit (blk4 p1 p2 0 p4).det`. Rewrite using `[← hp', Matrix.det_mul]`. Conclude with `hg.mul (Matrix.isUnit_nonsing_inv_det _ hh)`. Rewrite `hdet` using `[det_block_lower_zero]`. Rewrite `hgp` using `[eg, eh, submatrix_fromBlocks_mul]`.

Use `blockMatrixTwoByTwoFin_injective hgp` as an intermediate fact. Use `⟨p4, isUnit_of_mul_isUnit_right hdet, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using this.2.2.1`. Simplify using `using this.2.2.2`.
-/
theorem factor_of_siegel {n : ℕ} {g h : Matrix (Fin (n + n)) (Fin (n + n)) K} (hg : IsUnit g.det)
    (hh : IsUnit h.det) (hp : IsSiegelP (g * h⁻¹)) {A B C D A' B' C' D' : Matrix (Fin n) (Fin n) K}
    (eg : g = blk4 A B C D) (eh : h = blk4 A' B' C' D') :
    ∃ p : Matrix (Fin n) (Fin n) K, IsUnit p.det ∧ C = p * C' ∧ D = p * D' := by
  obtain ⟨p1, p2, p3, p4, hp'⟩ := exists_blockMatrixTwoByTwoFin_eq (g * h⁻¹)
  rw [hp', is_siegel_parabolic_block_iff] at hp
  subst hp
  have hgp : g = blk4 p1 p2 0 p4 * h := by
    rw [← hp', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.mul_one]
  have hdet : IsUnit (blk4 p1 p2 0 p4).det := by
    rw [← hp', Matrix.det_mul]; exact hg.mul (Matrix.isUnit_nonsing_inv_det _ hh)
  rw [det_block_lower_zero] at hdet
  rw [eg, eh, submatrix_fromBlocks_mul] at hgp
  have := blockMatrixTwoByTwoFin_injective hgp
  refine ⟨p4, isUnit_of_mul_isUnit_right hdet, ?_, ?_⟩
  · simpa using this.2.2.1
  · simpa using this.2.2.2

/- English proof (translation)
Establish `ha'` using `isUnit_det_cT σ ha`. Establish `h1 : p * eId K n r = p' * eId K n r`. Use `congrArg (· * a⁻¹) hC` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha]`. Establish `h2 : p * (1 - eId K n r - extB b) = p' * (1 - eId K n r - extB b')`.

Use `congrArg (· * cT σ a) hD` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha']`. Establish `key : ∀ b₀ : Matrix (Fin r) (Fin r) K, (1 - eId K n r - extB b₀) * (1 - eId K n r) = 1 - eId K n r`. Introduce `b₀`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, eId_mul_eId, extB_mul_eId]`.

Normalize the expressions using the abelian group laws. Establish `h3 : p * (1 - eId K n r) = p' * (1 - eId K n r)`. Combine the equalities or inequalities in the displayed calculation. Establish `hpp : p = p'`. Establish `e1 : ∀ q : Matrix (Fin n) (Fin n) K, q = q * eId K n r + q * (1 - eId K n r)`.

Introduce `q`. Rewrite using `[← Matrix.mul_add]`. Simplify using the standard rewrite rules. Rewrite using `[e1 p, e1 p', h1, h3]`. Substitute `hpp` using the available equality.

Use `congrArg (p⁻¹ * ·) h2` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul, sub_right_inj] at this`. Conclude with `extB_injective hr this`.
-/
theorem herm_unique (σ : K →+* K) {n r : ℕ} (hr : r ≤ n) (a : Matrix (Fin n) (Fin n) K) (ha : IsUnit a.det)
    (b b' : Matrix (Fin r) (Fin r) K) (p p' : Matrix (Fin n) (Fin n) K) (hp : IsUnit p.det)
    (hC : p * -(eId K n r * a) = p' * -(eId K n r * a))
    (hD : p * ((1 - eId K n r - extB b) * (cT σ a)⁻¹) = p' * ((1 - eId K n r - extB b') * (cT σ a)⁻¹)) :
    b = b' := by
  have ha' := isUnit_det_cT σ ha
  have h1 : p * eId K n r = p' * eId K n r := by
    have := congrArg (· * a⁻¹) hC
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha] using this
  have h2 : p * (1 - eId K n r - extB b) = p' * (1 - eId K n r - extB b') := by
    have := congrArg (· * cT σ a) hD
    simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha'] using this
  have key : ∀ b₀ : Matrix (Fin r) (Fin r) K,
      (1 - eId K n r - extB b₀) * (1 - eId K n r) = 1 - eId K n r := by
    intro b₀
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, eId_mul_eId, extB_mul_eId]
    abel
  have h3 : p * (1 - eId K n r) = p' * (1 - eId K n r) := by
    calc p * (1 - eId K n r) = p * ((1 - eId K n r - extB b) * (1 - eId K n r)) := by rw [key]
      _ = p * (1 - eId K n r - extB b) * (1 - eId K n r) := by rw [Matrix.mul_assoc]
      _ = p' * (1 - eId K n r - extB b') * (1 - eId K n r) := by rw [h2]
      _ = p' * (1 - eId K n r) := by rw [Matrix.mul_assoc, key]
  have hpp : p = p' := by
    have e1 : ∀ q : Matrix (Fin n) (Fin n) K, q = q * eId K n r + q * (1 - eId K n r) := by
      intro q; rw [← Matrix.mul_add]; simp
    rw [e1 p, e1 p', h1, h3]
  subst hpp
  have := congrArg (p⁻¹ * ·) h2
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul, sub_right_inj] at this
  exact extB_injective hr this

/- English proof (translation)
Introduce `K _ σ hσ _ n c hc a ha`. Establish `hr : ∀ U : Submodule K (Fin n → K), Module.finrank K U ≤ n` using `fun U => (Submodule.finrank_le U).trans (by simp)`. Use `⟨fun U b hb => repMat_unitary σ hσ b (a U) hb (ha U).1, ?_⟩` and prove the remaining obligations. Introduce `g hg hgu`. Take `⟨A, B, C, D, rfl⟩` from `exists_blockMatrixTwoByTwoFin_eq g`.

Establish `hiso` using `isotropic_of_unitary σ hgu`. Use `set U := Submodule.span K (Set.range C) with hU`. Take `⟨T, L, hT, -, hLT⟩` from `GlobalTheory.T.same_span_transfer_matrices C (c U) (hc U).1 (hc U).2`. Take `⟨b, hb, hcond⟩` from `GlobalTheory.T.hermitian_block_solution_exists σ hσ (hr U) (c U) (a U) C D T L (ha U) hT hLT hiso`. Establish `hS` using `(siegel_rep_iff σ hσ b (a U) hb (ha U).1 A B C D).2 hcond`.

Use `⟨⟨U, b, hb⟩, hS, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨U', b', hb'⟩ hq`. Establish `hrep'` using `repMat_unitary σ hσ b' (a U') hb' (ha U').1`. Take `⟨p', hp', hC', hD'⟩` from `factor_of_siegel hg hrep'.1 hq rfl (repMat_eq σ b' (a U'))`. Establish `hUU : U' = U`.

Rewrite using `[← (hc U').2, ← GlobalTheory.T.span_range_complement_transform (hr U') (c U') (a U') p' (ha U') hp', ← hC']`. Substitute `hUU` using the available equality. Establish `hrep` using `repMat_unitary σ hσ b (a U) hb (ha U).1`. Take `⟨p, hp, hC, hD⟩` from `factor_of_siegel hg hrep.1 hS rfl (repMat_eq σ b (a U))`. Establish `hbb` using `herm_unique σ (hr U) (a U) (ha U).1 b' b p' p hp' (hC'.symm.trans hC) (hD'.symm.trans hD)`.

Substitute `hbb` using the available equality. Both sides reduce to the same expression.
-/
theorem bruhat : Bruhat := by
  intro K _ σ hσ _ n c hc a ha
  have hr : ∀ U : Submodule K (Fin n → K), Module.finrank K U ≤ n := fun U =>
    (Submodule.finrank_le U).trans (by simp)
  refine ⟨fun U b hb => repMat_unitary σ hσ b (a U) hb (ha U).1, ?_⟩
  intro g hg hgu
  obtain ⟨A, B, C, D, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq g
  have hiso := isotropic_of_unitary σ hgu
  set U := Submodule.span K (Set.range C) with hU
  obtain ⟨T, L, hT, -, hLT⟩ := GlobalTheory.T.same_span_transfer_matrices C (c U) (hc U).1 (hc U).2
  obtain ⟨b, hb, hcond⟩ := GlobalTheory.T.hermitian_block_solution_exists σ hσ (hr U) (c U) (a U) C D T L (ha U) hT hLT hiso
  have hS := (siegel_rep_iff σ hσ b (a U) hb (ha U).1 A B C D).2 hcond
  refine ⟨⟨U, b, hb⟩, hS, ?_⟩
  rintro ⟨U', b', hb'⟩ hq
  have hrep' := repMat_unitary σ hσ b' (a U') hb' (ha U').1
  obtain ⟨p', hp', hC', hD'⟩ := factor_of_siegel hg hrep'.1 hq rfl (repMat_eq σ b' (a U'))
  have hUU : U' = U := by
    rw [← (hc U').2, ← GlobalTheory.T.span_range_complement_transform (hr U') (c U') (a U') p' (ha U') hp', ← hC']
  subst hUU
  have hrep := repMat_unitary σ hσ b (a U) hb (ha U).1
  obtain ⟨p, hp, hC, hD⟩ := factor_of_siegel hg hrep.1 hS rfl (repMat_eq σ b (a U))
  have hbb := herm_unique σ (hr U) (a U) (ha U).1 b' b p' p hp' (hC'.symm.trans hC) (hD'.symm.trans hD)
  subst hbb
  rfl

end GlobalTheory.CompanionTheory.BruhatCell
